import MachCSL.Machine.SupervisorPmpProofs

namespace MachCSL.Machine.SupervisorPmp
open MachCSL.Logic.EventWP LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

private theorem lift_except {reads : ReadAllowed} {program : SailM α}
    {rs : RegisterFile} {value : α} (plan : Returns reads rs program value rs) (ε : Type) :
    Returns reads rs (monadLift program : SailME ε α).run (.ok value) rs := by
  change Returns reads rs (program >>= fun a => pure (Except.ok a)) (.ok value) rs
  exact plan.bind (pure_plan reads rs _)

/-- Grain zero preserves the raw address, for every configuration bit pattern. -/
theorem read_address_plan (reads : ReadAllowed) (rs : RegisterFile) (n : Nat) :
    Returns reads rs (pmpReadAddrReg n) (rs .pmpaddr_n)[n]! rs := by
  unfold pmpReadAddrReg
  refine (read_plan reads rs .pmpcfg_n (by decide)).bind ?_
  refine (read_plan reads rs .pmpaddr_n (by decide)).bind ?_
  dsimp only
  split <;> exact pure_plan reads rs _

theorem match_tor_plan (reads : ReadAllowed) (rs : RegisterFile)
    (address width : BitVec 64) (cfg : BitVec 8) (upper : BitVec 64)
    (tor : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A cfg) = .TOR)
    (positive : 0 < upper.toNat)
    (range : pmpRangeMatch 0 (upper.toNat * 4) address.toNat width.toNat = .PMP_Match) :
    Returns reads rs (pmpMatchAddr (.Physaddr address) width cfg upper 0#64) .PMP_Match rs := by
  unfold pmpMatchAddr
  rw [tor, (unsigned_positive upper).mpr positive]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have geometry : pmpRangeMatch
      (( _root_.Sail.BitVec.toNatInt (0#64)) * 4).toNat
      ((_root_.Sail.BitVec.toNatInt upper) * 4).toNat
      (_root_.Sail.BitVec.toNatInt address).toNat
      (_root_.Sail.BitVec.toNatInt width).toNat = .PMP_Match := by
    simpa [_root_.Sail.BitVec.toNatInt, Int.toNat_mul] using range
  change Returns reads rs
    (pure (pmpRangeMatch
      ((_root_.Sail.BitVec.toNatInt (0#64)) * 4).toNat
      ((_root_.Sail.BitVec.toNatInt upper) * 4).toNat
      (_root_.Sail.BitVec.toNatInt address).toNat
      (_root_.Sail.BitVec.toNatInt width).toNat)) .PMP_Match rs
  rw [geometry]
  exact pure_plan reads rs _

theorem permissions_plan (reads : ReadAllowed) (rs : RegisterFile) (config : TorRam rs)
    (access : MemoryAccessType mem_payload) (supported : Supported access) :
    Returns reads rs (pmpCheckRWX (entry0 rs) access) true rs := by
  cases supported <;> unfold pmpCheckRWX
  · rw [config.execute]; exact pure_plan reads rs _
  · rw [config.read]; exact pure_plan reads rs _
  · rw [config.read]; exact pure_plan reads rs _
  · rw [config.write]; exact pure_plan reads rs _

private theorem except_bind {reads : ReadAllowed} {program : SailME ε α}
    {next : α → SailME ε β} {rs : RegisterFile} {a : α} {b : Except ε β}
    (first : Returns reads rs program.run (.ok a) rs)
    (second : Returns reads rs (next a).run b rs) :
    Returns reads rs (program >>= next).run b rs := first.bind second

private theorem except_error {reads : ReadAllowed} {program : SailME ε α}
    {next : α → SailME ε β} {rs : RegisterFile} {error : ε}
    (first : Returns reads rs program.run (.error error) rs) :
    Returns reads rs (program >>= next).run (.error error) rs :=
  first.bind (pure_plan reads rs _)

private def checkRange : IntRange := ⟨0, 15, 1, by decide⟩

private theorem first_exit (reads : ReadAllowed) (rs : RegisterFile) (ε : Type)
    (body : (i : Int) → i ∈ checkRange → Unit → SailME ε (ForInStep Unit))
    (error : ε)
    (law : Returns reads rs (body 0 (by decide) ()).run (.error error) rs) :
    Returns reads rs
      (IntRange.forIn'.loop checkRange body () 0 (by simp [checkRange])).run
      (.error error) rs := by
  rw [IntRange.forIn'.loop.eq_1, dif_pos (show (0 : Int) ∈ checkRange by decide)]
  exact except_error law

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem check_ram_plan (reads : ReadAllowed) (rs : RegisterFile) (config : TorRam rs)
    (address : BitVec 64) (width : Nat) (positive : 0 < width)
    (_low : ramLow ≤ address.toNat) (fits : address.toNat + width ≤ ramHigh)
    (access : MemoryAccessType mem_payload) (supported : Supported access) :
    Returns reads rs (pmpCheck (.Physaddr address) width access .Supervisor) none rs := by
  unfold pmpCheck _root_.Sail.SailME.run PreSail.PreSailME.run
  simp only [show (sys_pmp_count == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine Returns.bind (value := Except.error none) ?_ (pure_plan reads rs _)
  apply except_error
  apply first_exit reads rs (Option ExceptionType) _ none
  dsimp only
  refine except_bind (pure_plan reads rs _) ?_
  refine except_bind (lift_except (read_plan reads rs .pmpcfg_n (by decide)) _) ?_
  refine except_bind (a := (rs .pmpcfg_n)[(0 : Int)]!) (pure_plan reads rs _) ?_
  refine except_bind (lift_except (read_address_plan reads rs 0) _) ?_
  have cfg : (rs .pmpcfg_n)[(0 : Int)]! = entry0 rs := by
    exact BootPmp.get_int _ 0 (by decide)
  have addr : (rs .pmpaddr_n)[(0 : Nat)]! = upper0 rs := by
    exact _root_.getElem!_pos _ _ (by decide)
  rw [cfg, addr]
  refine except_bind (lift_except (match_tor_plan reads rs address _ _ _ config.tor
    config.positive (ram_range rs config address width positive fits)) _) ?_
  refine except_bind (lift_except (permissions_plan reads rs config access supported) _) ?_
  exact pure_plan reads rs _

/-- The source hardware/supervisor wrapper; neither extra field inserts a read. -/
theorem source_check_ram_plan (reads : ReadAllowed) (rs : RegisterFile)
    (config : SourceConfig rs) (address : BitVec 64) (width : Nat)
    (positive : 0 < width) (low : ramLow ≤ address.toNat)
    (fits : address.toNat + width ≤ ramHigh)
    (access : MemoryAccessType mem_payload) (supported : Supported access) :
    Returns reads rs (pmpCheck (.Physaddr address) width access .Supervisor) none rs :=
  check_ram_plan reads rs config.toTorRam address width positive low fits access supported

/-- Source fetch grant, preserving arbitrary later entries and unrelated registers. -/
theorem fetch_plan (reads : ReadAllowed) (rs : RegisterFile) (config : TorRam rs)
    (address : BitVec 64) (width : Nat) (positive : 0 < width)
    (low : ramLow ≤ address.toNat) (fits : address.toNat + width ≤ ramHigh) :
    Returns reads rs
      (pmpCheck (.Physaddr address) width (.InstructionFetch ()) .Supervisor) none rs :=
  check_ram_plan reads rs config address width positive low fits _ .fetch

/-- Source page-table load grant; actual PTE memory/translation events are separate. -/
theorem pte_load_plan (reads : ReadAllowed) (rs : RegisterFile) (config : TorRam rs)
    (address : BitVec 64) (width : Nat) (positive : 0 < width)
    (low : ramLow ≤ address.toNat) (fits : address.toNat + width ≤ ramHigh) :
    Returns reads rs
      (pmpCheck (.Physaddr address) width (.Load .PageTableEntry) .Supervisor) none rs :=
  check_ram_plan reads rs config address width positive low fits _ .pte

end MachCSL.Machine.SupervisorPmp
