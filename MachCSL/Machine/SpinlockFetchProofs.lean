import MachCSL.Machine.SpinlockFetchDefs

namespace MachCSL.Machine.SpinlockFetch
open MachCSL.Logic.EventWP LeanPaperStock.Functions JalLoopPlan
variable (index : Fin 17)
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The read predicate is justified by the actual initial image bytes. Later
instruction rules must preserve or reacquire the corresponding RAM resources. -/
theorem codeRead_image (n : Nat) (req : Logic.MemoryReadWP.ReadRequest n)
    (word : BitVec (8 * n)) (read : CodeRead index n req word) :
    Memory.readBytes (loadedRam SpinlockImage.image) req.pa n = some word := by
  obtain ⟨rfl, address, value⟩ := read
  rw [address, value]
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using SpinlockImage.instruction_bytes index

private def accessSnapshot : JalLoop.Snapshot
  | .pma_regions => some pmaBoot
  | .mstatus => some 0xA00000000#64
  | .cur_privilege => some .Machine
  | .misa => some 0x800000000014112d#64
  | .htif_tohost_base => some none
  | .PC => some (SpinlockImage.instructionAddress index)
  | _ => none

private theorem accessSnapshot_covers (rs : RegisterFile) (static : Static index rs) :
    JalLoop.Covers (accessSnapshot index) rs := by
  intro r value found
  cases r <;> simp only [accessSnapshot, Option.some.injEq] at found
  all_goals first | contradiction | subst value
  · exact static.pma
  · exact static.htif
  · exact static.pc
  · exact static.mstatus
  · exact static.misa
  · exact static.privilege

private def codeAccessInfo : Phys_Mem_Access_Info := ⟨.CannotSplit, 0⟩

private theorem pma_checked :
    snapshotPlanRun (fun _ _ => none) (accessSnapshot index) 100
      (pmaCheck (.Physaddr (SpinlockImage.instructionAddress index)) 4 (.InstructionFetch ()) .PBMT_PMA false) =
      some (.Ok codeAccessInfo) := by
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨ index = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem translate_checked :
    snapshotPlanRun (fun _ _ => none) (accessSnapshot index) 100
      (translateAddr (.Virtaddr (SpinlockImage.instructionAddress index)) (.InstructionFetch ())) =
      some (.Ok (.Physaddr (SpinlockImage.instructionAddress index), .PBMT_PMA, ())) := by
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨ index = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem mmio_checked :
    snapshotPlanRun (fun _ _ => none) (accessSnapshot index) 100
      (within_mmio_readable (.Physaddr (SpinlockImage.instructionAddress index)) 4) = some false := by
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨ index = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem pma_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static index rs) :
    Returns reads rs (pmaCheck (.Physaddr (SpinlockImage.instructionAddress index)) 4 (.InstructionFetch ()) .PBMT_PMA false)
      (.Ok codeAccessInfo) rs :=
  snapshotPlanRun_plan reads (fun _ _ => none) (fun _ _ _ h => by cases h)
    (accessSnapshot index) rs (accessSnapshot_covers index rs static) _ _ _ (pma_checked index)

theorem translate_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static index rs) :
    Returns reads rs (translateAddr (.Virtaddr (SpinlockImage.instructionAddress index)) (.InstructionFetch ()))
      (.Ok (.Physaddr (SpinlockImage.instructionAddress index), .PBMT_PMA, ())) rs :=
  snapshotPlanRun_plan reads (fun _ _ => none) (fun _ _ _ h => by cases h)
    (accessSnapshot index) rs (accessSnapshot_covers index rs static) _ _ _ (translate_checked index)

private theorem mmio_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static index rs) :
    Returns reads rs (within_mmio_readable (.Physaddr (SpinlockImage.instructionAddress index)) 4) false rs :=
  snapshotPlanRun_plan reads (fun _ _ => none) (fun _ _ _ h => by cases h)
    (accessSnapshot index) rs (accessSnapshot_covers index rs static) _ _ _ (mmio_checked index)

private theorem pma_priority_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static index rs) :
    Returns reads rs (check_pma_with_pmp_priority (.InstructionFetch ()) .PBMT_PMA .Machine
      (.Physaddr (SpinlockImage.instructionAddress index)) 4 false) (.Ok codeAccessInfo) rs := by
  unfold check_pma_with_pmp_priority
  refine (pma_plan index reads rs static).bind ?_
  exact pure_plan reads rs _

theorem read_ram_plan (rs : RegisterFile) :
    Returns (CodeRead index) rs (read_ram .Read_plain (.Physaddr (SpinlockImage.instructionAddress index)) 4 false) ((SpinlockImage.word index), ()) rs := by
  obtain ⟨position, bound⟩ := index
  let index : Fin 17 := ⟨position, bound⟩
  have cases : position = 0 ∨ position = 1 ∨ position = 2 ∨ position = 3 ∨ position = 4 ∨ position = 5 ∨ position = 6 ∨ position = 7 ∨ position = 8 ∨ position = 9 ∨ position = 10 ∨ position = 11 ∨ position = 12 ∨ position = 13 ∨ position = 14 ∨ position = 15 ∨ position = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    with_unfolding_all
      apply ExecPlan.readMem (word := (SpinlockImage.word index)) (by rfl) (by rfl) ⟨rfl, rfl, rfl⟩
      exact pure_plan (CodeRead index) rs _

theorem checked_mem_read_plan (rs : RegisterFile) (static : Static index rs)
    (pmp : Returns (CodeRead index) rs
      (pmpCheck (.Physaddr (SpinlockImage.instructionAddress index)) 4 (.InstructionFetch ()) .Machine) none rs) :
    Returns (CodeRead index) rs
      (checked_mem_read (.InstructionFetch ()) .PBMT_PMA .Machine
        (.Physaddr (SpinlockImage.instructionAddress index)) 4 false false false false) (.Ok ((SpinlockImage.word index), ())) rs := by
  obtain ⟨position, bound⟩ := index
  let index : Fin 17 := ⟨position, bound⟩
  have cases : position = 0 ∨ position = 1 ∨ position = 2 ∨ position = 3 ∨ position = 4 ∨ position = 5 ∨ position = 6 ∨ position = 7 ∨ position = 8 ∨ position = 9 ∨ position = 10 ∨ position = 11 ∨ position = 12 ∨ position = 13 ∨ position = 14 ∨ position = 15 ∨ position = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    with_unfolding_all
      unfold checked_mem_read _root_.Sail.SailME.run PreSail.PreSailME.run
      refine Returns.bind (value := Except.ok (.Ok ((SpinlockImage.word index), ()))) ?_
        (pure_plan (CodeRead index) rs _)
      apply Returns.exceptBind (middle := rs) (a := codeAccessInfo)
      · refine ((pma_priority_plan index (CodeRead index) rs static).liftExcept
          (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))).bind ?_
        exact pure_plan (CodeRead index) rs _
      refine Returns.exceptBind (middle := rs) (a := ((1, 4) : Int × Int))
        (pure_plan (CodeRead index) rs _) ?_
      refine Returns.exceptBind (middle := rs) (a := read_kind.Read_plain)
        (pure_plan (CodeRead index) rs _) ?_
      refine Returns.exceptBind (middle := rs) (a := ((SpinlockImage.word index), true, (0 : Nat))) ?_
        (pure_plan (CodeRead index) rs _)
      refine Returns.exceptBind (middle := rs) (a := ((SpinlockImage.word index), true, (0 : Nat))) ?_
        (pure_plan (CodeRead index) rs _)
      simp only [untilFuelM]
      refine Returns.exceptBind (middle := rs) (a := ((SpinlockImage.word index), true, (0 : Nat))) ?_
        (pure_plan (CodeRead index) rs _)
      refine (pmp.liftExcept
        (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))).bind ?_
      refine ((mmio_plan index (CodeRead index) rs static).liftExcept
        (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))).bind ?_
      simp only [ExceptT.bindCont]
      refine Returns.exceptBind (middle := rs) (a := (SpinlockImage.word index)) ?_
        (pure_plan (CodeRead index) rs _)
      refine ((read_ram_plan index rs).liftExcept
        (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))).bind ?_
      exact pure_plan (CodeRead index) rs _

theorem mem_read_plan (rs : RegisterFile) (static : Static index rs) (off : BootPmp.Off rs) :
    Returns (CodeRead index) rs
      (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr (SpinlockImage.instructionAddress index)) 4 false false false)
      (.Ok (SpinlockImage.word index)) rs := by
  unfold mem_read
  refine (read_plan (CodeRead index) rs .mstatus (by decide)).bind ?_
  refine (read_plan (CodeRead index) rs .cur_privilege (by decide)).bind ?_
  rw [static.mstatus, static.privilege]
  unfold effectivePrivilege
  change Returns (CodeRead index) rs
    (mem_read_priv (.InstructionFetch ()) .PBMT_PMA .Machine
      (.Physaddr (SpinlockImage.instructionAddress index)) 4 false false false) (.Ok (SpinlockImage.word index)) rs
  unfold mem_read_priv mem_read_priv_meta
  refine Returns.bind (middle := rs) (value := _root_.Sail.Result.Ok ((SpinlockImage.word index), ())) ?_
    (pure_plan (CodeRead index) rs _)
  refine (checked_mem_read_plan index rs static
    (BootPmp.check_off_plan (CodeRead index) rs off _ _ _)).bind ?_
  exact pure_plan (CodeRead index) rs _

theorem fetch_bytes_plan (rs : RegisterFile) (static : Static index rs) (off : BootPmp.Off rs) :
    Returns (CodeRead index) rs (fetch_bytes (SpinlockImage.instructionAddress index) (SpinlockImage.instructionAddress index) 4)
      (.FetchBytes_Success (SpinlockImage.word index)) rs := by
  unfold fetch_bytes _root_.Sail.SailME.run PreSail.PreSailME.run
  refine Returns.bind (value := Except.ok (.FetchBytes_Success (SpinlockImage.word index))) ?_
    (pure_plan (CodeRead index) rs _)
  refine Returns.exceptBind (middle := rs) (a := (.Physaddr (SpinlockImage.instructionAddress index), page_based_mem_type.PBMT_PMA)) ?_ ?_
  · refine ((translate_plan index (CodeRead index) rs static).liftExcept (FetchBytes_Result 4)).bind ?_
    exact pure_plan (CodeRead index) rs _
  · refine ((mem_read_plan index rs static off).liftExcept (FetchBytes_Result 4)).bind ?_
    exact pure_plan (CodeRead index) rs _

private theorem zca_checked :
    snapshotPlanRun (fun _ _ => none) (accessSnapshot index) 100 (currentlyEnabled .Ext_Zca) = some true := by
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨ index = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem ziccif_checked :
    snapshotPlanRun (fun _ _ => none) (accessSnapshot index) 100 (currentlyEnabled .Ext_Ziccif) = some true := by
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨ index = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem zca_plan (rs : RegisterFile) (static : Static index rs) :
    Returns (CodeRead index) rs (currentlyEnabled .Ext_Zca) true rs :=
  snapshotPlanRun_plan (CodeRead index) (fun _ _ => none) (fun _ _ _ h => by cases h)
    (accessSnapshot index) rs (accessSnapshot_covers index rs static) _ _ _ (zca_checked index)

private theorem ziccif_plan (rs : RegisterFile) (static : Static index rs) :
    Returns (CodeRead index) rs (currentlyEnabled .Ext_Ziccif) true rs :=
  snapshotPlanRun_plan (CodeRead index) (fun _ _ => none) (fun _ _ _ h => by cases h)
    (accessSnapshot index) rs (accessSnapshot_covers index rs static) _ _ _ (ziccif_checked index)

private theorem address_bit0 : Sail.BitVec.access (SpinlockImage.instructionAddress index) 0 = 0#1 := by
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨ index = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem address_bit1 : Sail.BitVec.access (SpinlockImage.instructionAddress index) 1 = 0#1 := by
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨ index = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem address_aligned : is_aligned_vaddr (.Virtaddr (SpinlockImage.instructionAddress index)) 4 = true := by
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨ index = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem word_not_rvc : isRVC (Sail.BitVec.extractLsb (SpinlockImage.word index) 15 0) = false := by
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨ index = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

/-- Actual fetch under every postboot static/OFF family. No PMP address value
or unrelated config bit is fixed, and the four-byte resource contract is exact. -/
theorem universal_fetch_plan [Platform] (rs : RegisterFile) (static : Static index rs)
    (off : BootPmp.Off rs) : Returns (CodeRead index) rs (fetch ()) (.F_Base (SpinlockImage.word index)) rs := by
  unfold fetch _root_.Sail.SailME.run PreSail.PreSailME.run
  refine Returns.bind (value := Except.ok (.F_Base (SpinlockImage.word index))) ?_ (pure_plan (CodeRead index) rs _)
  refine (read_plan (CodeRead index) rs .PC (by decide)).bind ?_
  refine (read_plan (CodeRead index) rs .PC (by decide)).bind ?_
  rw [static.pc]
  refine (read_plan (CodeRead index) rs .PC (by decide)).bind ?_
  refine (read_plan (CodeRead index) rs .PC (by decide)).bind ?_
  refine ((zca_plan index rs static).liftExcept FetchResult).bind ?_
  rw [static.pc]
  simp only [address_bit0, address_bit1, bne_self_eq_false, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine (read_plan (CodeRead index) rs .PC (by decide)).bind ?_
  refine ((ziccif_plan index rs static).liftExcept FetchResult).bind ?_
  rw [static.pc]
  simp only [address_aligned, Bool.true_and]
  refine (read_plan (CodeRead index) rs .PC (by decide)).bind ?_
  refine (read_plan (CodeRead index) rs .PC (by decide)).bind ?_
  rw [static.pc]
  refine ((fetch_bytes_plan index rs static off).liftExcept FetchResult).bind ?_
  simp only [ExceptT.bindCont]
  simp only [word_not_rvc, Bool.false_eq_true, ↓reduceIte]
  exact pure_plan (CodeRead index) rs _

end MachCSL.Machine.SpinlockFetch
