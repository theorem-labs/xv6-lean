import Xv6.Kernel.MycpuOffSpec
import Xv6.Kernel.HartTpPure

namespace Xv6.Kernel.MycpuOff
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

def gprFootprint : RegisterFootprint.Footprint :=
  HartTp.physicalKeys.map (fun r => (r, .own 1))

def framedRegisters : List Register :=
  [.x3, .x5, .x6, .x7, .x11, .x12, .x13, .x14, .x16, .x17, .x28, .x29, .x30, .x31]

def framedFootprint : RegisterFootprint.Footprint :=
  framedRegisters.map (fun r => (r, .own 1))

theorem footprint_counts shares :
    (controlFootprint shares).length = 21 ∧ gprFootprint.length = 31 ∧
    (MycpuCycleBody.footprint (cycleShares shares)).length = 28 ∧
    (MycpuBare.frameFootprint (fun _ => .own 1)).length = 11 ∧
    framedFootprint.length = 14 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem footprint_unique shares : RegisterFootprint.Unique
    (controlFootprint shares ++ [(Register.mstatus, DFrac.own 1)] ++ gprFootprint) := by
  have keys : (controlFootprint shares ++ [(Register.mstatus, DFrac.own 1)] ++ gprFootprint).map Prod.fst =
    (controlFootprint ⟨.discard, .discard, ⟨.discard, .discard, .discard, .discard⟩,
      .discard, .discard, .discard, .discard, .discard, .discard⟩ ++
      [(Register.mstatus, DFrac.own 1)] ++ gprFootprint).map Prod.fst := by rfl
  unfold RegisterFootprint.Unique
  rw [keys]
  decide

theorem bit_ne_one_eq_zero (bit : BitVec 1) (notOne : (bit == 1#1) = false) : bit = 0#1 := by
  have all : ∀ value : BitVec 1, (value == 1#1) = false → value = 0#1 := by decide
  exact all bit notOne

theorem entry_config control cpu values (config : EntryConfig control)
    (facts : SupervisorBits.MsFacts (control .mstatus))
    (off : (_get_Mstatus_SIE (control .mstatus) == 1#1) = false) :
    MycpuBare.EntryConfig (entry control cpu values) := by
  refine ⟨⟨config.privilege, config.active, config.landing, config.misa,
    config.environment, off, bit_ne_one_eq_zero _ facts.1, ?_, facts.2.1,
    config.delegated, config.bare, ?_, config.htif, config.pma⟩, config.pc⟩
  · exact of_decide_eq_true facts.2.2.1
  · exact ⟨config.tor.tor, config.tor.positive, config.tor.execute, config.tor.write, config.tor.read, config.tor.covers⟩

theorem entry_tp control cpu values : (entry control cpu values) .x4 = HartTp.hartWord cpu := rfl

theorem returned_result control cpu values after
    (result : MycpuBare.HartResult (entry control cpu values) after cpu) :
    Result control cpu values after := by
  refine ⟨result, ?_, rfl, ?_, ?_⟩
  · intro index member
    simp only [savedIndices, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  · exact result.value
  · exact result.cpuAddress

theorem control_list shares : controlFootprint shares =
  [(.PC, .own 1), (.misa, shares.misa), (.cur_privilege, shares.privilege), (.satp, shares.satp), (.pma_regions, shares.physical.pma), (.pmpcfg_n, shares.physical.cfg), (.pmpaddr_n, shares.physical.addr), (.htif_tohost_base, shares.physical.htif), (.mie, shares.enable), (.mideleg, shares.delegation), (.menvcfg, shares.environment), (.elp, shares.landing), (.nextPC, .own 1), (.minstret, .own 1), (.minstret_increment, .own 1), (.mcountinhibit, .discard), (.minstretcfg, .discard), (.mcycle, .own 1), (.mtime, .own 1), (.mip, .own 1), (.hart_state, shares.hart)] := rfl

theorem cycle_list shares : MycpuCycleBody.footprint (cycleShares shares) =
  [(.PC, .own 1), (.misa, shares.misa), (.mstatus, .own 1), (.cur_privilege, shares.privilege), (.satp, shares.satp), (.pma_regions, shares.physical.pma), (.pmpcfg_n, shares.physical.cfg), (.pmpaddr_n, shares.physical.addr), (.htif_tohost_base, shares.physical.htif), (.mie, shares.enable), (.mideleg, shares.delegation), (.menvcfg, shares.environment), (.elp, shares.landing), (.nextPC, .own 1), (.x1, .own 1), (.x2, .own 1), (.x8, .own 1), (.x15, .own 1), (.x10, .own 1), (.x4, .own 1), (.minstret, .own 1), (.minstret_increment, .own 1), (.mcountinhibit, .discard), (.minstretcfg, .discard), (.mcycle, .own 1), (.mtime, .own 1), (.mip, .own 1), (.hart_state, shares.hart)] := rfl

theorem gpr_list : gprFootprint =
  [(.x1, .own 1), (.x2, .own 1), (.x3, .own 1), (.x4, .own 1), (.x5, .own 1), (.x6, .own 1), (.x7, .own 1), (.x8, .own 1), (.x9, .own 1), (.x10, .own 1), (.x11, .own 1), (.x12, .own 1), (.x13, .own 1), (.x14, .own 1), (.x15, .own 1), (.x16, .own 1), (.x17, .own 1), (.x18, .own 1), (.x19, .own 1), (.x20, .own 1), (.x21, .own 1), (.x22, .own 1), (.x23, .own 1), (.x24, .own 1), (.x25, .own 1), (.x26, .own 1), (.x27, .own 1), (.x28, .own 1), (.x29, .own 1), (.x30, .own 1), (.x31, .own 1)] := rfl

/-- Equality is required only on the function's owned keys. Unlisted GPRs
remain in the explicit physical remainder. -/
theorem returned_agrees control cpu values after
    (result : MycpuBare.HartResult (entry control cpu values) after cpu)
    (r : Register) (owned : r ∉ framedRegisters) :
    entry after cpu (returnedMap values after) r = after r := by
  have saved2 := result.saved .x2 (by decide)
  have saved8 := result.saved .x8 (by decide)
  have saved9 := result.saved .x9 (by decide)
  have saved18 := result.saved .x18 (by decide)
  have saved19 := result.saved .x19 (by decide)
  have saved20 := result.saved .x20 (by decide)
  have saved21 := result.saved .x21 (by decide)
  have saved22 := result.saved .x22 (by decide)
  have saved23 := result.saved .x23 (by decide)
  have saved24 := result.saved .x24 (by decide)
  have saved25 := result.saved .x25 (by decide)
  have saved26 := result.saved .x26 (by decide)
  have saved27 := result.saved .x27 (by decide)
  have saved1 := result.ra
  have tp := result.stable .x4 (by decide)
  cases r <;> first
    | rfl
    | exact False.elim (owned (by decide))
    | exact tp.symm
    | exact saved1.symm
    | exact saved2.symm
    | exact saved8.symm
    | exact saved9.symm
    | exact saved18.symm
    | exact saved19.symm
    | exact saved20.symm
    | exact saved21.symm
    | exact saved22.symm
    | exact saved23.symm
    | exact saved24.symm
    | exact saved25.symm
    | exact saved26.symm
    | exact saved27.symm

theorem framed_entry control cpu values after (r : Register) (framed : r ∈ framedRegisters) :
    entry after cpu (returnedMap values after) r = entry control cpu values r := by
  simp only [framedRegisters, List.mem_cons, List.not_mem_nil, or_false] at framed
  rcases framed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem cycle_owned shares r (member : r ∈ (MycpuCycleBody.footprint (cycleShares shares)).map Prod.fst) :
    r ∉ framedRegisters := by
  rw [cycle_list] at member
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem saved_owned r (member : r ∈ MycpuBare.remainingSaved) : r ∉ framedRegisters := by
  simp only [MycpuBare.remainingSaved, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

end Xv6.Kernel.MycpuOff
