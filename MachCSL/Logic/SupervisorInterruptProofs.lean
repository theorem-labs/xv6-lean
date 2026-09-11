import MachCSL.Logic.SupervisorInterruptSpec
import MachCSL.Logic.RegisterPlanProofs
import MachCSL.Machine.SupervisorInterruptProofs

namespace MachCSL.Logic.SupervisorInterrupt
open Iris Iris.BI MachCSL.Machine Machine.SupervisorInterrupt LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

theorem Returns.bind {shares : Shares} {rs middle after : RegisterFile}
    {program : SailM α} {next : α → SailM β} {value : α} {result : β}
    (first : Returns shares rs program value middle)
    (rest : Returns shares middle (next value) result after) :
    Returns shares rs (program >>= next) result after :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (shares : Shares) (rs : RegisterFile) (value : α) :
    Returns shares rs (.pure value) value rs := .pure ⟨rfl, rfl⟩

private theorem read_plan (shares : Shares) (rs : RegisterFile) (r : Register)
    (dq : DFrac) (member : (r, dq) ∈ footprint shares) :
    Returns shares rs (PreSail.readReg r) (rs r) rs :=
  .read member (.pure ⟨rfl, rfl⟩)

theorem currentlyEnabled_s_plan (reads : Shares) (rs : RegisterFile)
    (enabled : _get_Misa_S (rs .misa) = 1#1) :
    Returns reads rs (currentlyEnabled .Ext_S) true rs := by
  unfold currentlyEnabled
  refine (read_plan reads rs .misa reads.misa (by simp [footprint])).bind ?_
  rw [enabled, show currentlyEnabled .Ext_Zicsr = (Pure.pure true : SailM Bool) by
    unfold currentlyEnabled
    rw [show hartSupports .Ext_Zicsr = true by unfold hartSupports; rfl]]
  rw [show hartSupports .Ext_S = true by unfold hartSupports; rfl]
  exact pure_plan reads rs true

/-- Both pin results are independent universal branches of the event plan. -/
theorem external_plan (reads : Shares) (rs : RegisterFile)
    (enabled : _get_Misa_S (rs .misa) = 1#1) :
    RegisterPlan.Plan (footprint reads) rs (external_interrupts_pending ())
      (fun value after => (∃ meip seip, value = externalValue meip seip) ∧ after = rs) := by
  unfold external_interrupts_pending
  apply RegisterPlan.Plan.readAny
  intro meip
  dsimp only [_root_.Sail.ArchSem.FreeM.bind]
  refine RegisterPlan.Plan.bind (currentlyEnabled_s_plan reads rs enabled) ?_
  intro value after same
  rcases same with ⟨valueEq, afterEq⟩
  subst after
  subst value
  apply RegisterPlan.Plan.readAny
  intro seip
  exact .pure ⟨⟨meip, seip, rfl⟩, rfl⟩

/-- The current pending register is arbitrary and needs no owned cell.
All platform-pin branches also remain universal. -/
theorem read_mip_plan (reads : Shares) (rs : RegisterFile)
    (enabled : _get_Misa_S (rs .misa) = 1#1) :
    RegisterPlan.Plan (footprint reads) rs (read_mip .IncludePlatformInterrupts)
      (fun _ after => after = rs) := by
  unfold read_mip
  apply RegisterPlan.Plan.readAny
  intro pending
  dsimp only [_root_.Sail.ArchSem.FreeM.bind]
  refine RegisterPlan.Plan.bind (external_plan reads rs enabled) ?_
  intro value after same
  rcases same with ⟨_, equal⟩
  subst after
  exact .pure rfl

theorem getPendingSet_plan (reads : Shares) (rs : RegisterFile)
    (disabled : Disabled rs) :
    Returns reads rs (getPendingSet .Supervisor) none rs := by
  unfold getPendingSet
  refine (currentlyEnabled_s_plan reads rs disabled.supervisorEnabled).bind ?_
  refine (read_plan reads rs .mideleg reads.delegation (by simp [footprint])).bind ?_
  refine RegisterPlan.Plan.bind (read_mip_plan reads rs disabled.supervisorEnabled) ?_
  intro pending after same
  have afterEq := same
  subst after
  refine (read_plan reads rs .mie reads.enable (by simp [footprint])).bind ?_
  refine (read_plan reads rs .mie reads.enable (by simp [footprint])).bind ?_
  refine (read_plan reads rs .mstatus reads.status (by simp [footprint])).bind ?_
  refine (read_plan reads rs .mstatus reads.status (by simp [footprint])).bind ?_
  rw [machine_pending_zero rs disabled pending, disabled.sie]
  exact pure_plan reads rs none

theorem dispatch_plan (reads : Shares) (rs : RegisterFile)
    (disabled : Disabled rs) :
    Returns reads rs (dispatchInterrupt .Supervisor) none rs := by
  unfold dispatchInterrupt
  exact (getPendingSet_plan reads rs disabled).bind (pure_plan reads rs none)

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint]

theorem registers_intro {GF : BundledGFunctors} (capacity : Registers.Capacity GF)
    γ shares (rs : RegisterFile) (disabled : Disabled rs) :
    iprop(RegisterFootprint.cells capacity γ rs (footprint shares) ⊢
      registers capacity γ shares) := by
  iintro Hregs
  unfold registers
  iexists rs
  iframe Hregs
  ipureintro
  exact disabled

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- Native suppression uses only the four source fractional register cells.
The mip and both pin reads branch universally and require no ownership. -/
theorem wp_dispatch image fixed whole gen era cpu shares
    (continuation : Option (InterruptType × Privilege) → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      registers capacity.era.registers (era.registers cpu) shares -∗
      (registers capacity.era.registers (era.registers cpu) shares -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation none)) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (dispatchInterrupt .Supervisor >>= continuation)) post) := by
  iintro Hcert Hconfig Hfinish
  iunfold registers at Hconfig
  icases Hconfig with ⟨%rs, %disabled, Hregs⟩
  iapply RegisterPlan.fold capacity (footprint shares) (footprint_unique shares)
    image fixed whole gen era cpu rs _ (fun result after => result = none ∧ after = rs)
    continuation post (dispatch_plan shares rs disabled) $$ Hcert Hregs
  iintro %value %after %same Hregs
  rcases same with ⟨rfl, equal⟩
  subst after
  iapply Hfinish
  iapply registers_intro capacity.era.registers (era.registers cpu) shares rs disabled $$ Hregs

theorem actual : Spec capacity := ⟨wp_dispatch capacity⟩

end MachCSL.Logic.SupervisorInterrupt
