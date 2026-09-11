import Xv6.Kernel.MycpuActivePlan
import MachCSL.Logic.RegisterPlanProofs

namespace Xv6.Kernel.MycpuActive
open Iris Iris.BI MachCSL.Memory MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

/-- Widen a proved register plan to a shared footprint without duplicating cells. -/
theorem plan_weaken {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

theorem Prefix.weaken {small large : RegisterFootprint.Footprint} {rs after : RegisterFile}
    {program body : SailM α} (cut : Prefix small rs program body after)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : Prefix large rs program body after := by
  induction cut with
  | done => exact .done
  | «prefix» first _ ih => exact .prefix (plan_weaken first members) ih

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint, MycpuFetch.footprint, SupervisorBareFetch.footprint,
    SupervisorBare.footprint, SupervisorFetchRead.footprint]

theorem footprint_length (shares : Shares) : (footprint shares).length = 14 := rfl

theorem prepared_nextPC (i : Fin 14) (rs : RegisterFile) :
    prepared i rs .nextPC = Sail.BitVec.addInt (rs .PC) (MycpuDecode.width i) := by
  simp [prepared, MachCSL.Sail.Registers.write]

theorem prepared_other (i : Fin 14) (rs : RegisterFile) (r : Register) (other : r ≠ .nextPC) :
    prepared i rs r = rs r := by
  exact MachCSL.Sail.Registers.write_other rs .nextPC r _ (Ne.symm other)

theorem prepared_pc (i : Fin 14) (rs : RegisterFile) : prepared i rs .PC = rs .PC :=
  prepared_other i rs .PC (by decide)

/-- The actual compressed decoder result redirects exactly once to its base AST. -/
theorem compressed_tail [Platform] (i : Fin 14) (rvc : MycpuDecode.compressed i = true) :
    executeTail i = (execute (MycpuDecode.normalized i) >>= fun result =>
      pure (.Step_Execute (result, instbits i))) := by
  unfold executeTail
  rw [MycpuDecode.compressed_expansion i rvc]
  rfl

/-- No non-ExecuteAs assumption is inserted for the base instruction. -/
theorem base_tail [Platform] (i : Fin 14) (base : MycpuDecode.compressed i = false) :
    executeTail i = (do
      let first ← execute (MycpuDecode.normalized i)
      let final ← match first with
        | .ExecuteAs other => execute other
        | other => pure other
      pure (.Step_Execute (final, instbits i))) := by
  unfold executeTail
  rw [MycpuDecode.base_normalized i base]
  congr 1

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- Ordinary native bind rule to the actual residual body. This does not claim
that the body is safe; its WP remains the explicit continuation obligation. -/
theorem Prefix.fold {A : Type} (fp : RegisterFootprint.Footprint) (unique : RegisterFootprint.Unique fp)
    (rs after : RegisterFile) (program body : SailM A) (cut : Prefix fp rs program body after)
    image fixed whole gen era cpu (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu) after fp -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (body >>= continuation)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction cut with
  | done =>
    iintro #Hcert Hregs Hfinish
    iapply Hfinish $$ Hregs
  | @«prefix» B A rs middle after segment value next body first rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hfinish
    iapply RegisterPlan.fold capacity fp unique image fixed whole gen era cpu rs segment
      (fun result after => result = value ∧ after = middle)
      (fun value => next value >>= continuation) post first $$ Hcert Hregs
    iintro %result %actual %same Hregs
    rcases same with ⟨rfl, rfl⟩
    iapply ih $$ Hcert Hregs Hfinish

end Xv6.Kernel.MycpuActive
