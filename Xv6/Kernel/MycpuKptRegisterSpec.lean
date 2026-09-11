import Xv6.Kernel.MycpuKptRegisterDefs
import MachCSL.Logic.RegisterPlanSpec

namespace Xv6.Kernel.MycpuKptRegister
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

structure PureSpec [Platform] : Prop where
  scalarBody : ∀ i, body (.scalar i) = MycpuScalar.body i
  returnBody : body .returns = MycpuReturn.body
  scalarPhysical : ∀ i, HartTp.physical (scalarIndex i) = some (scalarRegister i)
  scalarNonzero : ∀ i, scalarIndex i ≠ 0#5 ∧ scalarIndex i ≠ HartTp.tp
  scalarEntry : ∀ i control cpu values,
    entry (afterControl (.scalar i) control cpu values) cpu (afterValues (.scalar i) control cpu values) =
      MycpuScalar.after i (entry control cpu values)
  returnEntry : ∀ control cpu values,
    entry (afterControl .returns control cpu values) cpu (afterValues .returns control cpu values) =
      MycpuReturn.after (entry control cpu values)
  scalarOther : ∀ i control cpu values key, key ≠ scalarIndex i →
    afterValues (.scalar i) control cpu values key = values key
  zero : ∀ instruction control cpu values,
    afterValues instruction control cpu values 0#5 = values 0#5
  pinnedTP : ∀ instruction control cpu values,
    HartTp.rget cpu (afterValues instruction control cpu values) HartTp.tp = HartTp.hartWord cpu
  status : ∀ instruction control cpu values,
    afterControl instruction control cpu values .mstatus = control .mstatus
  physicalPC : ∀ instruction control cpu values,
    afterControl instruction control cpu values .PC = control .PC
  returnTarget : ∀ control cpu values,
    afterControl .returns control cpu values .nextPC = MycpuReturn.retPC (HartTp.rget cpu values 1#5)
  plan : ∀ instruction shares control cpu values, Config instruction control →
    RegisterPlan.Returns (MycpuRegimeShell.footprint shares) (entry control cpu values)
      (body instruction) (.Retire_Success ())
      (entry (afterControl instruction control cpu values) cpu (afterValues instruction control cpu values))

/-- All actual register subevents are discharged by native RegisterPlan.
The literal frame can retain anchored virtual words, running context and the
actual reservation without adding a memory or body WP premise. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  body : ∀ instruction shares control values, Config instruction control →
    ∀ image fixed whole gen era cpu (N : Namespace) root (frame : IProp GF)
      (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗ frame -∗
      (resources capacity era cpu N root instruction control values shares frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (MycpuKptRegister.body instruction >>= continuation)) post)

end Xv6.Kernel.MycpuKptRegister
