import Xv6.Kernel.PushOffScalarDefs
import MachCSL.Logic.RegisterPlanSpec

namespace Xv6.Kernel.PushOffScalar
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

structure PureSpec [Platform] : Prop where
  inventory : ([Instruction.subSP,.framePointer,.saveStatus,.branchZero,.increment,
    .restoreSP,.returns,.shift,.mask,.jumpBack].map (fun i => (index i).val)) =
      [0,4,6,9,12,17,18,20,21,23]
  entry : ∀ i control cpu values,
    PushOffScalar.entry (afterControl i control cpu values) cpu (afterValues i cpu values) =
      after i (PushOffScalar.entry control cpu values)
  other : ∀ i cpu values key, destination i ≠ some key → afterValues i cpu values key = values key
  zero : ∀ i cpu values, afterValues i cpu values 0#5 = values 0#5
  pinnedTP : ∀ i cpu values, HartTp.rget cpu (afterValues i cpu values) HartTp.tp = HartTp.hartWord cpu
  controlOther : ∀ i control cpu values r, r ≠ .nextPC →
    afterControl i control cpu values r = control r
  sourceConfig : ∀ i control,
    control .misa = 0x800000000014112d#64 → control .cur_privilege = .Supervisor →
    control .menvcfg = 0xa000000000000000#64 → control .PC = PushOffCode.pc (index i) → Config i control
  branchTaken : ∀ control cpu values, PushOffScalar.branchTaken cpu values = true →
    afterControl .branchZero control cpu values .nextPC = control .PC + 22#64
  branchNotTaken : ∀ control cpu values, PushOffScalar.branchTaken cpu values = false →
    afterControl .branchZero control cpu values = control
  jumpTarget : ∀ control cpu values,
    afterControl .jumpBack control cpu values .nextPC = control .PC - 32#64
  returnTarget : ∀ control cpu values,
    afterControl .returns control cpu values .nextPC = MycpuReturn.retPC (HartTp.rget cpu values 1#5)
  plan : ∀ i shares control cpu values, Config i control →
    RegisterPlan.Returns (MycpuRegimeShell.footprint shares) (PushOffScalar.entry control cpu values)
      (PushOffScalar.body i) (.Retire_Success ())
      (PushOffScalar.entry (afterControl i control cpu values) cpu (afterValues i cpu values))

/-- Actual normalized execution on the common packet. No fetch, decoder,
body-success, memory callback or whole-cycle WP is supplied by a caller. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  body : ∀ i shares control values, Config i control →
    ∀ image fixed whole gen era cpu regime (frame : IProp GF)
      (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu regime control values shares -∗ frame -∗
      (resources capacity era cpu regime i control values shares frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (PushOffScalar.body i >>= continuation)) post)

end Xv6.Kernel.PushOffScalar
