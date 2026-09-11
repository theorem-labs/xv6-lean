import Xv6.Kernel.KptJalDefs

namespace Xv6.Kernel.KptJal
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

structure PureSpec [Platform] : Prop where
  encoder : ∀ imm, Encodable imm → encdec_forwards (instruction imm) = pure (encoding imm)
  base : ∀ imm, isRVC (KernelTextDatum.lowHalf (encoding imm)) = false
  immediateEven : ∀ pc imm, is_aligned_vaddr (.Virtaddr pc) 2 = true → TargetEven pc imm → Encodable imm
  decoder : ∀ shares control imm, Config control → Encodable imm →
    RegisterPlan.Returns (footprint shares) control (ext_decode (encoding imm)) (instruction imm) control
  executeFactor : ∀ imm, execute (instruction imm) =
    (get_next_pc () >>= fun returnAddress => PreSail.readReg .PC >>= fun pc =>
      jump_to (target pc imm) >>= fun execution => match execution with
      | .Retire_Success () => wX_bits (.Regidx 1#5) returnAddress >>= fun _ => pure (.Retire_Success ())
      | failure => pure failure)
  preparePlan : ∀ shares control cpu values pc imm, Config control → control .PC = pc → Encodable imm →
    MycpuActive.Prefix (footprint shares) (entry control cpu values)
      (MycpuActive.afterFetch 0 (result imm)) (executeTail imm) (entry (prepared pc control) cpu values)
  bodyPlan : ∀ shares control cpu values pc imm, Config control → control .PC = pc →
    control .nextPC = link pc → TargetEven pc imm →
    RegisterPlan.Returns (footprint shares) (entry control cpu values) (body imm) (.Retire_Success ())
      (entry (afterControl pc imm control) cpu (afterValues pc values))
  preparedEntry : ∀ pc control cpu values, prepared pc (entry control cpu values) = entry (prepared pc control) cpu values
  afterPrepared : ∀ pc imm control, afterControl pc imm (prepared pc control) = afterControl pc imm control
  ra : ∀ pc cpu values, HartTp.rget cpu (afterValues pc values) 1#5 = link pc
  other : ∀ pc cpu values index, index ≠ 1#5 →
    HartTp.rget cpu (afterValues pc values) index = HartTp.rget cpu values index
  zero : ∀ pc values, afterValues pc values 0#5 = values 0#5
  startedConfig : ∀ control, Config control → Config (started control)
  preparedConfig : ∀ pc control, Config control → Config (prepared pc control)
  afterConfig : ∀ pc imm control, Config control → Config (afterControl pc imm control)
  completedConfig : ∀ pc imm control after, Config control →
    MycpuRegimeShell.Completed (afterControl pc imm control) after → Config after
  completedPC : ∀ pc imm control after, MycpuRegimeShell.Completed (afterControl pc imm control) after →
    after .PC = target pc imm ∧ after .nextPC = target pc imm

structure ResourceSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  persistent : ∀ era tier pc imm, Persistent (code capacity era tier pc imm)
  alignment : ∀ era tier pc imm, iprop(code capacity era tier pc imm ⊢ ⌜is_aligned_vaddr (.Virtaddr pc) 2 = true⌝)
  window : ∀ era tier pc imm, is_aligned_vaddr (.Virtaddr pc) 2 = true →
    iprop(KernelTextDatum.window capacity.translation era tier pc 4 .discard (encoding imm) ⊢ code capacity era tier pc imm)

/-- Supplied code is native RX/pristine ownership. These rules internally
execute their programs; only their genuine returned continuation is a WP input. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  fetch : ∀ shares control values, Config control → ∀ pc imm, control .PC = pc →
    ∀ tier ξ rr image fixed whole gen era cpu (N : Namespace) root (frame : IProp GF)
      (continuation : FetchResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗ code capacity era tier pc imm -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      fetchFinish capacity image fixed whole gen era cpu shares control values N root tier ξ pc imm rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (fetch () >>= continuation)) post)
  body : ∀ shares control values, Config control → ∀ pc imm, control .PC = pc →
    control .nextPC = link pc → TargetEven pc imm →
    ∀ ξ image fixed whole gen era cpu (N : Namespace) root (frame : IProp GF)
      (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗ frame -∗
      (bodyResources capacity era cpu shares control values N root ξ pc imm frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (KptJal.body imm >>= continuation)) post)
  active : ∀ shares control values, Config control → ∀ pc imm, control .PC = pc → TargetEven pc imm →
    ∀ tier ξ rr image fixed whole gen era cpu (N : Namespace) root (frame : IProp GF)
      (continuation : Step → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗ code capacity era tier pc imm -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      activeFinish capacity image fixed whole gen era cpu shares control values N root tier ξ pc imm rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (run_hart_active 0 >>= continuation)) post)
  cycle : ∀ shares control values, Config control → ∀ pc imm, control .PC = pc → TargetEven pc imm →
    ∀ tier ξ rr tick image fixed whole gen era cpu (N : Namespace) root (frame : IProp GF) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗ code capacity era tier pc imm -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      cycleFinish capacity image fixed whole gen era cpu shares control values N root tier ξ pc imm frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (MachCSL.Machine.cycle tick)) post)

end Xv6.Kernel.KptJal
