import Xv6.Kernel.BareJalDefs

namespace Xv6.Kernel.BareJal
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure ResourceSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  partition : ∀ era cpu control values,
    iprop(packet capacity era cpu control values ⊣⊢ ∃ satp pmp,
      ⌜_get_Satp64_Mode (Mk_Satp64 satp) = 0#4⌝ ∗ ⌜SupervisorPmp.TorRam pmp⌝ ∗
      BareJalFetch.cells capacity.translation era cpu (entry (patch control satp pmp) cpu values) fetchShares ∗
      fetchFrame capacity era cpu (patch control satp pmp) values)

/-- Actual generated component WPs. The final Link supplies the shared
finite decoder/body plans and the Bare physical fetch internally. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  fetch : ∀ control values, Config control → ∀ pc imm, control .PC = pc →
    ∀ ξ rr image fixed whole gen era cpu frame continuation post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu control values -∗ code capacity era pc imm -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      fetchFinish capacity image fixed whole gen era cpu ξ control values pc imm rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (fetch () >>= continuation)) post)
  body : ∀ control values, Config control → ∀ pc imm, control .PC = pc →
    control .nextPC = KptJal.link pc → TargetEven pc imm →
    ∀ ξ image fixed whole gen era cpu frame continuation post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu control values -∗ TsoContextReadWP.running capacity.machine era cpu ξ -∗ frame -∗
      (bodyResources capacity era cpu ξ control values pc imm frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (body imm >>= continuation)) post)
  active : ∀ control values, Config control → ∀ pc imm, control .PC = pc → TargetEven pc imm →
    ∀ ξ rr image fixed whole gen era cpu frame continuation post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu control values -∗ code capacity era pc imm -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      activeFinish capacity image fixed whole gen era cpu ξ control values pc imm rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (run_hart_active 0 >>= continuation)) post)
  cycle : ∀ control values, Config control → ∀ pc imm, control .PC = pc → TargetEven pc imm →
    ∀ ξ rr tick image fixed whole gen era cpu frame post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu control values -∗ code capacity era pc imm -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      cycleFinish capacity image fixed whole gen era cpu ξ control values pc imm frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post)

end Xv6.Kernel.BareJal
