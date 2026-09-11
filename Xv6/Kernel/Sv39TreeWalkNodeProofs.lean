import Xv6.Kernel.Sv39TreeWalkFactor
import MachCSL.Logic.SupervisorPteReadLink

namespace Xv6.Kernel.Sv39TreeWalk
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- Fold actual register reads without supplying any register ownership when
all their possible responses have already been covered by the plan. -/
private theorem fold_empty {A : Type} (rs : RegisterFile) (program : SailM A) (value : A)
    (plan : RegisterPlan.Returns [] rs program value rs)
    image fixed whole gen era cpu (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation value)) post -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  iintro #Hcert Hfinish
  iapply RegisterPlan.fold (hlc := hlc) capacity [] (by simp [RegisterFootprint.Unique])
    image fixed whole gen era cpu rs program (fun v after => v = value ∧ after = rs)
    continuation post plan $$ Hcert []
  · iunfold RegisterFootprint.cells; itrivial
  iintro %v %after %same _
  rcases same with ⟨rfl, rfl⟩
  iexact Hfinish

/-- Arbitrary valid raw pointer, preserving G/RSW and all actual validation
reads. The full nonleaf pin family determines the read word exactly. -/
theorem wp_pointer (shares : Shares) (rs : RegisterFile) (ppn : BitVec 44) (raw : PtTree.Word)
    (valid : PtTree.Valid raw) (pointer : PtTree.Pointer raw)
    (vpn : BitVec 27) (level : Fin 3) (positive : 0 < level.val)
    (region : PMA_Region)
    (config : SupervisorPteRead.Config rs (PtTree.slotAddress ppn (PtTree.index level.val vpn)) region)
    (access : MemoryAccessType mem_payload) (mxr doSum global : Bool)
    image fixed whole gen era cpu bound dq values rr (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoPinnedReadWP.credential capacity era cpu bound -∗
      TsoPinnedReadWP.slot capacity era (PtTree.slotAddress ppn (PtTree.index level.val vpn)) 8 dq values bound
        (PteCanonical.slotSet raw) -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoPinnedReadWP.credential capacity era cpu bound -∗
        TsoPinnedReadWP.slot capacity era (PtTree.slotAddress ppn (PtTree.index level.val vpn)) 8 dq values bound
          (PteCanonical.slotSet raw) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (pt_walk 39 vpn access .Supervisor mxr doSum (PtTree.nextBase raw) (level.val - 1) (global || PtTree.globalBit raw) () >>= continuation)) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (pt_walk 39 vpn access .Supervisor mxr doSum ppn level.val global () >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  rw [Sv39Walk.node_eq vpn access mxr doSum ppn level global, BootPmp.sail_bind_assoc, address_same]
  iintro #Hcert Hregs Hcred Hslot Hresv Hfinish
  iapply SupervisorPteRead.wp_plain capacity shares rs _ region config
    image fixed whole gen era cpu dq values bound raw rr
    (fun response => Sv39Walk.afterRead vpn access mxr doSum
      (.Physaddr (PtTree.slotAddress ppn (PtTree.index level.val vpn))) level.val global response >>= continuation) post
    $$ Hcert Hregs Hcred Hslot Hresv
  iintro !> %view %word %canon %exactWord Hregs Hcred Hslot Hresv Hview
  have same : word = raw := exactWord pointer
  subst word
  simp only [Sv39Walk.afterRead, BootPmp.sail_bind_assoc]
  have validate := PtTree.nativePointerSpec.validation_plan raw valid pointer rs
  unfold PtTree.validation at validate
  iapply fold_empty capacity rs _ false validate
    image fixed whole gen era cpu
    (fun invalid => Sv39Walk.afterInvalid vpn access mxr doSum raw
      (.Physaddr (PtTree.slotAddress ppn (PtTree.index level.val vpn))) level.val global invalid >>= continuation) post $$ Hcert
  rw [pointer_next vpn access mxr doSum raw pointer _ level.val positive global]
  iapply Hfinish $$ %view Hregs Hcred Hslot Hresv Hview


end Xv6.Kernel.Sv39TreeWalk
