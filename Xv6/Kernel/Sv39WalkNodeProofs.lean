import Xv6.Kernel.Sv39WalkFactor
import MachCSL.Logic.SupervisorPteReadLink

namespace Xv6.Kernel.Sv39Walk
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

/-- An interior node consumes one actual ordinary memory event and returns the
same full slot assertion, credential, reservation and register cells. -/
theorem wp_pointer (shares : Shares) (rs : RegisterFile) (ppn next : BitVec 44)
    (vpn : BitVec 27) (level : Fin 3) (positive : 0 < level.val)
    (region : PMA_Region)
    (config : SupervisorPteRead.Config rs (addressAt ppn (index vpn level.val)) region)
    (access : MemoryAccessType mem_payload) (mxr doSum global : Bool)
    image fixed whole gen era cpu bound dq values rr (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoPinnedReadWP.credential capacity era cpu bound -∗
      TsoPinnedReadWP.slot capacity era (addressAt ppn (index vpn level.val)) 8 dq values bound
        (PteCanonical.slotSet (pointer next)) -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoPinnedReadWP.credential capacity era cpu bound -∗
        TsoPinnedReadWP.slot capacity era (addressAt ppn (index vpn level.val)) 8 dq values bound
          (PteCanonical.slotSet (pointer next)) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (pt_walk 39 vpn access .Supervisor mxr doSum next (level.val - 1) global () >>= continuation)) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (pt_walk 39 vpn access .Supervisor mxr doSum ppn level.val global () >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  rw [node_eq vpn access mxr doSum ppn level global, BootPmp.sail_bind_assoc]
  iintro #Hcert Hregs Hcred Hslot Hresv Hfinish
  iapply SupervisorPteRead.wp_plain capacity shares rs _ region config
    image fixed whole gen era cpu dq values bound (pointer next) rr
    (fun response => afterRead vpn access mxr doSum
      (.Physaddr (addressAt ppn (index vpn level.val))) level.val global response >>= continuation) post
    $$ Hcert Hregs Hcred Hslot Hresv
  iintro !> %view %word %canon %exactWord Hregs Hcred Hslot Hresv Hview
  have same : word = pointer next := exactWord (pointer_nonleaf next)
  subst word
  simp only [afterRead, BootPmp.sail_bind_assoc]
  iapply fold_empty capacity rs _ false (pointer_valid rs next)
    image fixed whole gen era cpu
    (fun invalid => afterInvalid vpn access mxr doSum (pointer next)
      (.Physaddr (addressAt ppn (index vpn level.val))) level.val global invalid >>= continuation) post $$ Hcert
  rw [pointer_next vpn access mxr doSum next _ level.val positive global]
  iapply Hfinish $$ %view Hregs Hcred Hslot Hresv Hview

/-- The final ordinary read derives its A/D variant from canonical slot
membership before folding all twelve actual validity/extension reads. -/
theorem wp_leaf (shares : Shares) (rs : RegisterFile) (path : Path) (vpn : BitVec 27)
    (region : PMA_Region) (config : SupervisorPteRead.Config rs (address path vpn 0) region)
    (permission : KptLeaf.Permission) (access : MemoryAccessType mem_payload)
    (supported : KptLeaf.Supported access) (allowed : KptLeaf.Allows permission access)
    (mxr doSum global : Bool) image fixed whole gen era cpu bound dq values rr
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoPinnedReadWP.credential capacity era cpu bound -∗
      TsoPinnedReadWP.slot capacity era (address path vpn 0) 8 dq values bound
        (PteCanonical.slotSet (KptLeaf.word path.leaf permission false false)) -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ a d view, cells capacity era cpu rs shares -∗
        TsoPinnedReadWP.credential capacity era cpu bound -∗
        TsoPinnedReadWP.slot capacity era (address path vpn 0) 8 dq values bound
          (PteCanonical.slotSet (KptLeaf.word path.leaf permission false false)) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok (output path vpn permission global a d, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (pt_walk 39 vpn access .Supervisor mxr doSum path.table0 0 global () >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  rw [node_eq vpn access mxr doSum path.table0 ⟨0, by decide⟩ global, BootPmp.sail_bind_assoc]
  iintro #Hcert Hregs Hcred Hslot Hresv Hfinish
  ieval (
    change _ ⊢ MemoryReadWP.threadWP capacity image fixed whole
      (.hart gen cpu (read_pte (.Physaddr (address path vpn 0)) 8 >>= fun response =>
        afterRead vpn access mxr doSum (.Physaddr (address path vpn 0)) 0 global response >>= continuation)) post)
  iapply SupervisorPteRead.wp_plain capacity shares rs _ region config
    image fixed whole gen era cpu dq values bound (KptLeaf.word path.leaf permission false false) rr
    (fun response => afterRead vpn access mxr doSum (.Physaddr (address path vpn 0)) 0 global response >>= continuation) post
    $$ Hcert Hregs Hcred Hslot Hresv
  iintro !> %view %word %canon %_exactWord Hregs Hcred Hslot Hresv Hview
  obtain ⟨a, d, rfl⟩ := leaf_variant path.leaf permission word canon
  iapply fold_empty capacity rs _ (.Ok (output path vpn permission global a d, ()))
    (leaf_plan rs path vpn permission a d access supported allowed mxr doSum global)
    image fixed whole gen era cpu continuation post $$ Hcert
  iapply Hfinish $$ %a %d %view Hregs Hcred Hslot Hresv Hview

end Xv6.Kernel.Sv39Walk
