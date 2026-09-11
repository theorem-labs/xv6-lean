import Xv6.Kernel.KptTreeWalkPteProofs
import Xv6.Kernel.Sv39TreeWalkFactor

namespace Xv6.Kernel.KptTreeWalk
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

private theorem fold_empty {A : Type} (rs : RegisterFile) (program : SailM A) (value : A)
    (plan : RegisterPlan.Returns [] rs program value rs)
    image fixed whole gen era cpu (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation value)) post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  iintro #Hcert Hfinish
  iapply RegisterPlan.fold (hlc := hlc) capacity.machine [] (by simp [RegisterFootprint.Unique])
    image fixed whole gen era cpu rs program (fun v after => v = value ∧ after = rs)
    continuation post plan $$ Hcert []
  · iunfold RegisterFootprint.cells; itrivial
  iintro %v %after %same _
  rcases same with ⟨rfl,rfl⟩
  iexact Hfinish

/-- One actual upper node with the complete raw pointer, including G/RSW.
The location equalities select the corresponding level of the same Maps path. -/
theorem wp_pointer shares rs tree vpn p2 p1 p0 (mapped : PtTree.Maps tree vpn p2 p1 p0)
    (level : Fin 3) (positive : 0 < level.val) base raw
    (location : PtTree.slotAddress base (PtTree.index level.val vpn) = KptReadEvent.address tree vpn p2 p1 level)
    (reference : KptReadEvent.reference p2 p1 p0 level = raw)
    (valid : PtTree.Valid raw) (pointer : PtTree.Pointer raw)
    region (config : SupervisorPteRead.Config rs (KptReadEvent.address tree vpn p2 p1 level) region)
    access mxr doSum global image fixed whole gen era cpu (N : Namespace) root bound rr
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (pt_walk 39 vpn access .Supervisor mxr doSum (PtTree.nextBase raw)
            (level.val - 1) (global || PtTree.globalBit raw) () >>= continuation)) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (pt_walk 39 vpn access .Supervisor mxr doSum base level.val global () >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  rw [Sv39Walk.node_eq vpn access mxr doSum base level global, BootPmp.sail_bind_assoc,
    Sv39TreeWalk.address_same, location]
  iintro #Hcert Hregs Hclients Hresv Hfinish
  iapply wp_pte capacity shares rs tree vpn p2 p1 p0 level mapped region config
    image fixed whole gen era cpu N root bound rr
    (fun response => Sv39Walk.afterRead vpn access mxr doSum
      (.Physaddr (KptReadEvent.address tree vpn p2 p1 level)) level.val global response >>= continuation) post
    $$ Hcert Hregs Hclients Hresv
  iintro !> %view %word %relation Hregs Hclients Hresv Hreceipt
  rw [reference] at relation
  have same : word = raw := relation.2 pointer
  subst word
  simp only [Sv39Walk.afterRead, BootPmp.sail_bind_assoc]
  have validation := PtTree.nativePointerSpec.validation_plan raw valid pointer rs
  unfold PtTree.validation at validation
  iapply fold_empty capacity rs _ false validation image fixed whole gen era cpu
    (fun invalid => Sv39Walk.afterInvalid vpn access mxr doSum raw
      (.Physaddr (KptReadEvent.address tree vpn p2 p1 level)) level.val global invalid >>= continuation) post $$ Hcert
  rw [Sv39TreeWalk.pointer_next vpn access mxr doSum raw pointer _ level.val positive global]
  iapply Hfinish $$ %view Hregs Hclients Hresv Hreceipt

/-- The final actual ordinary read determines the leaf A/D bits, followed
by both real validity checks and all leaf extension/permission branches. -/
theorem wp_leaf shares rs tree vpn p2 p1 ppn permission referenceA referenceD
    (mapped : PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD))
    region (config : SupervisorPteRead.Config rs (PtTree.addr0 p1 vpn) region)
    access (supported : KptLeaf.Supported access) (allowed : KptLeaf.Allows permission access)
    mxr doSum global image fixed whole gen era cpu (N : Namespace) root bound rr
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ (∀ a d view, cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok (Sv39Walk.output (Sv39TreeWalk.geometry tree p2 p1 ppn)
            vpn permission global a d, ())))) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (pt_walk 39 vpn access .Supervisor mxr doSum (PtTree.nextBase p1) 0 global () >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  rw [Sv39Walk.node_eq vpn access mxr doSum (PtTree.nextBase p1) ⟨0, Nat.zero_lt_succ 2⟩ global,
    BootPmp.sail_bind_assoc, Sv39TreeWalk.address_same]
  iintro #Hcert Hregs Hclients Hresv Hfinish
  ieval (
    change _ ⊢ MemoryReadWP.threadWP capacity.machine image fixed whole
      (.hart gen cpu (read_pte (.Physaddr (KptReadEvent.address tree vpn p2 p1 ⟨0, Nat.zero_lt_succ 2⟩)) 8 >>= fun response =>
        Sv39Walk.afterRead vpn access mxr doSum (.Physaddr (PtTree.addr0 p1 vpn)) 0 global response >>= continuation)) post)
  iapply wp_pte capacity shares rs tree vpn p2 p1 _ ⟨0, Nat.zero_lt_succ 2⟩ mapped region config
    image fixed whole gen era cpu N root bound rr
    (fun response => Sv39Walk.afterRead vpn access mxr doSum (.Physaddr (PtTree.addr0 p1 vpn)) 0 global response >>= continuation) post
    $$ Hcert Hregs Hclients Hresv
  iintro !> %view %word %relation Hregs Hclients Hresv Hreceipt
  have canonical : PteCanonical.canon word = PteCanonical.canon (KptLeaf.word ppn permission false false) := by
    simpa only [KptReadEvent.reference, KptLeaf.word_canonical] using relation.1
  obtain ⟨a,d,rfl⟩ := Sv39Walk.leaf_variant ppn permission word canonical
  have plan := Sv39Walk.leaf_plan rs (Sv39TreeWalk.geometry tree p2 p1 ppn) vpn permission a d
    access supported allowed mxr doSum global
  rw [show Sv39Walk.address (Sv39TreeWalk.geometry tree p2 p1 ppn) vpn 0 = PtTree.addr0 p1 vpn from rfl,
    show (Sv39TreeWalk.geometry tree p2 p1 ppn).leaf = ppn from rfl] at plan
  iapply fold_empty capacity rs _ (.Ok (Sv39Walk.output (Sv39TreeWalk.geometry tree p2 p1 ppn)
    vpn permission global a d, ())) plan
    image fixed whole gen era cpu continuation post $$ Hcert
  iapply Hfinish $$ %a %d %view Hregs Hclients Hresv Hreceipt

end Xv6.Kernel.KptTreeWalk
