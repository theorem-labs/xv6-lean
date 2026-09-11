import Xv6.Kernel.KptExclusiveEventSpec
import Xv6.Kernel.KptReadEventAccess
import MachCSL.Logic.MemoryExclusiveWPProofs

namespace Xv6.Kernel.KptExclusiveEvent
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF) (ownership : KptOwnership.Spec capacity)
include ownership

/-- Authority-backed current-memory read. Forgetting a slot is used only to
prove a pure fact; the invariant accessor retains the original resource. -/
theorem heap_slot_read era (g : State) tier a dq word :
    iprop(⊢ Era.heapInterpAt capacity.machine.era era g -∗
      KptOwnership.slotOwn capacity era tier a dq word -∗
      ⌜readBytes g.memory a 8 = some word⌝) := by
  iintro Hheap Hslot
  ihave Hraw := ownership.slot_forget era tier a dq word $$ Hslot
  iunfold KptOwnership.rawWord at Hraw
  icases Hraw with ⟨_,Hbytes⟩
  have reads := MemoryExclusiveWP.heap_window_read capacity.machine era g a 8 dq word
  unfold TsoRead.byteWindow at reads
  iapply reads $$ Hheap Hbytes

variable {hlc : HasLC} [InvGS_gen hlc GF]

omit ownership in
instance clients_persistent era N root tree : Persistent (clients capacity era N root tree) := by
  unfold clients
  infer_instance

/-- Reopen at the actual state after the native view advance, derive the
current leaf from the full heap, and close with precisely the same tree. -/
theorem current era (g : State) cpu (N : Namespace) (E : CoPset) root tree vpn p2 p1 p0
    (mask : (↑N : CoPset) ⊆ E) (mapped : PtTree.Maps tree vpn p2 p1 p0) :
    iprop(⊢ clients capacity era N root tree -∗
      MemoryExclusiveWP.readBundle capacity.machine.era era g -∗
      Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes
        (TsoRead.advanceView g cpu g.log.length) -∗
      Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) g.log.length
      ={E}=∗ ∃ word,
        ⌜readBytes g.memory (PtTree.addr0 p1 vpn) 8 = some word ∧ ReadFact p0 word⌝ ∗
        MemoryExclusiveWP.readBundle capacity.machine.era era g ∗
        Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes
          (TsoRead.advanceView g cpu g.log.length) ∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) g.log.length ∗
        clients capacity era N root tree) := by
  haveI := KptShared.body_timeless capacity ownership era root
  iintro #Hclients Hbundle Htso #Hreceipt
  iunfold clients at Hclients
  icases Hclients with ⟨#Hshared,#Hsnapshot⟩
  iunfold KptShared.shared at Hshared
  imod inv_acc mask $$ Hshared with ⟨Hbody,Hclose⟩
  imod Hbody
  iunfold KptShared.body at Hbody
  icases Hbody with ⟨%currentTree,%mapping,%B,Htree,#HcurrentSnapshot,#Hbound,Hmap,%spec⟩
  ihave %same := KptGhost.agree capacity.ghost era.kernelPageTable tree currentTree
    $$ [Hsnapshot HcurrentSnapshot]
  · iframe Hsnapshot HcurrentSnapshot
  ihave ⟨%word,%relation,Hslot,Hrestore⟩ := KptReadEvent.path_access capacity ownership era
    (.kernel B) (.own 1) tree currentTree vpn p2 p1 p0 ⟨0, by decide⟩ mapped same $$ Htree
  isimp only [KptReadEvent.address, KptReadEvent.reference] at Hslot Hrestore
  iunfold MemoryExclusiveWP.readBundle at Hbundle
  icases Hbundle with ⟨Hregs,Hheap,Hdevices⟩
  ihave %reads := heap_slot_read capacity ownership era g (.kernel B) (PtTree.addr0 p1 vpn)
    (.own 1) word $$ Hheap Hslot
  ihave Htree := Hrestore $$ Hslot
  imod Hclose $$ [Htree Hmap] with _
  · iintro !>
    iunfold KptShared.body
    iexists currentTree, mapping, B
    iframe Htree Hmap HcurrentSnapshot Hbound
    ipureintro
    exact spec
  imodintro
  iexists word
  isplit
  · ipureintro
    exact ⟨reads, relation.1⟩
  · iunfold MemoryExclusiveWP.readBundle
    iunfold clients
    iunfold KptShared.shared
    iframe Hregs Hheap Hdevices Htso Hreceipt Hshared Hsnapshot

variable [Platform]

/-- The native exclusive rule retains overlap retries and old-generation
steps. Only its successful arm consumes this fully discharged read premise. -/
theorem wp_read image fixed whole gen era cpu (N : Namespace) root tree vpn p2 p1 p0
    (mapped : PtTree.Maps tree vpn p2 p1 p0) (req : MemoryExclusiveWP.ReadRequest 8)
    (location : req.pa = PtTree.addr0 p1 vpn)
    (ram : deviceAddress req.pa = false) (exclusive : accessExclusive req.access_kind = true)
    rr (continuation : MemoryExclusiveWP.ReadResult 8 → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      clients capacity era N root tree -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜ReadFact p0 word⌝ -∗
        clients capacity era N root tree -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
          (some (snapshot req.pa 8 word)) -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryExclusiveWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok (word, none)))) post) -∗
      MemoryExclusiveWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (.impure (.readMem 8 req) continuation)) post) := by
  iintro #Hcert #Hclients Hresv Hcontinue
  iapply MemoryExclusiveWP.wp_exclusive capacity.machine image fixed whole gen era cpu 8 req continuation
    rr post ram exclusive $$ Hcert Hresv
  iunfold MemoryExclusiveWP.exclusivePremise
  iintro %g Hbundle Htso Hreceipt
  have mask : (↑N : CoPset) ⊆ ⊤ := by intro x _; exact CoPset.mem_full
  imod current capacity ownership era g cpu N ⊤ root tree vpn p2 p1 p0 mask mapped
    $$ Hclients Hbundle Htso Hreceipt with ⟨%word,%facts,Hbundle,Htso,Hreceipt,_⟩
  iapply fupd_mask_intro (E2 := ∅) (by intro x _; exact CoPset.mem_full)
  iintro Hback
  iexists word
  isplit
  · ipureintro
    simpa only [location] using facts.1
  · iintro !>
    imod Hback
    imodintro
    iframe Hbundle Htso
    iintro Hresv
    iapply Hcontinue $$ %g.log.length %word %facts.2 Hclients Hresv Hreceipt

theorem actual : Spec capacity := ⟨current capacity ownership, wp_read capacity ownership⟩

end Xv6.Kernel.KptExclusiveEvent
