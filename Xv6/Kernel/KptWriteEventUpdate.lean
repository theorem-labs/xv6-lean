import Xv6.Kernel.KptWriteEventSlots
import Xv6.Kernel.KptSharedProofs
import MachCSL.Logic.TsoPinnedWriteWPProofs

namespace Xv6.Kernel.KptWriteEvent
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) (ownership : KptOwnership.Spec capacity)

instance clients_persistent era N root tree : Persistent (clients capacity era N root tree) := by
  unfold clients
  infer_instance

include ownership

/-- Open and restore the same shared invariant in one mask-preserving
update. The payer is the actual complete heap/TSO of the supplied state. -/
theorem update era (g : State) cpu (N : Namespace) (E : CoPset) root tree vpn p2 p1 p0
    (mask : (↑N : CoPset) ⊆ E) (mapped : PtTree.Maps tree vpn p2 p1 p0)
    (req : MemoryWriteWP.WriteRequest 8) (new : BitVec 64)
    (location : req.pa = PtTree.addr0 p1 vpn)
    (canonical : PteCanonical.canon new = PteCanonical.canon p0) :
    iprop(⊢ clients capacity era N root tree -∗
      MemoryWriteWP.writeBundle capacity.machine.era era g -∗
      Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes g
      ={E}=∗
        MemoryWriteWP.writeBundle capacity.machine.era era (MemoryWriteWP.writeState g cpu req new) ∗
        Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes
          (MemoryWriteWP.writeState g cpu req new) ∗
        Tso.History.logElem capacity.machine.era.history era.logEntries g.log.length
          ⟨snapshot req.pa 8 new, hartAgent cpu⟩ ∗ clients capacity era N root tree) := by
  haveI := KptShared.body_timeless capacity ownership era root
  iintro #Hclients Hbundle Htso
  iunfold clients at Hclients
  icases Hclients with ⟨#Hshared,#Hgiven⟩
  iunfold KptShared.shared at Hshared
  imod inv_acc mask $$ Hshared with ⟨Hbody,Hclose⟩
  imod Hbody
  iunfold KptShared.body at Hbody
  icases Hbody with ⟨%current,%mapping,%B,Htree,#Hsnapshot,#Hbound,Hmap,%spec⟩
  ihave %same := KptGhost.agree capacity.ghost era.kernelPageTable tree current $$ [Hgiven Hsnapshot]
  · iframe Hgiven Hsnapshot
  obtain ⟨physical,currentMaps,currentCanonical⟩ := PtTree.maps_across tree current vpn p2 p1 p0 same mapped
  obtain ⟨a,d,newEq⟩ := PteCanonical.canon_inv physical new (canonical.trans currentCanonical.symm)
  subst new
  have leaf : PtTree.Leaf physical := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,leaf,_,_⟩ := currentMaps
    exact leaf
  ihave ⟨Hslot2,Hslot1,Hslot0,Hrestore⟩ := ownership.path_update era (.kernel B) (.own 1)
    current vpn p2 p1 physical currentMaps $$ Htree
  iunfold KptOwnership.slotOwn at Hslot0
  iunfold KptOwnership.kernelSlot at Hslot0
  icases Hslot0 with ⟨Haligned,Hslot⟩
  isimp only [← location] at Hslot
  ihave ⟨%floors,Hpin,Hanchors⟩ := SupervisorPteAD.slot_open capacity.machine era req.pa physical B
    (PteCanonical.slotSet physical) $$ Hslot
  imod TsoPinnedWriteWP.bundle_store capacity.machine era g cpu req physical
    (PteCanonical.setAD physical a d) floors (PteCanonical.slotSet physical)
    (fun j hj => PteCanonical.slot_mem_variant physical a d j leaf hj)
    $$ Hbundle Htso Hpin with ⟨Hbundle,Htso,Hreceipt,Hpin⟩
  ihave Hslot := SupervisorPteAD.slot_close capacity.machine era req.pa (PteCanonical.setAD physical a d)
    (g.log.length+1) B floors (PteCanonical.slotSet physical) $$ [Hpin Hanchors]
  · iframe Hpin Hanchors
  ihave Hslot := slot_family capacity era req.pa (.own 1) B physical a d leaf $$ Hslot
  isimp only [location] at Hslot
  ihave Htree := Hrestore $$ %(PteCanonical.setAD physical a d) Hslot2 Hslot1 [Haligned Hslot]
  · iunfold KptOwnership.slotOwn
    iunfold KptOwnership.kernelSlot
    dsimp only
    iframe Haligned Hslot
  have canonicalTree := PtTree.canon_set_leaf current vpn p2 p1 physical a d currentMaps
  ihave #HnewSnapshot := KptGhost.canonical capacity.ghost era.kernelPageTable current
    (PtTree.setLeaf current vpn (PteCanonical.setAD physical a d)) canonicalTree.symm $$ Hsnapshot
  imod Hclose $$ [Htree Hmap] with _
  · iintro !>
    iunfold KptShared.body
    iexists (PtTree.setLeaf current vpn (PteCanonical.setAD physical a d)), mapping, B
    iframe Htree Hmap HnewSnapshot Hbound
    ipureintro
    exact KptShared.set_leaf_spec root mapping current spec vpn p2 p1 physical currentMaps a d
  imodintro
  iframe Hbundle Htso Hreceipt
  iunfold clients
  iunfold KptShared.shared
  iframe Hshared Hgiven

end Xv6.Kernel.KptWriteEvent
