import Xv6.Kernel.KptReadEventAccess
import MachCSL.Logic.TsoPinnedReadWPProofs

namespace Xv6.Kernel.KptReadEvent
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) (ownership : KptOwnership.Spec capacity)
include ownership

omit [Platform] in
/-- At one actual pre-read state, open the invariant, prove the all-view
relation, restore the complete tree and power interpretation, and close.
The selected read word remains existential inside each chosen view. -/
theorem power_reads fixed (g : State) gen era cpu (live : ThreadLive g gen)
    (N : Namespace) root tree vpn p2 p1 p0 level
    (mapped : PtTree.Maps tree vpn p2 p1 p0) B :
    iprop(⊢ MachineInterp.powerInterp capacity.machine fixed g -∗
      MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      KptShared.shared capacity era N root -∗ KptShared.snapshot capacity era tree -∗
      KptShared.bound capacity era B -∗ TsoPinnedReadWP.credential capacity.machine era cpu B
      ={⊤}=∗ MachineInterp.powerInterp capacity.machine fixed g ∗
      ⌜∀ view, g.views cpu ≤ view → ∃ word,
        ReadsBytes g.image g.log (hartAgent cpu) view (address tree vpn p2 p1 level) 8 word ∧
        ReadFact (reference p2 p1 p0 level) word⌝) := by
  haveI := KptShared.body_timeless capacity ownership era root
  iintro Hp #Hcert #Hshared #Hsnapshot #Hbound #Hcredential
  iunfold KptShared.shared at Hshared
  have mask : (↑N : CoPset) ⊆ ⊤ := by intro x _; exact CoPset.mem_full
  imod inv_acc mask $$ Hshared with ⟨Hbody,Hclose⟩
  imod Hbody
  iunfold KptShared.body at Hbody
  icases Hbody with ⟨%current,%mapping,%currentB,Htree,#HcurrentSnapshot,#HcurrentBound,Hmap,%spec⟩
  ihave %same := KptGhost.agree capacity.ghost era.kernelPageTable tree current $$ [Hsnapshot HcurrentSnapshot]
  · iframe Hsnapshot HcurrentSnapshot
  ihave %sameBound := KptGhost.bound_agree capacity.ghost era.kernelPageTableBound
    era.logLength era.logLength currentB B $$ [HcurrentBound Hbound]
  · iframe HcurrentBound Hbound
  subst currentB
  ihave ⟨%currentWord,%relation,Hslot,Hrestore⟩ := path_access capacity ownership era (.kernel B) (.own 1)
    tree current vpn p2 p1 p0 level mapped same $$ Htree
  iunfold KptOwnership.slotOwn at Hslot
  iunfold KptOwnership.kernelSlot at Hslot
  icases Hslot with ⟨Haligned,Hpin⟩
  ihave ⟨Hp,_,Hpin,%reads⟩ := TsoPinnedReadWP.power_slot_read capacity.machine fixed g gen era cpu live
    (address tree vpn p2 p1 level) 8 (.own 1) (nthByte currentWord) B (PteCanonical.slotSet currentWord)
    $$ Hp Hcert Hcredential Hpin
  ihave Htree := Hrestore $$ [Haligned Hpin]
  · iunfold KptOwnership.slotOwn
    iunfold KptOwnership.kernelSlot
    dsimp only
    iframe Haligned Hpin
  imod Hclose $$ [Htree Hmap] with _
  · iintro !>
    iunfold KptShared.body
    iexists current, mapping, B
    iframe Htree Hmap HcurrentSnapshot HcurrentBound
    ipureintro
    exact spec
  imodintro
  iframe Hp
  ipureintro
  intro view lower
  obtain ⟨word,wordRead,allowed⟩ := TsoPinnedReadWP.slot_reads_words g cpu
    (address tree vpn p2 p1 level) 8 (PteCanonical.slotSet currentWord) reads view lower
  exact ⟨word,wordRead,readFact_allowed _ currentWord word relation allowed⟩

end Xv6.Kernel.KptReadEvent
