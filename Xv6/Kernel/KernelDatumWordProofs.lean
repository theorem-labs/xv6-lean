import Xv6.Kernel.KernelDatumWordPure
import Xv6.Kernel.KernelDatumLink

namespace Xv6.Kernel.KernelDatumWord
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic KernelDatum
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance claims_persistent era tier va ppn : Persistent (claims capacity era tier va ppn) := by
  unfold claims
  infer_instance

theorem head era tier va ppn :
    iprop(claims capacity era tier va ppn ⊢ claim capacity era tier va ppn) := by
  unfold claims
  have get := BigSepL.bigSepL_lookup (PROP := IProp GF)
    (Φ := fun _ j => claim capacity era tier (addressAdd va j) ppn)
    (l := List.range 8) (i := 0) (x := 0) (by rfl)
  simpa [addressAdd] using get

theorem choose era tier ξ va dq value :
    iprop(KernelDatum.word capacity era tier ξ va dq value ⊢ ∃ ppn,
      claim capacity era tier va ppn ∗ KernelDatum.word capacity era tier ξ va dq value) := by
  unfold KernelDatum.word
  iintro ⟨Halign,Hbytes⟩
  have get := (BigSepL.bigSepL_lookup_acc (PROP := IProp GF)
    (Φ := fun _ j => byte capacity era tier ξ (addressAdd va j) dq (nthByte value j))
    (l := List.range 8) (i := 0) (x := 0) (by rfl)).mp
  ihave ⟨Hzero,Hclose⟩ := get $$ Hbytes
  iunfold byte at Hzero
  icases Hzero with ⟨%ppn,#Hclaim,Hphysical⟩
  iexists ppn
  have addZero : addressAdd va 0 = va := by simp [addressAdd]
  isimp only [addZero] at Hclaim Hphysical
  iframe Hclaim Halign
  have same : (List.range 8).set 0 0 = List.range 8 := rfl
  ihave Hclose := Hclose $$ %0
  isimp only [same] at Hclose
  iapply Hclose $$ [Hphysical]
  iunfold byte
  iexists ppn
  isimp only [addZero]
  iframe Hclaim Hphysical

theorem normalize_byte era tier ξ va dq value ppn j
    (aligned : TsoContextWord.Aligned va) (bound : j < 8) :
    iprop(⊢ claim capacity era tier va ppn -∗
      byte capacity era tier ξ (addressAdd va j) dq value -∗
      claim capacity era tier (addressAdd va j) ppn ∗
      physicalByte capacity era ξ (addressAdd (physical ppn va) j) dq value) := by
  iintro Hhead Hbyte
  iunfold claim at Hhead
  icases Hhead with ⟨Hmap,_⟩
  iunfold byte at Hbyte
  icases Hbyte with ⟨%ppn',Hclaim,Hphysical⟩
  iunfold claim at Hclaim
  icases Hclaim with ⟨Hmap',%facts⟩
  have vpns := vpn_offset va j aligned bound
  isimp only [vpns] at Hmap'
  ihave %same := (KptGhost.nativeSpec capacity.ghost).mapAgree era.kernelMap (vpn va) ppn ppn' .rw .rw
    $$ [Hmap Hmap']
  · iframe Hmap Hmap'
  obtain ⟨rfl,_⟩ := same
  have pas := physical_offset va ppn j aligned bound
  isimp only [pas] at Hphysical
  iframe Hphysical
  iunfold claim
  isimp only [vpns]
  iframe Hmap'
  ipureintro
  exact facts

theorem close era tier ξ va dq value ppn (aligned : TsoContextWord.Aligned va) :
    iprop(⊢ claims capacity era tier va ppn -∗
      TsoContextReadWP.wordPointsto capacity.machine era ξ (physical ppn va) dq value -∗
      KernelDatum.word capacity era tier ξ va dq value) := by
  unfold claims TsoContextReadWP.wordPointsto TsoContextWord.pointsto KernelDatum.word
  iintro Hclaims ⟨_,Hphysical⟩
  isplit
  · ipureintro; exact aligned
  ihave Hpairs := BigSepL.bigSepL_sep_eqv.mpr $$ [Hclaims Hphysical]
  · iframe Hclaims Hphysical
  iapply BigSepL.bigSepL_mono $$ Hpairs
  intro k j lookup
  have bound : j < 8 := List.mem_range.mp (List.mem_of_getElem? lookup)
  have pas := physical_offset va ppn j aligned bound
  iintro ⟨Hclaim,Hphysical⟩
  iunfold byte
  iexists ppn
  iframe Hclaim
  isimp only [pas]
  iunfold physicalByte
  iexact Hphysical

theorem access era tier ξ va dq value :
    iprop(KernelDatum.word capacity era tier ξ va dq value ⊢ ∃ ppn,
      claims capacity era tier va ppn ∗
      TsoContextReadWP.wordPointsto capacity.machine era ξ (physical ppn va) dq value ∗
      (∀ newValue, TsoContextReadWP.wordPointsto capacity.machine era ξ (physical ppn va) dq newValue -∗
        KernelDatum.word capacity era tier ξ va dq newValue)) := by
  iintro Hword
  ihave ⟨%ppn,#Hhead,Hword⟩ := choose capacity era tier ξ va dq value $$ Hword
  iunfold KernelDatum.word at Hword
  icases Hword with ⟨%aligned,Hbytes⟩
  ihave Hnormalized : iprop([∗list] j ∈ List.range 8,
      claim capacity era tier (addressAdd va j) ppn ∗
      physicalByte capacity era ξ (addressAdd (physical ppn va) j) dq (nthByte value j)) $$ [Hbytes]
  · iapply BigSepL.bigSepL_impl $$ Hbytes
    iintro !> %k %j %lookup Hbyte
    have bound : j < 8 := List.mem_range.mp (List.mem_of_getElem? lookup)
    iapply normalize_byte capacity era tier ξ va dq (nthByte value j) ppn j aligned bound $$ Hhead Hbyte
  ihave ⟨#Hclaims,Hphysical⟩ := BigSepL.bigSepL_sep_eqv.mp $$ Hnormalized
  iexists ppn
  iunfold claims
  iframe Hclaims
  isplitl [Hphysical]
  · unfold TsoContextReadWP.wordPointsto TsoContextWord.pointsto
    iunfold physicalByte at Hphysical
    iframe Hphysical
    ipureintro
    exact physical_aligned va ppn aligned
  · iintro %newValue Hphysical
    have restore := close capacity era tier ξ va dq newValue ppn aligned
    unfold claims at restore
    iapply restore $$ Hclaims Hphysical

theorem actual : Spec capacity := ⟨access capacity,close capacity,head capacity⟩

end Xv6.Kernel.KernelDatumWord
