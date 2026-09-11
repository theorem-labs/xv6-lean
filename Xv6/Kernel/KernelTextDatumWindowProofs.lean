import Xv6.Kernel.KernelTextDatumProofs

namespace Xv6.Kernel.KernelTextDatum
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem window_head era tier va n ppn (positive : 0 < n) :
    iprop(claims capacity era tier va n ppn ⊢ claim capacity era tier va ppn) := by
  unfold claims
  have get := BigSepL.bigSepL_lookup (PROP := IProp GF)
    (Φ := fun _ j => claim capacity era tier (addressAdd va j) ppn)
    (l := List.range n) (i := 0) (x := 0) (by simp [positive])
  simpa [addressAdd] using get

theorem choose era tier va n dq word (positive : 0 < n) :
    iprop(window capacity era tier va n dq word ⊢ ∃ ppn,
      claim capacity era tier va ppn ∗ window capacity era tier va n dq word) := by
  unfold window
  iintro Hbytes
  have get := (BigSepL.bigSepL_lookup_acc (PROP := IProp GF)
    (Φ := fun _ j => byte capacity era tier (addressAdd va j) dq (nthByte word j))
    (l := List.range n) (i := 0) (x := 0) (by simp [positive])).mp
  ihave ⟨Hzero,Hclose⟩ := get $$ Hbytes
  iunfold byte at Hzero
  icases Hzero with ⟨%ppn,#Hclaim,Hphysical,#Hpristine⟩
  iexists ppn
  have addZero : addressAdd va 0 = va := by simp [addressAdd]
  isimp only [addZero] at Hclaim Hphysical Hpristine
  iframe Hclaim
  have same : (List.range n).set 0 0 = List.range n := by
    cases n with
    | zero => omega
    | succ n => simp [List.range_succ_eq_map]
  ihave Hclose := Hclose $$ %0
  isimp only [same] at Hclose
  iapply Hclose $$ [Hphysical]
  iunfold byte
  iexists ppn
  isimp only [addZero]
  iframe Hclaim Hphysical Hpristine

theorem raw_physical era tier va ppn dq value :
    iprop(⊢ claim capacity era tier va ppn -∗ rawByte capacity era (physical ppn va) dq value -∗
      Tso.physBytePointsto capacity.machine.era.heap.ledger era.heap (physical ppn va) dq value) := by
  unfold claim rawByte Tso.physBytePointsto
  simp only [MachCSL.Logic.Heap.pointsto_eq_byteElem]
  iintro ⟨_,%facts⟩ Hbyte
  iframe Hbyte
  ipureintro
  exact text_ram _ facts.2.1

theorem normalize_byte era tier va n dq value ppn j
    (page : SamePage va n) (bound : j < n) :
    iprop(⊢ claim capacity era tier va ppn -∗ byte capacity era tier (addressAdd va j) dq value -∗
      claim capacity era tier (addressAdd va j) ppn ∗
      Tso.physBytePointsto capacity.machine.era.heap.ledger era.heap
        (addressAdd (physical ppn va) j) dq value ∗ pristine capacity era (addressAdd (physical ppn va) j)) := by
  iintro Hhead Hbyte
  iunfold claim at Hhead
  icases Hhead with ⟨Hmap,_⟩
  have vpns := vpn_offset va n j page bound
  have pas := physical_offset va ppn n j page bound
  isimp only [← vpns] at Hmap
  ihave ⟨#Hclaim,Hbyte,#Hpristine,_⟩ := pin_access capacity era tier (addressAdd va j) ppn dq value $$ Hmap Hbyte
  ihave Hbyte := raw_physical capacity era tier (addressAdd va j) ppn dq value $$ Hclaim Hbyte
  isimp only [pas] at Hbyte Hpristine
  iframe Hclaim Hbyte Hpristine

theorem window_close era tier va n ppn dq word (page : SamePage va n) :
    iprop(⊢ claims capacity era tier va n ppn -∗ physicalWindow capacity era (physical ppn va) n dq word -∗
      pristineWindow capacity era (physical ppn va) n -∗ window capacity era tier va n dq word) := by
  unfold claims physicalWindow pristineWindow TsoRead.byteWindow TsoRead.pristineWindow window
  iintro Hclaims Hphysical Hpristine
  ihave Hpairs := BigSepL.bigSepL_sep_eqv.mpr $$ [Hphysical Hpristine]
  · iframe Hphysical Hpristine
  ihave Hpairs := BigSepL.bigSepL_sep_eqv.mpr $$ [Hclaims Hpairs]
  · iframe Hclaims Hpairs
  iapply BigSepL.bigSepL_mono $$ Hpairs
  intro k j lookup
  have bound : j < n := List.mem_range.mp (List.mem_of_getElem? lookup)
  have pas := physical_offset va ppn n j page bound
  iintro ⟨Hclaim,⟨Hphysical,_⟩,Hpristine⟩
  iunfold byte
  iexists ppn
  iframe Hclaim
  isimp only [pas]
  unfold rawByte
  simp only [MachCSL.Logic.Heap.pointsto_eq_byteElem]
  iframe Hphysical Hpristine

theorem window_access era tier va n dq word (positive : 0 < n) (page : SamePage va n) :
    iprop(window capacity era tier va n dq word ⊢ ∃ ppn,
      claims capacity era tier va n ppn ∗ physicalWindow capacity era (physical ppn va) n dq word ∗
      pristineWindow capacity era (physical ppn va) n ∗
      (physicalWindow capacity era (physical ppn va) n dq word -∗ window capacity era tier va n dq word)) := by
  iintro Hword
  ihave ⟨%ppn,#Hhead,Hword⟩ := choose capacity era tier va n dq word positive $$ Hword
  iunfold window at Hword
  ihave Hnormalized : iprop([∗list] j ∈ List.range n,
      claim capacity era tier (addressAdd va j) ppn ∗
      Tso.physBytePointsto capacity.machine.era.heap.ledger era.heap (addressAdd (physical ppn va) j) dq (nthByte word j) ∗
      pristine capacity era (addressAdd (physical ppn va) j)) $$ [Hword]
  · iapply BigSepL.bigSepL_impl $$ Hword
    iintro !> %k %j %lookup Hbyte
    have bound : j < n := List.mem_range.mp (List.mem_of_getElem? lookup)
    iapply normalize_byte capacity era tier va n dq (nthByte word j) ppn j page bound $$ Hhead Hbyte
  ihave ⟨#Hclaims,Hrest⟩ := BigSepL.bigSepL_sep_eqv.mp $$ Hnormalized
  ihave ⟨Hphysical,#Hpristine⟩ := BigSepL.bigSepL_sep_eqv.mp $$ Hrest
  ihave #HC : claims capacity era tier va n ppn $$ []
  · unfold claims; iexact Hclaims
  ihave HP : physicalWindow capacity era (physical ppn va) n dq word $$ [Hphysical]
  · unfold physicalWindow TsoRead.byteWindow; iexact Hphysical
  ihave #HT : pristineWindow capacity era (physical ppn va) n $$ []
  · unfold pristineWindow TsoRead.pristineWindow; iexact Hpristine
  iexists ppn
  iframe HC HP HT
  iintro Hphysical
  iapply window_close capacity era tier va n ppn dq word page $$ HC Hphysical HT

theorem identity_byte era va dq value :
    iprop(byte capacity era .identity va dq value ⊢
      Tso.physBytePointsto capacity.machine.era.heap.ledger era.heap va dq value ∗ pristine capacity era va ∗
      (Tso.physBytePointsto capacity.machine.era.heap.ledger era.heap va dq value -∗
        byte capacity era .identity va dq value)) := by
  iintro Hbyte
  ihave ⟨%ppn,#Hclaim,Hbyte,#Hpristine,Hclose⟩ := access capacity era .identity va dq value $$ Hbyte
  ihave Hphysical := raw_physical capacity era .identity va ppn dq value $$ Hclaim Hbyte
  iunfold claim at Hclaim
  icases Hclaim with ⟨_,%facts⟩
  have same : physical ppn va = va := facts.2.2
  isimp only [same] at Hphysical Hpristine Hclose
  iframe Hphysical Hpristine
  iintro ⟨Hbyte,_⟩
  iunfold rawByte at Hclose
  isimp only [MachCSL.Logic.Heap.pointsto_eq_byteElem] at Hclose
  iapply Hclose $$ Hbyte

theorem identity_access era va n dq word :
    iprop(window capacity era .identity va n dq word ⊢
      physicalWindow capacity era va n dq word ∗ pristineWindow capacity era va n ∗
      (physicalWindow capacity era va n dq word -∗ window capacity era .identity va n dq word)) := by
  unfold window physicalWindow pristineWindow TsoRead.byteWindow TsoRead.pristineWindow
  iintro Hword
  ihave Hrows := BigSepL.bigSepL_mono (fun {_ j} _ => identity_byte capacity era (addressAdd va j) dq (nthByte word j)) $$ Hword
  ihave ⟨Hbytes,Hrest⟩ := BigSepL.bigSepL_sep_eqv.mp $$ Hrows
  ihave ⟨#Hpristine,Hclose⟩ := BigSepL.bigSepL_sep_eqv.mp $$ Hrest
  iframe Hbytes Hpristine
  iintro Hbytes
  ihave Hpairs := BigSepL.bigSepL_sep_eqv.mpr $$ [Hbytes Hclose]
  · iframe Hbytes Hclose
  iapply BigSepL.bigSepL_mono $$ Hpairs
  intro k j lookup
  iintro ⟨Hbyte,Hclose⟩
  iapply Hclose $$ Hbyte

theorem split_four era tier va dq (word : BitVec 32) :
    iprop(window capacity era tier va 4 dq word ⊣⊢
      window capacity era tier va 2 dq (lowHalf word) ∗
      window capacity era tier (addressAdd va 2) 2 dq (highHalf word)) := by
  have lo0 := low_bytes word 0 (by decide)
  have lo1 := low_bytes word 1 (by decide)
  have hi0 := high_bytes word 0 (by decide)
  have hi1 := high_bytes word 1 (by decide)
  have a0 : addressAdd (addressAdd va 2) 0 = addressAdd va 2 := by simp [addressAdd]
  have a1 : addressAdd (addressAdd va 2) 1 = addressAdd va 3 := by
    simp [addressAdd, BitVec.add_assoc]
  simp only [window, show List.range 4 = [0,1,2,3] from rfl,
    show List.range 2 = [0,1] from rfl, BigSepL.bigSepL_cons.to_eq, BigSepL.bigSepL_nil.to_eq,
    sep_emp.to_eq, lo0,lo1,hi0,hi1,a0,a1]
  exact sep_assoc.symm

theorem context_identity era ξ va n word :
    iprop(window capacity era .identity va n .discard word ⊢ contextWindow capacity era ξ va n word) := by
  iintro Hword
  ihave ⟨Hbytes,Hpristine,_⟩ := identity_access capacity era va n .discard word $$ Hword
  have convert : iprop(physicalWindow capacity era va n .discard word ∗ pristineWindow capacity era va n ⊢
      contextWindow capacity era ξ va n word) :=
    TsoContextBytes.of_pristine_discard (TsoContextReadWP.contextCapacity capacity.machine)
      (TsoContextReadWP.contextNames era) ξ va n word
  iapply convert $$ [Hbytes Hpristine]
  iframe Hbytes Hpristine

theorem context_full era tier ξ va n word (positive : 0 < n) (page : SamePage va n) :
    iprop(window capacity era tier va n .discard word ⊢ ∃ ppn,
      claims capacity era tier va n ppn ∗ contextWindow capacity era ξ (physical ppn va) n word) := by
  iintro Hword
  ihave ⟨%ppn,Hclaims,Hbytes,Hpristine,_⟩ := window_access capacity era tier va n .discard word positive page $$ Hword
  iexists ppn
  iframe Hclaims
  have convert : iprop(physicalWindow capacity era (physical ppn va) n .discard word ∗ pristineWindow capacity era (physical ppn va) n ⊢
      contextWindow capacity era ξ (physical ppn va) n word) :=
    TsoContextBytes.of_pristine_discard (TsoContextReadWP.contextCapacity capacity.machine)
      (TsoContextReadWP.contextNames era) ξ (physical ppn va) n word
  iapply convert $$ [Hbytes Hpristine]
  iframe Hbytes Hpristine

end Xv6.Kernel.KernelTextDatum
