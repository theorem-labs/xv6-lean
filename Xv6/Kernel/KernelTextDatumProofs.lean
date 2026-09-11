import Xv6.Kernel.KernelTextDatumPureProofs
import Xv6.Kernel.KernelDatumLink
import MachCSL.Logic.TsoReadProofs
import MachCSL.Logic.TsoContextBytesProofs

namespace Xv6.Kernel.KernelTextDatum
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance pristine_persistent era pa : Persistent (pristine capacity era pa) := by infer_instance
instance pristine_timeless era pa : Timeless (pristine capacity era pa) := by infer_instance
instance claim_persistent era tier va ppn : Persistent (claim capacity era tier va ppn) := by
  unfold claim; infer_instance
instance claim_timeless era tier va ppn : Timeless (claim capacity era tier va ppn) := by
  unfold claim; infer_instance
instance rawByte_persistent era pa value : Persistent (rawByte capacity era pa .discard value) := by
  unfold rawByte Heap.pointsto
  infer_instance
instance byte_persistent era tier va value : Persistent (byte capacity era tier va .discard value) := by
  unfold byte; infer_instance
instance byte_timeless era tier va dq value : Timeless (byte capacity era tier va dq value) := by
  unfold byte; infer_instance
instance window_persistent era tier va n word : Persistent (window capacity era tier va n .discard word) := by
  unfold window; infer_instance
instance window_timeless era tier va n dq word : Timeless (window capacity era tier va n dq word) := by
  unfold window; infer_instance
instance claims_persistent era tier va n ppn : Persistent (claims capacity era tier va n ppn) := by
  unfold claims; infer_instance

theorem claim_agree era tier tier' va ppn ppn' :
    iprop(⊢ claim capacity era tier va ppn -∗ claim capacity era tier' va ppn' -∗ ⌜ppn = ppn'⌝) := by
  unfold claim
  iintro ⟨Hmap,_⟩ ⟨Hmap',_⟩
  ihave %same := (KptGhost.nativeSpec capacity.ghost).mapAgree era.kernelMap (vpn va) ppn ppn' .rx .rx
    $$ [Hmap Hmap']
  · iframe Hmap Hmap'
  ipureintro; exact same.1

theorem access era tier va dq value :
    iprop(byte capacity era tier va dq value ⊢ ∃ ppn,
      claim capacity era tier va ppn ∗ rawByte capacity era (physical ppn va) dq value ∗
      pristine capacity era (physical ppn va) ∗
      (rawByte capacity era (physical ppn va) dq value -∗ byte capacity era tier va dq value)) := by
  unfold byte
  iintro ⟨%ppn,#Hclaim,Hbyte,#Hpristine⟩
  iexists ppn
  iframe Hclaim Hbyte Hpristine
  iintro Hbyte
  iexists ppn
  iframe Hclaim Hbyte Hpristine

theorem close era tier va ppn dq value :
    iprop(⊢ claim capacity era tier va ppn -∗ rawByte capacity era (physical ppn va) dq value -∗
      pristine capacity era (physical ppn va) -∗ byte capacity era tier va dq value) := by
  iintro Hclaim Hbyte Hpristine
  iunfold byte
  iexists ppn
  iframe Hclaim Hbyte Hpristine

theorem pin_access era tier va ppn dq value :
    iprop(⊢ KptGhost.mapAt capacity.ghost era.kernelMap (vpn va) ppn .rx -∗
      byte capacity era tier va dq value -∗
      claim capacity era tier va ppn ∗ rawByte capacity era (physical ppn va) dq value ∗
      pristine capacity era (physical ppn va) ∗
      (rawByte capacity era (physical ppn va) dq value -∗ byte capacity era tier va dq value)) := by
  iintro Hmap Hbyte
  ihave ⟨%ppn',#Hclaim,Hbyte,#Hpristine,Hclose⟩ := access capacity era tier va dq value $$ Hbyte
  iunfold claim at Hclaim
  icases Hclaim with ⟨Hmap',_⟩
  ihave %same := (KptGhost.nativeSpec capacity.ghost).mapAgree era.kernelMap (vpn va) ppn ppn' .rx .rx
    $$ [Hmap Hmap']
  · iframe Hmap Hmap'
  obtain ⟨rfl,_⟩ := same
  ihave Hbyte := Hclose $$ Hbyte
  ihave ⟨%ppn'',Hclaim,Hbyte,Hpristine,Hclose⟩ := access capacity era tier va dq value $$ Hbyte
  iunfold claim at Hclaim
  icases Hclaim with ⟨Hmap'',%facts⟩
  ihave %same := (KptGhost.nativeSpec capacity.ghost).mapAgree era.kernelMap (vpn va) ppn ppn'' .rx .rx
    $$ [Hmap' Hmap'']
  · iframe Hmap' Hmap''
  obtain ⟨rfl,_⟩ := same
  iframe Hbyte Hpristine Hclose
  iunfold claim
  iframe Hmap''
  ipureintro; exact facts

theorem canonical era tier va dq value :
    iprop(byte capacity era tier va dq value ⊢ ⌜KernelDatum.Positive va⌝) := by
  unfold byte claim
  iintro ⟨%ppn,⟨_,%facts⟩,_,_⟩
  ipureintro; exact facts.1

theorem code_text era tier va dq value :
    iprop(byte capacity era tier va dq value ⊢ ∃ ppn, claim capacity era tier va ppn) := by
  unfold byte
  iintro ⟨%ppn,Hclaim,_,_⟩
  iexists ppn
  iexact Hclaim

theorem valid era tier g va dq value :
    iprop(⊢ heapAt capacity era g -∗ byte capacity era tier va dq value -∗
      ∃ ppn, claim capacity era tier va ppn ∗ ⌜g.memory (physical ppn va) = some value⌝) := by
  unfold heapAt Era.heapInterpAt byte
  iintro ⟨%memory,Hheap,%rep⟩ ⟨%ppn,Hclaim,Hbyte,_⟩
  ihave %found := MachCSL.Logic.Heap.valid capacity.machine.era.heap ⟨era.heap,era.metadata⟩ memory (physical ppn va) dq value $$ Hheap Hbyte
  iexists ppn
  iframe Hclaim
  ipureintro
  rw [← rep]
  exact found

theorem agree era tier tier' va dq dq' value value' :
    iprop(⊢ byte capacity era tier va dq value -∗ byte capacity era tier' va dq' value' -∗ ⌜value = value'⌝) := by
  unfold byte
  iintro ⟨%ppn,Hclaim,Hbyte,_⟩ ⟨%ppn',Hclaim',Hbyte',_⟩
  ihave %same := claim_agree capacity era tier tier' va ppn ppn' $$ Hclaim Hclaim'
  subst ppn'
  unfold rawByte
  simp only [MachCSL.Logic.Heap.pointsto_eq_byteElem]
  letI := capacity.machine.era.heap.ledger.bytes
  iapply ghost_map_elem_agree $$ [Hbyte Hbyte']
  iframe Hbyte Hbyte'

theorem mono era tier tier' va dq value (le : KernelDatum.Tier.Le tier tier') :
    iprop(byte capacity era tier va dq value ⊢ byte capacity era tier' va dq value) := by
  unfold byte claim
  iintro ⟨%ppn,⟨Hmap,%facts⟩,Hbyte,Hpristine⟩
  iexists ppn
  iframe Hmap Hbyte Hpristine
  ipureintro
  exact ⟨facts.1,facts.2.1,KernelDatum.pin_mono tier tier' ppn va le facts.2.2⟩

theorem persist era tier va dq value :
    iprop(byte capacity era tier va dq value ⊢ |==> byte capacity era tier va .discard value) := by
  unfold byte rawByte
  simp only [MachCSL.Logic.Heap.pointsto_eq_byteElem]
  iintro ⟨%ppn,Hclaim,Hbyte,Hpristine⟩
  letI := capacity.machine.era.heap.ledger.bytes
  imod ghost_map_elem_persist (GF := GF) (K := PhysicalAddress) (V := Byte) (H := Tso.AddressMap)
    era.heap (physical ppn va) dq value $$ Hbyte with Hbyte
  imodintro
  iexists ppn
  iframe Hclaim Hbyte Hpristine

theorem actual : Spec capacity :=
  ⟨pristine_persistent capacity,pristine_timeless capacity,claim_persistent capacity,
    claim_timeless capacity,byte_persistent capacity,byte_timeless capacity,
    window_persistent capacity,window_timeless capacity,claim_agree capacity,
    access capacity,close capacity,pin_access capacity,canonical capacity,code_text capacity,
    valid capacity,agree capacity,mono capacity,persist capacity⟩

end Xv6.Kernel.KernelTextDatum
