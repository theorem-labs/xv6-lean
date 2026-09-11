import Xv6.Kernel.KernelTextImagePureProofs
import Xv6.Kernel.KernelTextDatumLink
import Xv6.Kernel.KernelMapStaticLink

namespace Xv6.Kernel.KernelTextImage
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
open Xv6.Generated.KernelMaps
variable {GF : BundledGFunctors} (capacity : Capacity GF)

attribute [local irreducible] codeRuns

instance text_persistent era tier : Persistent (text capacity era tier) := by
  unfold text; infer_instance
instance text_intuitionistic era tier : Intuitionistic (text capacity era tier) where
  intuitionistic := by iintro #H; iintro !>; iexact H
instance physical_persistent era : Persistent (physicalText capacity era) := by
  unfold physicalText; infer_instance
instance listed_persistent era tier : Persistent (listedText capacity era tier) := by
  unfold listedText; infer_instance

theorem lookup era tier a b (found : sourceMap a = some b) :
    iprop(text capacity era tier ⊢ KernelTextDatum.byte capacity era tier (address a) .discard (value b)) := by
  unfold text
  iintro H
  iapply H $$ %a %b %found

theorem listed era tier : iprop(text capacity era tier ⊣⊢ listedText capacity era tier) := by
  constructor
  · unfold listedText
    simp only [BigSepL.bigSepL_map]
    apply BigSepL.bigSepL_intro
    intro k run found
    apply BigSepL.bigSepL_intro
    intro l j hj
    have member := List.mem_of_getElem? found
    have bound : j < run.length := List.mem_range.mp (List.mem_of_getElem? hj)
    exact lookup capacity era tier _ _ (listed_lookup run member j bound)
  · unfold listedText
    iintro #H
    iunfold text
    iintro %a %b %found
    obtain ⟨run, member, j, bound, rfl, rfl⟩ := lookup_listed a b found
    obtain ⟨k, found⟩ := List.mem_iff_getElem?.mp member
    ihave Hrun := BigSepL.bigSepL_lookup found $$ H
    isimp [BigSepL.bigSepL_map] at Hrun
    iapply BigSepL.bigSepL_lookup (show (List.range run.length)[j]? = some j from by simp [bound]) $$ Hrun

private theorem physical_from (era : Era.Record) (P : IProp GF) [Persistent P]
    (maps : ∀ a b, sourceMap a = some b → iprop(P ⊢
      KptGhost.mapAt capacity.ghost era.kernelMap (KernelDatum.vpn (address a))
        (KernelMapStatic.identityPPN (KernelDatum.vpn (address a))) .rx)) :
    iprop(⊢ physicalText capacity era -∗ P -∗ text capacity era .identity) := by
  iintro #Hphysical #Hmaps
  iunfold text
  iintro %a %b %found
  have facts := text_address a b found
  have identity := KernelMapStatic.identity (address a) facts.1
  ihave Hmap := maps a b found $$ Hmaps
  iunfold physicalText at Hphysical
  ihave ⟨Hbyte,Hpristine⟩ := Hphysical $$ %a %b %found
  ihave Hclaim : KernelTextDatum.claim capacity era .identity (address a)
      (KernelMapStatic.identityPPN (KernelDatum.vpn (address a))) $$ [Hmap]
  · iunfold KernelTextDatum.claim
    iframe Hmap
    ipureintro
    exact ⟨facts.1, by simpa only [identity] using facts.2, identity⟩
  have rule := KernelTextDatum.close capacity era .identity (address a)
    (KernelMapStatic.identityPPN (KernelDatum.vpn (address a))) .discard (value b)
  simp only [KernelTextDatum.physical, identity] at rule
  iapply rule $$ Hclaim Hbyte Hpristine

theorem physical era :
    iprop(⊢ physicalText capacity era -∗ KernelMapStatic.claims capacity era.kernelMap -∗ text capacity era .identity) := by
  apply physical_from capacity era
  intro a b found
  have facts := text_address a b found
  exact (KernelMapStatic.nativeSpec capacity).lookup era.kernelMap _ .rx
    (KernelMapStatic.text_class _ facts.2.1 facts.2.2)

theorem mono era tier tier' (le : KernelDatum.Tier.Le tier tier') :
    iprop(text capacity era tier ⊢ text capacity era tier') := by
  iintro #H
  iunfold text
  iintro %a %b %found
  ihave Hbyte := lookup capacity era tier a b found $$ H
  iapply KernelTextDatum.mono capacity era tier tier' (address a) .discard (value b) le $$ Hbyte

theorem window era tier a n (word : BitVec (8*n))
    (bytes : ∀ j, j < n → ∃ b, sourceMap (a + (j : Int)) = some b ∧ value b = nthByte word j) :
    iprop(text capacity era tier ⊢ KernelTextDatum.window capacity era tier (address a) n .discard word) := by
  unfold KernelTextDatum.window
  apply BigSepL.bigSepL_intro
  intro k j found
  obtain ⟨b, found, value_eq⟩ := bytes j (List.mem_range.mp (List.mem_of_getElem? found))
  have addr : address (a + (j : Int)) = addressAdd (address a) j := by
    simp only [address, addressAdd, BitVec.ofInt_add, BitVec.ofInt_natCast]
  simpa only [addr, value_eq] using lookup capacity era tier (a + (j : Int)) b found

theorem mycpu era tier (shell : MycpuRegimeShell.Capacity GF) (same : shell.translation = capacity) :
    iprop(text capacity era tier ⊢ text capacity era tier ∗ MycpuKptFetch.code shell era tier) := by
  iintro #H
  iframe H
  have windows : iprop(text capacity era tier ⊢ MycpuKptFetch.code shell era tier) := by
    unfold MycpuKptFetch.code MycpuKptFetch.window
    rw [same]
    apply BigSepL.bigSepL_intro
    intro k i found
    change iprop(text capacity era tier ⊢ KernelTextDatum.window capacity era tier
      (address (MycpuDecode.base + (MycpuDecode.offset i : Int))) (MycpuFetchBytes.width i)
      .discard (MycpuFetchBytes.word i))
    apply window capacity era tier
    intro j bound
    simpa only [Int.natCast_add, Int.add_assoc] using mycpu_bytes i ⟨j,bound⟩
  iapply windows $$ H

theorem actual : Spec capacity :=
  ⟨text_persistent capacity, listed capacity, lookup capacity, physical capacity,
    mono capacity, window capacity, mycpu capacity⟩

end Xv6.Kernel.KernelTextImage
