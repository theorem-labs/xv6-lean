import MachCSL.Logic.IcacheTopRetagSpec
import MachCSL.Logic.IcacheTopRegistryLink

namespace MachCSL.Logic.IcacheTopRetag
open Iris Iris.Std Iris.BI IcacheTopRegistry

theorem clean_retag (nodes : Xv6.Fs.DurableState.InodeMap) (arms : ArmMap Entry)
    (i : Int) (new : FsTop.Node) (localNode : Xv6.Fs.DurableNode.Local i new)
    (h : clean nodes arms) : clean (nodes.insert i new) arms := by
  intro j node found clear
  by_cases same : i = j
  · subst j
    have eq : new = node := Option.some.inj ((_root_.Std.ExtTreeMap.getElem?_insert_self).symm.trans found)
    simpa only [eq] using localNode
  · apply h j node _ clear
    simpa only [_root_.Std.ExtTreeMap.getElem?_insert, show compare i j ≠ .eq by simpa using same, if_false] using found

theorem clean_retag_armed (nodes : Xv6.Fs.DurableState.InodeMap) (arms : ArmMap Entry)
    (k t : Nat) (q : Qp) (S : InumSet) (i : Int) (new : FsTop.Node)
    (entry : get? arms k = some ((t,q),S)) (member : i ∈ S)
    (h : clean nodes arms) : clean (nodes.insert i new) arms := by
  intro j node found clear
  by_cases same : i = j
  · subst j
    exact (clear k t q S entry member).elim
  · apply h j node _ clear
    simpa only [_root_.Std.ExtTreeMap.getElem?_insert, show compare i j ≠ .eq by simpa using same, if_false] using found

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) (names : Names)

theorem retag (N : Namespace) (E : CoPset) (i : Int) (old new : FsTop.Node)
    (mask : (↑N : CoPset) ⊆ E) (localNode : Xv6.Fs.DurableNode.Local i new) :
    iprop(⊢ invariant capacity names N -∗ FsTop.frag capacity.top names.top i old
      ={E}=∗ FsTop.frag capacity.top names.top i new) := by
  iintro #Hi Hf
  iunfold invariant at Hi
  imod inv_acc mask $$ Hi with ⟨Hb, Hclose⟩
  imod Hb
  iunfold body at Hb
  icases Hb with ⟨%nodes, %arms, Ha, Hla, Hp, %hc⟩
  imod FsTop.update capacity.top names.top nodes i old new $$ Ha Hf with ⟨Ha, Hf⟩
  imod Hclose $$ [Ha Hla Hp] with _
  · iintro !>
    unfold body
    iexists nodes.insert i new, arms
    iframe Ha Hla Hp
    ipureintro
    exact clean_retag nodes arms i new localNode hc
  · imodintro
    iexact Hf

theorem retag_armed (N : Namespace) (E : CoPset) (k t : Nat) (q : Qp) (S : InumSet)
    (i : Int) (old new : FsTop.Node) (mask : (↑N : CoPset) ⊆ E) (member : i ∈ S) :
    iprop(⊢ invariant capacity names N -∗ armed capacity names k t q S -∗
      FsTop.frag capacity.top names.top i old ={E}=∗
      armed capacity names k t q S ∗ FsTop.frag capacity.top names.top i new) := by
  iintro #Hi Hr Hf
  iunfold invariant at Hi
  imod inv_acc mask $$ Hi with ⟨Hb, Hclose⟩
  imod Hb
  iunfold body at Hb
  icases Hb with ⟨%nodes, %arms, Ha, Hla, Hp, %hc⟩
  ihave %entry := armed_lookup capacity names arms k t q S $$ Hla Hr
  imod FsTop.update capacity.top names.top nodes i old new $$ Ha Hf with ⟨Ha, Hf⟩
  imod Hclose $$ [Ha Hla Hp] with _
  · iintro !>
    unfold body
    iexists nodes.insert i new, arms
    iframe Ha Hla Hp
    ipureintro
    exact clean_retag_armed nodes arms k t q S i new entry member hc
  · imodintro
    iframe Hr Hf

theorem actual : Spec capacity := ⟨retag capacity, retag_armed capacity⟩

theorem nativeSpec [InvGS IcacheTopRegistry.registry] : Spec IcacheTopRegistry.nativeCapacity :=
  actual IcacheTopRegistry.nativeCapacity

end MachCSL.Logic.IcacheTopRetag
