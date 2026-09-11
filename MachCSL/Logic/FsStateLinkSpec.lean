import MachCSL.Logic.FsStateLinkDefs

namespace MachCSL.Logic.FsState
open Iris Iris.Std Iris.BI Iris.CMRA Xv6.Fs FsView

structure LinkResourceSpec {GF : BundledGFunctors} (view : View GF)
    (capacity : FsLink.Capacity GF) : Prop where
  packScatter : ∀ i n ty types,
    iOwn (E := capacity.link) view.link (LinkFamily.nodeElem i n ty types) ⊣⊢
      FsLink.auth capacity view.link i (LinkFamily.multiplicity n) ty ∗
      entriesAt view capacity i n.orphan n.dirEntries types
  inode : ∀ i n, inodeGhost view capacity i n ⊣⊢
    linkNode capacity view.link i n ∗ ⌜DurableNode.Local i n⌝
  gather : ∀ γ nodes (acc : FsLink.FamilyRA),
    iprop(⊢ iOwn (E := capacity.link) γ acc -∗ links capacity γ nodes -∗
      ∃ f, ⌜LinkFamily.ElemOK nodes f⌝ ∗
        iOwn (E := capacity.link) γ (acc • LinkFamily.elem nodes f))
  validToken : ∀ γ nodes root ty,
    iprop(⊢ links capacity γ nodes -∗ FsLink.tok capacity γ root ty -∗
      ⌜∃ f, LinkFamily.ElemOK nodes f ∧ ✓ (LinkFamily.elem nodes f • FsLink.tokElem root ty)⌝)

/-- Fresh native allocation contract, to be used by initial epoch-zero
setup. It does not transport or consume a pre-existing filesystem instance. -/
structure LinkBootSpec {GF : BundledGFunctors} (capacity : FsLink.Capacity GF)
    (topCapacity : FsTop.Capacity GF) : Prop where
  independent : ∀ left right f, LinkFamily.ElemOK left f → ✓ LinkFamily.elem left f →
    iprop(⊢ |==> ∃ gl gt, FsTop.auth topCapacity gt right ∗
      FsTop.allFragments topCapacity gt right ∗ links capacity gl left)
  rootSlack : ∀ nodes f root ty,
    LinkFamily.ElemOK nodes f → ✓ (LinkFamily.elem nodes f • FsLink.tokElem root ty) →
    iprop(⊢ |==> ∃ gl gt, FsTop.auth topCapacity gt nodes ∗
      FsTop.allFragments topCapacity gt nodes ∗ links capacity gl nodes ∗
      FsLink.tok capacity gl root ty)

end MachCSL.Logic.FsState
