import MachCSL.Logic.FsStateDefs
import MachCSL.Logic.FsTopDefs

/-! Native link gathering interfaces. All existing names, elements, and
node/choice carriers are reused; no resource is allocated by these definitions. -/
namespace MachCSL.Logic.FsState
open Iris Iris.Std Iris.BI Xv6.Fs FsView

/-- Per-entry side condition for a total value-choice function. Tokenless
entries impose no value constraint, exactly as in the source. -/
def EntryChoicesOK (self : Int) (parent : Option Int) (orphan : Bool)
    (markers : NameSet) (entries : NameMap) (types : FName → FsLink.IType) : Prop :=
  ∀ name target, entries[name]? = some target →
    LinkFamily.tokenless self orphan name target = false →
    LinkFamily.EntryTypeOK self parent (decide (name ∈ markers)) name (types name)

variable {GF : BundledGFunctors} (view : View GF) (capacity : FsLink.Capacity GF)

def entriesAt (self : Int) (orphan : Bool) (entries : NameMap)
    (types : FName → FsLink.IType) : IProp GF :=
  bigSepM (M := EntryMap) (fun name target => entTokAt view capacity self orphan name target (types name)) entries

/-- Source fs_links_full: all native authority/fragment resources are still
at home, including present zero-multiplicity entries. -/
def fullLinks (γ : GName) (nodes : DurableState.InodeMap)
    (values : Int → FsLink.IType) : IProp GF :=
  bigSepM (M := InodeMap) (fun i n =>
    iOwn (E := capacity.link) γ (FsLink.fullElem i (LinkFamily.multiplicity n) (values i))) nodes

end MachCSL.Logic.FsState
