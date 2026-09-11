import MachCSL.Logic.TsoPredicates
import Iris.BI.Lib.GenHeap

/-! Full native gen_heap over finite 64-bit physical addresses. The value
camera and points-to assertions are the existing TSO byte resource. -/
namespace MachCSL.Logic.Heap
open MachCSL.Memory Tso Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

abbrev MetadataMapRA := HeapView PhysicalAddress (Agree (DiscreteO GName)) AddressMap
abbrev MetadataMapRF := constOF MetadataMapRA
abbrev MetadataRF := constOF MetaUR

structure Capacity (GF : BundledGFunctors) where
  ledger : Tso.Capacity GF
  metadataMap : GhostMapG GF PhysicalAddress GName AddressMap
  metadata : ElemG GF MetadataRF

/-- Like the source era record, these are only runtime names, independent of GF. -/
structure Names where
  bytes : GName
  metadata : GName

@[reducible] def Capacity.preS {GF : BundledGFunctors} (c : Capacity GF) :
    genHeapPreS PhysicalAddress Byte GF AddressMap :=
  ⟨c.ledger.bytes, c.metadataMap, c.metadata⟩

@[reducible] def Capacity.native {GF : BundledGFunctors} (c : Capacity GF) (names : Names) :
    genHeapGS PhysicalAddress Byte GF AddressMap :=
  { heap := c.ledger.bytes, metaInfo := c.metadataMap, metaData := c.metadata, heapName := names.bytes, metaName := names.metadata }

variable {GF : BundledGFunctors} (capacity : Capacity GF)

abbrev metadataAuth (name : GName) (indirection : AddressMap GName) : IProp GF :=
  letI := capacity.metadataMap
  ghost_map_auth name (.own 1) indirection

abbrev interp (names : Names) (memory : AddressMap Byte) : IProp GF :=
  genHeapInterp (G := capacity.native names) memory

abbrev pointsto (names : Names) (a : PhysicalAddress) (dq : DFrac) (byte : Byte) : IProp GF :=
  pointsTo (G := capacity.native names) a dq byte

abbrev physicalPointsto (names : Names) (a : PhysicalAddress) (dq : DFrac) (byte : Byte) : IProp GF :=
  iprop(pointsto capacity names a dq byte ∗ ⌜AddrIsRAM a⌝)

abbrev token (names : Names) (a : PhysicalAddress) (mask : CoPset) : IProp GF :=
  metaToken (G := capacity.native names) a mask

abbrev metadata {A : Type} [Pos.Countable A] (names : Names) (a : PhysicalAddress)
    (ns : Namespace) (value : A) : IProp GF :=
  metaInfo (G := capacity.native names) a ns value

abbrev clients (names : Names) (memory : AddressMap Byte) : IProp GF :=
  iprop(([∗map] a ↦ byte ∈ memory, pointsto capacity names a (.own 1) byte) ∗
    ([∗map] a ↦ _byte ∈ memory, token capacity names a ⊤))

end MachCSL.Logic.Heap
