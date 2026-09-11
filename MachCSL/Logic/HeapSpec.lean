import MachCSL.Logic.HeapDefs

namespace MachCSL.Logic.Heap
open MachCSL.Memory Tso Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

structure HeapSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  allocate : ∀ memory, iprop(⊢ |==> ∃ names : Names,
    interp capacity names memory ∗ clients capacity names memory)
  attachMetadata : ∀ (γbytes : GName) (memory : AddressMap Byte),
    iprop(⊢ byteAuth capacity.ledger γbytes (.own 1) memory ==∗ ∃ γmeta : GName,
      interp capacity ⟨γbytes, γmeta⟩ memory ∗
      ([∗map] a ↦ _byte ∈ memory, token capacity ⟨γbytes, γmeta⟩ a ⊤))
  valid : ∀ names memory a dq byte,
    iprop(⊢ interp capacity names memory -∗ pointsto capacity names a dq byte -∗
      ⌜memory[a]? = some byte⌝)
  update : ∀ names memory a old new,
    iprop(interp capacity names memory ∗ pointsto capacity names a (.own 1) old ⊢ |==>
      (interp capacity names (Iris.Std.PartialMap.insert memory a new) ∗
      pointsto capacity names a (.own 1) new))
  allocateCell : ∀ names memory a byte, memory[a]? = none →
    iprop(interp capacity names memory ⊢ |==>
      (interp capacity names (Iris.Std.PartialMap.insert memory a byte) ∗
      pointsto capacity names a (.own 1) byte ∗ token capacity names a ⊤))
  tokenUnion : ∀ names a (left right : CoPset), left ## right →
    iprop(token capacity names a (left ∪ right) ⊣⊢
      token capacity names a left ∗ token capacity names a right)
  tokenDifference : ∀ names a (small large : CoPset), small ⊆ large →
    iprop(token capacity names a large ⊣⊢
      token capacity names a small ∗ token capacity names a (large \ small))
  metadataSet : ∀ {A : Type} [Pos.Countable A] names a (mask : CoPset) (ns : Namespace) (value : A),
    (↑ns : CoPset) ⊆ mask →
    iprop(⊢ token capacity names a mask ==∗ metadata capacity names a ns value)
  metadataAgree : ∀ {A : Type} [Pos.Countable A] names a ns (left right : A),
    iprop(⊢ metadata capacity names a ns left -∗ metadata capacity names a ns right -∗
      ⌜left = right⌝)

end MachCSL.Logic.Heap
