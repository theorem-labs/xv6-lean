import MachCSL.Logic.TsoPinnedStoreDefs

namespace MachCSL.Logic.TsoPinnedStore
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

structure StoreSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  update : ∀ names image before after old new author floors sets,
    TsoStore.SameDomain old new →
    (∀ a byte, new[a]? = some byte → byte ∈ sets a) →
    TsoStore.Transition before after new author →
    iprop(⊢ TsoStore.heapAt capacity names before.memory -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso image before -∗
      pinMap capacity names old (.own 1) floors sets ==∗
      TsoStore.heapAt capacity names after.memory ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso image after ∗
      Tso.History.logElem capacity.history names.tso.logEntries before.log.length
        ⟨FiniteMap.decode new, author⟩ ∗ storedMap capacity names new (before.log.length + 1) floors sets)
  window : ∀ names image before after a n {bits : Nat} (old new : BitVec bits) author
      (floors : Nat → Nat) (sets : Nat → Tso.ByteSet)
      (addressFloors : PhysicalAddress → Nat) (addressSets : PhysicalAddress → Tso.ByteSet),
    n ≤ 2 ^ 64 →
    (∀ j, j < n → addressFloors (addressAdd a j) = floors j) →
    (∀ j, j < n → addressSets (addressAdd a j) = sets j) →
    (∀ j, j < n → nthByte new j ∈ sets j) →
    TsoStore.WindowTransition before after a n new author →
    iprop(⊢ TsoStore.heapAt capacity names before.memory -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso image before -∗
      pinWindow capacity names a n old (.own 1) floors sets ==∗
      TsoStore.heapAt capacity names after.memory ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso image after ∗
      Tso.History.logElem capacity.history names.tso.logEntries before.log.length
        ⟨snapshot a n new, author⟩ ∗
      storedWindow capacity names a n new (before.log.length + 1) floors sets)

end MachCSL.Logic.TsoPinnedStore
