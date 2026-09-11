import MachCSL.Logic.TsoContextStoreDefs

namespace MachCSL.Logic.TsoContextStore
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContext

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  store : ∀ names cpu ξ eraImage before after old new,
    TsoStore.SameDomain old new → TsoStore.Transition before after new (hartAgent cpu) →
    iprop(⊢ TsoContext.heapAt capacity names before -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ownContext capacity names cpu ξ -∗ physMap capacity names ξ old ==∗
      TsoContext.heapAt capacity names after ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      ownContext capacity names cpu ξ ∗ physMap capacity names ξ new)
  ordinary : ∀ names cpu ξ eraImage before after old new,
    TsoStore.SameDomain old new → OrdinaryTransition before after new cpu →
    iprop(⊢ TsoContext.heapAt capacity names before -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ownContext capacity names cpu ξ -∗ physMap capacity names ξ old ==∗
      TsoContext.heapAt capacity names after ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      ownContext capacity names cpu ξ ∗ physMap capacity names ξ new)

end MachCSL.Logic.TsoContextStore
