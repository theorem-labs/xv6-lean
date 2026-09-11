import MachCSL.Logic.TsoContextBytesStoreDefs

namespace MachCSL.Logic.TsoContextBytesStore
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContext

/-- A byte window has no repeated physical keys when its width is at most
2^64. The transition is supplied by the actual event adapter in the subsequent native WP layer. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  ordinary : ∀ names cpu ξ eraImage before after a n old new,
    n ≤ 2^64 →
    TsoContextStore.OrdinaryTransition before after (TsoStore.windowMap a n new) cpu →
    iprop(⊢ heapAt capacity names before -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ownContext capacity names cpu ξ -∗ window capacity names ξ a n (.own 1) old ==∗
      heapAt capacity names after ∗ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      ownContext capacity names cpu ξ ∗ window capacity names ξ a n (.own 1) new ∗
      ⌜Readback after cpu a n new⌝)

end MachCSL.Logic.TsoContextBytesStore
