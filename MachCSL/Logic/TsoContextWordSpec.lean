import MachCSL.Logic.TsoContextWordDefs

namespace MachCSL.Logic.TsoContextWord
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContext

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  load : ∀ names cpu ξ eraImage g a dq word,
    iprop(⊢ heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      ownContext capacity names cpu ξ -∗ pointsto capacity names ξ a dq word -∗
      heapAt capacity names g ∗ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      ownContext capacity names cpu ξ ∗ pointsto capacity names ξ a dq word ∗
      ⌜Readback g cpu a word⌝)
  ordinary : ∀ names cpu ξ eraImage before after a old new,
    TsoContextStore.OrdinaryTransition before after (TsoStore.windowMap a 8 new) cpu →
    iprop(⊢ heapAt capacity names before -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ownContext capacity names cpu ξ -∗ pointsto capacity names ξ a (.own 1) old ==∗
      heapAt capacity names after ∗ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      ownContext capacity names cpu ξ ∗ pointsto capacity names ξ a (.own 1) new ∗
      ⌜Readback after cpu a new⌝)

end MachCSL.Logic.TsoContextWord
