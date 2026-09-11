import MachCSL.Logic.TsoContextBytesDefs

namespace MachCSL.Logic.TsoContextBytes
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContext

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  load : ∀ names cpu ξ eraImage g a n dq word,
    iprop(⊢ heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      ownContext capacity names cpu ξ -∗ window capacity names ξ a n dq word -∗
      heapAt capacity names g ∗ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      ownContext capacity names cpu ξ ∗ window capacity names ξ a n dq word ∗
      ⌜Readback g cpu a n word⌝)

end MachCSL.Logic.TsoContextBytes
