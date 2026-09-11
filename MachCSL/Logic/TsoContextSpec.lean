import MachCSL.Logic.TsoContextDefs

namespace MachCSL.Logic.TsoContext
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

structure TsoContextSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  allocate : ∀ names cpu,
    iprop(⊢ |==> ∃ ξ, ownContext capacity names cpu ξ)
  load : ∀ names cpu ξ eraImage g a dq byte,
    iprop(⊢ heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      ownContext capacity names cpu ξ -∗ physPointsto capacity names ξ a dq byte -∗
      heapAt capacity names g ∗ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      ownContext capacity names cpu ξ ∗ physPointsto capacity names ξ a dq byte ∗
      ⌜∀ view, g.views cpu ≤ view → read g.image g.log (hartAgent cpu) view a = some byte⌝)

end MachCSL.Logic.TsoContext
