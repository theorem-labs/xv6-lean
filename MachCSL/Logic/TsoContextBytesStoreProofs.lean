import MachCSL.Logic.TsoContextBytesStoreSpec
import MachCSL.Logic.TsoContextBytesProofs
import MachCSL.Logic.TsoContextStoreProofs

namespace MachCSL.Logic.TsoContextBytesStore
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContext
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem window_map names ξ a n word (bound : n ≤ 2^64) :
    iprop(window capacity names ξ a n (.own 1) word ⊣⊢
      TsoContextStore.physMap capacity names ξ (TsoStore.windowMap a n word)) := by
  unfold window TsoContextBytes.window TsoContextStore.physMap
  exact (TsoStore.window_map (fun b byte => physPointsto capacity names ξ b (.own 1) byte)
    a n word bound).symm

/-- The native finite-map store updates each actual byte and mirrored
context timestamp once, retaining all unrelated heap and context clients. -/
theorem ordinary names cpu ξ eraImage before after a n old new (bound : n ≤ 2^64)
    (step : TsoContextStore.OrdinaryTransition before after (TsoStore.windowMap a n new) cpu) :
    iprop(⊢ heapAt capacity names before -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ownContext capacity names cpu ξ -∗ window capacity names ξ a n (.own 1) old ==∗
      heapAt capacity names after ∗ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      ownContext capacity names cpu ξ ∗ window capacity names ξ a n (.own 1) new ∗
      ⌜Readback after cpu a n new⌝) := by
  rw [(window_map capacity names ξ a n old bound).to_eq]
  iintro Hheap Htso Hrun Hold
  imod TsoContextStore.ordinary capacity names cpu ξ eraImage before after
    (TsoStore.windowMap a n old) (TsoStore.windowMap a n new)
    (TsoStore.windowMap_sameDomain a n old new) step $$ Hheap Htso Hrun Hold
    with ⟨Hheap, Htso, Hrun, Hnew⟩
  imodintro
  ihave Hword : window capacity names ξ a n (.own 1) new $$ [Hnew]
  · rw [(window_map capacity names ξ a n new bound).to_eq]
    iexact Hnew
  iapply TsoContextBytes.load capacity names cpu ξ eraImage after a n (.own 1) new $$ Hheap Htso Hrun Hword

theorem actual : Spec capacity := ⟨ordinary capacity⟩

end MachCSL.Logic.TsoContextBytesStore
