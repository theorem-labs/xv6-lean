import MachCSL.Logic.TsoContextStoreProofs
import MachCSL.Logic.TsoContextLink

namespace MachCSL.Logic.TsoContextStore
open Iris Iris.Std Iris.BI MachCSL.Memory MachCSL.Machine TsoContext

abbrev registry := TsoContext.registry
abbrev registryCapacity := TsoContext.registryCapacity

theorem registrySpec : Spec registryCapacity := actual registryCapacity

theorem context_capacity_same : registryCapacity = TsoContext.registryCapacity := rfl

/-- Ordinary-store readback at all permitted views follows from the actual
new dirty receipts, without advancing the writing hart's view. -/
theorem ordinary_readback {GF : BundledGFunctors} (capacity : Capacity GF)
    names cpu ξ eraImage before after old new
    (same : TsoStore.SameDomain old new) (step : OrdinaryTransition before after new cpu) :
    iprop(⊢ TsoContext.heapAt capacity names before -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ownContext capacity names cpu ξ -∗ physMap capacity names ξ old ==∗
      TsoContext.heapAt capacity names after ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      ownContext capacity names cpu ξ ∗ physMap capacity names ξ new ∗
      ⌜∀ a byte, PartialMap.get? new a = some byte → ∀ view, after.views cpu ≤ view →
        read after.image after.log (hartAgent cpu) view a = some byte⌝) := by
  iintro Hheap Htso Hrun Hold
  imod ordinary capacity names cpu ξ eraImage before after old new same step $$ Hheap Htso Hrun Hold
    with ⟨Hheap, Htso, Hrun, Hnew⟩
  imodintro
  ihave %reads : ⌜∀ a byte, PartialMap.get? new a = some byte → ∀ view, after.views cpu ≤ view →
      read after.image after.log (hartAgent cpu) view a = some byte⌝ $$ [Hheap Htso Hrun Hnew]
  · iapply pure_forall.mpr
    iintro %a
    iapply pure_forall.mpr
    iintro %byte
    iapply pure_imp.mpr
    iintro %lookup
    unfold physMap
    ihave Hb := BigSepM.bigSepM_lookup lookup $$ Hnew
    iapply TsoContext.load_fact capacity names cpu ξ eraImage after a (.own 1) byte $$ Hheap Htso Hrun Hb
  · iframe Hheap Htso Hrun Hnew
    ipureintro
    exact reads

end MachCSL.Logic.TsoContextStore
