import MachCSL.Logic.TsoContextProofs
import MachCSL.Logic.LockSetLink

namespace MachCSL.Logic.TsoContext
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

/-- Reuses the canonical registry, including held sets at 26. No new camera. -/
abbrev registry := LockSet.registry

def ofEraCapacity {GF : BundledGFunctors} (capacity : Era.Capacity GF) : Capacity GF :=
  ⟨capacity.heap, capacity.views, capacity.history⟩
def ofEraNames (era : Era.Record) : Names := ⟨era.tsoNames, era.metadata⟩
def registryCapacity : Capacity registry := ofEraCapacity LockSet.eraCapacity

theorem bound_slot : registryCapacity.views.sharedNat.τ = 3 := rfl
theorem dirty_slot : registryCapacity.history.dirty.τ = 5 := rfl
theorem byte_slot : registryCapacity.heap.ledger.bytes.elem.τ = 0 := rfl
theorem timestamp_slot : registryCapacity.heap.ledger.timestamps.elem.τ = 1 := rfl
theorem log_slot : registryCapacity.history.logs.elem.τ = 4 := rfl

theorem registrySpec : TsoContextSpec registryCapacity := actual registryCapacity

/-- The physical source gate inside the actual complete era interpretation. -/
theorem era_load {GF : BundledGFunctors} (capacity : Era.Capacity GF)
    (era : Era.Record) cpu ξ g a dq byte :
    iprop(⊢ Era.interp capacity era g -∗
      ownContext (ofEraCapacity capacity) (ofEraNames era) cpu ξ -∗
      physPointsto (ofEraCapacity capacity) (ofEraNames era) ξ a dq byte -∗
      Era.interp capacity era g ∗
      ownContext (ofEraCapacity capacity) (ofEraNames era) cpu ξ ∗
      physPointsto (ofEraCapacity capacity) (ofEraNames era) ξ a dq byte ∗
      ⌜∀ view, g.views cpu ≤ view → read g.image g.log (hartAgent cpu) view a = some byte⌝) := by
  unfold Era.interp
  iintro ⟨Hregs, Hheap, Hdevice, Hdisk, Htso, Hresv, %valid⟩ Hrun Hbyte
  have gate := load_fact (ofEraCapacity capacity) (ofEraNames era) cpu ξ era.imageBytes g a dq byte
  rw [show heapAt (ofEraCapacity capacity) (ofEraNames era) g = Era.heapInterpAt capacity era g from rfl] at gate
  rw [show Tso.Interp.tsoInterpAt (ofEraCapacity capacity).tso (ofEraNames era).tso era.imageBytes g =
    Tso.Interp.tsoInterpAt capacity.tso era.tsoNames era.imageBytes g from rfl] at gate
  ihave %reads := gate $$ Hheap Htso Hrun Hbyte
  iframe Hregs Hheap Hdevice Hdisk Htso Hresv Hrun Hbyte
  ipureintro
  exact ⟨valid, reads⟩

end MachCSL.Logic.TsoContext
