import MachCSL.Logic.ContextPinMintProofs
import MachCSL.Logic.TsoContextLink

namespace MachCSL.Logic.ContextPinMint
open Iris

/-- The fourteen source contracts are constructed at any supplied native
capacity. No context, heap, timestamp or era name is allocated here. -/
theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity where
  timestamp_bound := timestamp_bound capacity
  own_bound := own_bound capacity
  ledger_mint := ledger_mint capacity
  view_now := view_now capacity
  log_now := log_now capacity
  byte := byte capacity
  bytes := bytes capacity
  word := word capacity
  byte_top := byte_top capacity
  bytes_top := bytes_top capacity
  word_top := word_top capacity
  byte_boot := byte_boot capacity
  bytes_boot := bytes_boot capacity
  word_boot := word_boot capacity

theorem registrySpec : Spec TsoContext.registryCapacity := nativeSpec _

/-- Any complete era capacity supplies these exact existing components. -/
theorem eraSpec {GF : BundledGFunctors} (capacity : Era.Capacity GF) :
    Spec (TsoContext.ofEraCapacity capacity) := nativeSpec _

end MachCSL.Logic.ContextPinMint
