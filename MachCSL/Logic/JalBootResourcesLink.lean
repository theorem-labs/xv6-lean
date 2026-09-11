import MachCSL.Logic.JalBootResourcesProofs
import MachCSL.Logic.JalBootResourcesCode
import MachCSL.Logic.JalBootResourcesShare

namespace MachCSL.Logic.JalBootResources
open Iris Iris.Std Iris.BI MachCSL.Machine MachCSL.Memory
open Iris.Std.PartialMap

/-- The four-byte lookup is a consequence of actual BootFacts and the allocated
finite map's decoding equation. No preferred preboot register witness is chosen. -/
theorem boot_code_lookup (g : State) (facts : BootFacts jalImage g)
    (m : Tso.AddressMap Byte) (decoded : Memory.FiniteMap.decode m = g.memory)
    (a : PhysicalAddress) (member : a ∈ codeKeys) : get? m a = some (codeValue a) := by
  have loaded : Memory.FiniteMap.decode m = loadedRam jalImage := decoded.trans facts.2.1
  have atByte := congrFun loaded a
  change get? m a = loadedRam jalImage a at atByte
  rw [atByte]
  simp only [codeKeys, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

/-- Consume only the four code timestamps, share the four byte cells, and
retain every other full byte/timestamp resource and the initial log receipt. -/
theorem boot_code (era : Era.Record) (m : Tso.AddressMap Byte)
    (lookup : ∀ a, a ∈ codeKeys → get? m a = some (codeValue a)) :
    iprop(⊢ Tso.Interp.bootClients capacity.era.tso era.tsoNames m ==∗
      sharedCode capacity era ∗ byteRemainder capacity.era.heap.ledger era.heap m ∗
      timestampRemainder capacity.era.heap.ledger era.timestamps m ∗
      Tso.Views.natLB capacity.era.views era.logLength 0) := by
  unfold Tso.Interp.bootClients
  simp only [Era.Record.tsoNames, Era.Capacity.tso]
  iintro ⟨Hbytes, Htime, Hlength⟩
  ihave ⟨Hcode, Hrest⟩ := extract_code_bytes capacity.era.heap.ledger era.heap m lookup $$ Hbytes
  imod mint_code_timestamps capacity.era.heap.ledger era.timestamps m lookup $$ Htime with ⟨Hpristine, Htime⟩
  have share := code_eight capacity era
  unfold EventWP.codeResources at share
  ihave Hcode := share $$ [Hcode Hpristine]
  · iframe
  · imodintro
    iframe

end MachCSL.Logic.JalBootResources
