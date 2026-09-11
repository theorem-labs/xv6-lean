import MachCSL.Logic.EraSpec

namespace MachCSL.Logic.Era
open Iris Iris.BI MachCSL.Machine MachCSL.Memory
variable {GF : BundledGFunctors} (capacity : Capacity GF) (contracts : Contracts capacity)
include contracts

/-- Construct all seven actual-state era conjuncts without assuming initialized
ownership. Durable fixed-disk ownership is deliberately allocated elsewhere. -/
theorem allocate (image : BootImage) (g : State) (memory : Tso.AddressMap Byte)
    (template : Record) (diskBytes : Nat) (facts : BootFacts image g)
    (rep : FiniteMap.decode memory = g.memory) :
    iprop(⊢ |==> ∃ era : Record,
      ⌜era.image = memory ∧ AuxiliarySame era template⌝ ∗
      interp capacity era g ∗ bootClients capacity era memory g diskBytes) := by
  have resvOK := boot_reservations_ok image g facts
  have img : g.image = FiniteMap.decode memory := by
    rw [rep]
    exact facts.2.2.2.2.2.2.2.2.1
  imod contracts.tso.allocate image g memory facts rep with ⟨%tsoNames, Htso, Hb, HtsoClients⟩
  iunfold Tso.Interp.byteInterpAt at Hb
  icases Hb with ⟨Hb, _⟩
  iunfold Capacity.tso at Hb
  imod contracts.heap.attachMetadata tsoNames.ledger.bytes memory $$ Hb with ⟨%γmeta, Hheap, Htokens⟩
  imod contracts.registers.alloc g.registers with ⟨%γregs, Hregs, HregsClients⟩
  imod contracts.devices.alloc g.devices with ⟨%deviceNames, Hdevices, HdeviceClients⟩
  imod contracts.disk.alloc g.devices.virtio.v_disk diskBytes with ⟨%γdisk, Hdisk, HdiskClients⟩
  imod contracts.reservations.alloc g.reservations with ⟨%γresv, Hresv, HresvClients⟩
  imodintro
  iexists assemble template γregs tsoNames γmeta deviceNames γdisk γresv memory
  unfold interp bootClients heapInterpAt assemble Record.deviceNames Record.tsoNames Record.imageBytes
  rw [← img]
  iframe
  isplit
  · ipureintro
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  isplit
  · ipureintro
    exact rep
  · ipureintro
    exact resvOK

theorem eraSpec : EraSpec capacity := ⟨allocate capacity contracts⟩

end MachCSL.Logic.Era
