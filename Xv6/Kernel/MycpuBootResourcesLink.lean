import Xv6.Kernel.MycpuBootResourcesSharing
import MachCSL.Logic.EraLink

namespace Xv6.Kernel.MycpuBootResources
open Iris Iris.BI MachCSL.Memory MachCSL.Machine MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Era.Capacity GF)

/-- Consume the allocator's existing client maps, preserving its log receipt. -/
theorem boot_resources (era : Era.Record) (g : State) (facts : BootFacts Xv6.Machine.bootImage g)
    (memory : Tso.AddressMap Byte) (decoded : FiniteMap.decode memory = g.memory) :
    iprop(Tso.Interp.bootClients capacity.tso era.tsoNames memory ⊢
      rawSpan (storeCapacity capacity) (storeNames era) ∗
      remainder (storeCapacity capacity) (storeNames era) memory ∗
      Tso.Views.natLB capacity.views era.logLength 0) := by
  unfold Tso.Interp.bootClients Era.Capacity.tso
  iintro ⟨Hb, Ht, Hlength⟩
  have extracted := extract_initial (storeCapacity capacity) (storeNames era) g facts memory decoded
  unfold BootWindow.mapBytes BootWindow.mapTimes storeCapacity storeNames at extracted
  ihave ⟨Hspan, Hrest⟩ := extracted $$ [Hb Ht]
  · iframe
  · unfold storeCapacity storeNames
    isimp only [Era.Record.tsoNames] at Hlength
    iframe

/-- Every other era client is framed, including metadata for the extracted keys. -/
theorem extract_clients (era : Era.Record) (g : State) (memory : Tso.AddressMap Byte) (diskBytes : Nat)
    (facts : BootFacts Xv6.Machine.bootImage g) (decoded : FiniteMap.decode memory = g.memory) :
    iprop(Era.bootClients capacity era memory g diskBytes ⊢
      rawSpan (storeCapacity capacity) (storeNames era) ∗
      remainder (storeCapacity capacity) (storeNames era) memory ∗
      Tso.Views.natLB capacity.views era.logLength 0 ∗ otherClients capacity era memory g diskBytes) := by
  unfold Era.bootClients
  iintro ⟨Hregs, Htso, Hmeta, Hdevices, Hdisk, Hresv⟩
  ihave ⟨Hspan, Hrest, Hlength⟩ := boot_resources capacity era g facts memory decoded $$ Htso
  unfold otherClients
  iframe

/-- Actual xv6 boot and actual native allocation. The exhaustive finite-map
witness is used symbolically; no 64-bit address enumeration is evaluated. -/
theorem allocate_boot (before : State) (template : Era.Record) (diskBytes : Nat) :
    let g := Xv6.Machine.boot before
    let memory := FiniteMap.encodeAll g.memory
    iprop(⊢ |==> ∃ era : Era.Record,
      ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ ∗
      Era.interp capacity era g ∗
      rawSpan (storeCapacity capacity) (storeNames era) ∗
      remainder (storeCapacity capacity) (storeNames era) memory ∗
      Tso.Views.natLB capacity.views era.logLength 0 ∗ otherClients capacity era memory g diskBytes) := by
  dsimp only
  let g := Xv6.Machine.boot before
  let memory := FiniteMap.encodeAll g.memory
  have facts := Xv6.Machine.boot_facts before
  have decoded : FiniteMap.decode memory = g.memory := FiniteMap.decode_encodeAll _
  imod Era.allocate capacity (Era.contracts capacity) Xv6.Machine.bootImage g memory template diskBytes
    facts decoded with ⟨%era, %same, Hinterp, Hclients⟩
  ihave ⟨Hspan, Hrest, Hlength, Hother⟩ := extract_clients capacity era g memory diskBytes facts decoded $$ Hclients
  imodintro
  iexists era
  iframe
  ipureintro; exact same

/-- One allocation also supplies persistent windows for any finite list of
contexts, while retaining the entire interpretation and every other client. -/
theorem allocate_shared_boot (before : State) (template : Era.Record) (diskBytes : Nat)
    (contexts : List TsoContext.CtxId) :
    let g := Xv6.Machine.boot before
    let memory := FiniteMap.encodeAll g.memory
    iprop(⊢ |==> ∃ era : Era.Record,
      ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ ∗
      Era.interp capacity era g ∗
      physicalSpan (storeCapacity capacity) (storeNames era) .discard ∗
      ([∗list] ξ ∈ contexts, fetchWindows (storeCapacity capacity) (storeNames era) ξ) ∗
      remainder (storeCapacity capacity) (storeNames era) memory ∗
      Tso.Views.natLB capacity.views era.logLength 0 ∗ otherClients capacity era memory g diskBytes) := by
  dsimp only
  imod allocate_boot capacity before template diskBytes with ⟨%era, %same, Hinterp, Hspan, Hrest, Hlength, Hother⟩
  imod share (storeCapacity capacity) (storeNames era) $$ Hspan with Hspan
  ihave ⟨Hspan, Hwindows⟩ := discarded_contexts (storeCapacity capacity) (storeNames era) contexts $$ Hspan
  imodintro
  iexists era
  iframe
  ipureintro; exact same

/-- Implementation link: all allocation and sharing contracts are discharged. -/
theorem nativeSpec : Spec capacity :=
  ⟨extract_clients capacity, allocate_boot capacity,
    fun era => fetch_access (storeCapacity capacity) (storeNames era),
    fun era => share (storeCapacity capacity) (storeNames era),
    fun era => discarded_windows (storeCapacity capacity) (storeNames era)⟩

end Xv6.Kernel.MycpuBootResources
