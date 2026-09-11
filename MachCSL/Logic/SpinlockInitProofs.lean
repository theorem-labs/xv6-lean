import MachCSL.Logic.SpinlockBootResourcesLink
import MachCSL.Logic.SpinlockCodeProofs
import MachCSL.Logic.SpinlockProtocolLink

namespace MachCSL.Logic.SpinlockInit
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : SpinlockProtocol.Capacity GF)

omit [Platform] in
/-- Connect the actual boot ledger to the native lock invariant and all eight
code shares. Every unselected full cell and the original log receipt survives. -/
theorem allocate (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (N : Namespace) (g : State) (boot : BootFacts SpinlockImage.image g)
    (memory : Tso.AddressMap Memory.Byte) (decoded : Memory.FiniteMap.decode memory = g.memory) :
    iprop(MachineInterp.generationCertificate capacity.machine fixed gen era ∗
      Tso.Interp.bootClients capacity.machine.era.tso era.tsoNames memory ⊢
      |={⊤}=> ∃ γ,
        SpinlockProtocol.isLock capacity N era γ ∗
        (∀ cpu, SpinlockProtocol.resource capacity fixed gen era N γ cpu .idle) ∗
        SpinlockCode.shared capacity.machine era ∗
        SpinlockBootResources.remainder (SpinlockBootResources.storeCapacity capacity.machine.era)
          (SpinlockBootResources.storeNames era) memory ∗
        Tso.Views.natLB capacity.machine.era.views era.logLength 0) := by
  iintro ⟨Hcert, Hclients⟩
  ihave ⟨Hwindows, Hrest, Hlength⟩ := SpinlockBootResources.boot_resources
    capacity.machine.era era g boot memory decoded $$ Hclients
  iunfold SpinlockBootResources.windows at Hwindows
  icases Hwindows with ⟨Hcode, Hlock, Hcounter⟩
  isimp only [SpinlockBootResources.storeCapacity, SpinlockBootResources.storeNames] at Hcode Hlock Hcounter
  have code := SpinlockCode.mint_shared capacity.machine era
  unfold MemoryWriteWP.storeCapacity MemoryWriteWP.storeNames at code
  imod code $$ Hcode with Hcode
  have data := SpinlockProtocol.allocate (hlc := hlc) capacity fixed gen era N
  unfold SpinlockProtocol.wordAt SpinlockProtocol.storeCapacity SpinlockProtocol.storeNames
    MemoryWriteWP.storeCapacity MemoryWriteWP.storeNames at data
  iunfold SpinlockBootResources.lockWindow at Hlock
  iunfold SpinlockBootResources.counterWindow at Hcounter
  imod data $$ Hcert Hlock Hcounter with ⟨%γ, Hinv, Hidle⟩
  imodintro
  iexists γ
  iframe

end MachCSL.Logic.SpinlockInit
