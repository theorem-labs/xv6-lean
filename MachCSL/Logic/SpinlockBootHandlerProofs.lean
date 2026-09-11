import MachCSL.Logic.JalBootHandlerProofs
import MachCSL.Logic.SpinlockInitProofs
import MachCSL.Logic.SpinlockWPProofs

namespace MachCSL.Logic.SpinlockBootHandler
open Iris Iris.Std Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem harts_wp (lockCapacity : Lock.Capacity GF) (N : Namespace) (γ : GName)
    (fixed : MachineInterp.FixedNames) (whole : List Observation) (era : Era.Record)
    (g : State) (facts : BootFacts SpinlockImage.image g) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed g.generation era -∗
      (∀ cpu, SpinlockProtocol.resource ⟨capacity, lockCapacity⟩ fixed g.generation era N γ cpu .idle) -∗
      JalBootResources.cpuRegisters capacity.era.registers era.registers g.registers -∗
      SpinlockCode.shared capacity era -∗
      JalBootResources.cpuReservations capacity.era.reservations era.reservations g.reservations -∗
      [∗list] thread ∈ List.ofFn (fun cpu : CPU => loop g.generation cpu),
        DeadThread.threadWP capacity SpinlockImage.image fixed whole thread (fun _ => iprop(True))) := by
  iintro #Hcert #Hidle Hregs Hcode Hresv
  iunfold JalBootResources.cpuRegisters at Hregs
  iunfold SpinlockCode.shared at Hcode
  iunfold JalBootResources.cpuReservations at Hresv
  ihave Hpair := (BigSepS.bigSepS_sep
    (Φ := fun _ : CPU => SpinlockCode.allCode capacity era (.own JalBootResources.codeShare))
    (Ψ := fun cpu => Reservations.resvFrag capacity.era.reservations era.reservations cpu (g.reservations cpu))).2 $$ [Hcode Hresv]
  · iframe
  · ihave Hall := (BigSepS.bigSepS_sep
      (Φ := fun cpu => EventWP.ownedCells capacity.era.registers (era.registers cpu) (g.registers cpu))
      (Ψ := fun cpu => iprop(SpinlockCode.allCode capacity era (.own JalBootResources.codeShare) ∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu (g.reservations cpu)))).2 $$ [Hregs Hpair]
    · iframe
    · have mapped : List.ofFn (fun cpu : CPU => loop g.generation cpu) =
          (List.finRange 8).map (loop g.generation) := by simp [List.finRange]
      rw [mapped, BigSepL.bigSepL_map]
      iapply JalBootHandler.cpu_to_list
      iapply BigSepS.bigSepS_impl $$ Hall
      iintro !> %cpu %_ ⟨Hregs, Hcode, Hresv⟩
      unfold loop
      ihave Hphase := Hidle $$ %cpu
      iapply SpinlockWP.loop ⟨capacity, lockCapacity⟩ fixed whole g.generation era N γ cpu
        ⟨0, by decide⟩ (g.registers cpu) .idle
        (.own JalBootResources.codeShare) (fun _ => iprop(True)) (SpinlockFamily.boot g facts cpu)
        $$ Hcert Hregs Hcode [Hresv] Hphase
      unfold Reservations.resvAny
      iexists (g.reservations cpu)
      iexact Hresv

theorem boot_handler (ghost : UartGhost.Capacity GF) (ns : JalBootHandler.Namespaces)
    (lockCapacity : Lock.Capacity GF) (N : Namespace)
    (uart : UartWP.UartWPSpec capacity ghost) (plic : PlicWP.PlicWPSpec capacity)
    (disk : ResetDiskWP.ResetDiskWPSpec capacity)
    (fixed : MachineInterp.FixedNames) (whole : List Observation) (template : Era.Record) :
    iprop(⊢ ObservationInvariant.trivial capacity.power ns.observations fixed.observations -∗
      PowerWP.bootHandler capacity SpinlockImage.image fixed whole template) := by
  letI : Persistent (ObservationInvariant.trivial capacity.power ns.observations fixed.observations) := by
    unfold ObservationInvariant.trivial ObservationInvariant.ledger
    infer_instance
  letI : ∀ names N, Persistent (PlicWP.wireInv capacity.era.registers N names) := fun names N => by
    unfold PlicWP.wireInv
    infer_instance
  letI : ∀ N era names, Persistent (UartWP.uartInv capacity ghost N era names) := fun N era names => by
    unfold UartWP.uartInv
    infer_instance
  letI : ∀ N era, Persistent (UartWP.plicInv capacity N era) := fun N era => by
    unfold UartWP.plicInv
    infer_instance
  iintro #Hobs
  unfold PowerWP.bootHandler
  iintro !> %g %era %memory %facts %decoded %_eraeq #Hcert Hclients
  iunfold Era.bootClients at Hclients
  icases Hclients with ⟨Hregs, Hmemory, Hmeta, Hdev, Hdisk, Hresv⟩
  ihave ⟨Hregs, Hwires⟩ := JalBootResources.registers_split capacity.era.registers era.registers g.registers $$ Hregs
  imod SpinlockInit.allocate ⟨capacity, lockCapacity⟩ fixed g.generation era N g facts memory decoded
    $$ [Hcert Hmemory] with ⟨%γ, #Hlock, #Hidle, Hcode, Hrest, Hlength⟩
  · iframe Hcert Hmemory
  ihave Hresv := (JalBootResources.reservations_split capacity.era.reservations era.reservations g.reservations).1 $$ Hresv
  imod plic.allocate era.registers ns.wires ⊤ _ _ $$ Hwires with #Hwires
  iunfold Device.fragments at Hdev
  icases Hdev with ⟨Huart, Hplic, Hvirtio⟩
  simp only [Era.Record.deviceNames] at *
  imod uart.initialAllocate ns.uart ⊤ era g.devices.uart $$ Huart with ⟨%names, #Huart, Hinitial⟩
  have plic_ok : Devices.Plic.PlicPlanOK g.devices.plic := by
    rw [facts.2.2.2.2.1]
    exact Devices.Plic.initial_plan
  imod uart.plicAllocate ns.plic ⊤ era g.devices.plic plic_ok $$ Hplic with #Hplic
  obtain ⟨previous, reset⟩ := facts.2.2.2.2.2.1
  ihave Hharts := harts_wp capacity lockCapacity N γ fixed whole era g facts $$ Hcert Hidle Hregs Hcode Hresv
  ihave Huartwp := uart.trivialLoop SpinlockImage.image fixed whole g.generation era ns.uart ns.plic ns.observations
    names (fun _ => iprop(True)) ns.uart_observations $$ Hcert Huart Hplic Hobs
  ihave Hplicwp := plic.loop SpinlockImage.image fixed whole g.generation era ns.wires (fun _ => iprop(True)) $$ Hcert Hwires
  isimp only [reset] at Hvirtio
  ihave Hdiskwp := disk.resetDisk SpinlockImage.image fixed whole g.generation era previous (fun _ => iprop(True)) $$ Hcert Hvirtio
  imodintro
  unfold powerFork
  iapply BigSepL.bigSepL_append.mpr
  isplitl [Hharts]
  · iexact Hharts
  · iframe Huartwp Hdiskwp Hplicwp
    iapply BigSepL.bigSepL_nil.mpr
    itrivial

end MachCSL.Logic.SpinlockBootHandler
