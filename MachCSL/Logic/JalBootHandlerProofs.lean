import MachCSL.Logic.JalBootHandlerDefs
import MachCSL.Logic.JalBootResourcesLink

namespace MachCSL.Logic.JalBootHandler
open Iris Iris.Std Iris.BI MachCSL.Machine

variable {GF : BundledGFunctors}

theorem cpu_to_list (Φ : CPU → IProp GF) :
    iprop(([∗set] cpu ∈ GlobalRegisters.allCPUs, Φ cpu) ⊢ [∗list] cpu ∈ List.finRange 8, Φ cpu) := by
  have same : (Iris.Std.LawfulSet.ofList (List.finRange 8) : GlobalRegisters.CPUSet) = GlobalRegisters.allCPUs := by
    apply _root_.Std.ExtTreeSet.ext_mem
    intro cpu
    constructor
    · intro _; exact GlobalRegisters.mem_allCPUs cpu
    · intro _; exact Iris.Std.LawfulSet.mem_ofList.mp (List.mem_finRange cpu)
  rw [← same]
  exact (BigSepS.bigSepS_of_list (List.nodup_finRange 8)).1

variable [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem harts_wp (harts : EventWPJal.UniversalJalWPSpec capacity)
    (fixed : MachineInterp.FixedNames) (whole : List Observation) (era : Era.Record)
    (g : State) (facts : BootFacts jalImage g) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed g.generation era -∗
      JalBootResources.cpuRegisters capacity.era.registers era.registers g.registers -∗
      JalBootResources.sharedCode capacity era -∗
      JalBootResources.cpuReservations capacity.era.reservations era.reservations g.reservations -∗
      [∗list] thread ∈ List.ofFn (fun cpu : CPU => loop g.generation cpu),
        DeadThread.threadWP capacity jalImage fixed whole thread (fun _ => iprop(True))) := by
  iintro #Hcert Hregs Hcode Hresv
  iunfold JalBootResources.cpuRegisters at Hregs
  iunfold JalBootResources.sharedCode at Hcode
  iunfold JalBootResources.cpuReservations at Hresv
  ihave Hpair := (BigSepS.bigSepS_sep
    (Φ := fun _ : CPU => EventWP.codeResources capacity era (.own JalBootResources.codeShare))
    (Ψ := fun cpu => Reservations.resvFrag capacity.era.reservations era.reservations cpu (g.reservations cpu))).2 $$ [Hcode Hresv]
  · iframe
  · ihave Hall := (BigSepS.bigSepS_sep
      (Φ := fun cpu => EventWP.ownedCells capacity.era.registers (era.registers cpu) (g.registers cpu))
      (Ψ := fun cpu => iprop(EventWP.codeResources capacity era (.own JalBootResources.codeShare) ∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu (g.reservations cpu)))).2 $$ [Hregs Hpair]
    · iframe
    · have mapped : List.ofFn (fun cpu : CPU => loop g.generation cpu) =
          (List.finRange 8).map (loop g.generation) := by simp [List.finRange]
      rw [mapped, BigSepL.bigSepL_map]
      iapply cpu_to_list
      iapply BigSepS.bigSepS_impl $$ Hall
      iintro !> %cpu %_ ⟨Hregs, Hcode, Hresv⟩
      unfold loop
      iapply harts.loop jalImage fixed whole g.generation era cpu (g.registers cpu)
        (.own JalBootResources.codeShare) (fun _ => iprop(True)) (JalLoopPlan.bootFacts_family g facts cpu)
        $$ Hcert Hregs Hcode [Hresv]
      unfold Reservations.resvAny
      iexists (g.reservations cpu)
      iexact Hresv

theorem boot_handler (ghost : UartGhost.Capacity GF) (ns : Namespaces)
    (harts : EventWPJal.UniversalJalWPSpec capacity)
    (uart : UartWP.UartWPSpec capacity ghost) (plic : PlicWP.PlicWPSpec capacity)
    (disk : ResetDiskWP.ResetDiskWPSpec capacity)
    (fixed : MachineInterp.FixedNames) (whole : List Observation) (template : Era.Record) :
    iprop(⊢ ObservationInvariant.trivial capacity.power ns.observations fixed.observations -∗
      PowerWP.bootHandler capacity jalImage fixed whole template) := by
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
  imod JalBootResources.boot_code capacity era memory
    (JalBootResources.boot_code_lookup g facts memory decoded) $$ Hmemory with ⟨Hcode, Hbytes, Htime, Hlength⟩
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
  ihave Hharts := harts_wp capacity harts fixed whole era g facts $$ Hcert Hregs Hcode Hresv
  ihave Huartwp := uart.trivialLoop jalImage fixed whole g.generation era ns.uart ns.plic ns.observations
    names (fun _ => iprop(True)) ns.uart_observations $$ Hcert Huart Hplic Hobs
  ihave Hplicwp := plic.loop jalImage fixed whole g.generation era ns.wires (fun _ => iprop(True)) $$ Hcert Hwires
  isimp only [reset] at Hvirtio
  ihave Hdiskwp := disk.resetDisk jalImage fixed whole g.generation era previous (fun _ => iprop(True)) $$ Hcert Hvirtio
  imodintro
  unfold powerFork
  iapply BigSepL.bigSepL_append.mpr
  isplitl [Hharts]
  · iexact Hharts
  · iframe Huartwp Hdiskwp Hplicwp
    iapply BigSepL.bigSepL_nil.mpr
    itrivial

end MachCSL.Logic.JalBootHandler
