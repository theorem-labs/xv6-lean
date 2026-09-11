import MachCSL.Logic.UartWPSpec
import MachCSL.Logic.UartGhostProofs
import MachCSL.Logic.EraDevicesLink
import MachCSL.Logic.ObservationInvariantProofs
import MachCSL.Logic.RegisterWPProofs

namespace MachCSL.Logic.UartWP
open Iris Iris.Std Iris.BI Iris.ProgramLogic MachCSL.Machine
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (ghost : UartGhost.Capacity GF)

instance uartBody_timeless era names : Timeless (uartBody capacity ghost era names) := by
  unfold uartBody Device.uartFrag Device.uartAuth
  infer_instance
instance plicBody_timeless era : Timeless (plicBody capacity era) := by
  unfold plicBody Device.plicFrag Device.plicAuth
  infer_instance
instance uartInv_persistent N era names : Persistent (uartInv capacity ghost N era names) := by
  unfold uartInv
  infer_instance
instance plicInv_persistent N era : Persistent (plicInv capacity N era) := by
  unfold plicInv
  infer_instance
instance obsPermit_persistent N γ names : Persistent (obsPermit capacity ghost N γ names) := by
  unfold obsPermit
  infer_instance

theorem uart_allocate (N : Namespace) (E : CoPset) (era : Era.Record) (names : UartGhost.Names)
    (u : Devices.Uart.State) :
    iprop(⊢ Device.uartFrag capacity.era.devices era.uart u -∗ UartGhost.ghosts ghost names u
      ={E}=∗ uartInv capacity ghost N era names) := by
  iintro Hu Hg
  unfold uartInv
  iapply inv_alloc
  iintro !>
  unfold uartBody
  iexists u
  iframe

theorem plic_allocate (N : Namespace) (E : CoPset) (era : Era.Record) (p : Devices.Plic.State)
    (ok : Devices.Plic.PlicPlanOK p) :
    iprop(⊢ Device.plicFrag capacity.era.devices era.plic p ={E}=∗ plicInv capacity N era) := by
  iintro Hp
  unfold plicInv
  iapply inv_alloc
  iintro !>
  unfold plicBody
  iexists p
  iframe
  ipureintro
  exact ok

theorem trivial_permit (N Nobs : Namespace) (γ : GName) (names : UartGhost.Names)
    (mask : (↑Nobs : CoPset) ⊆ ⊤ \ ↑N) :
    iprop(⊢ ObservationInvariant.trivial capacity.power Nobs γ -∗ obsPermit capacity ghost N γ names) := by
  iintro #Hinv
  unfold obsPermit
  iintro !> %history %events %d %next _ _ _ Hg Ha
  imod ObservationInvariant.trivial_update capacity.power Nobs (⊤ \ ↑N) γ history (history ++ events) mask $$ Hinv Ha with Ha
  imodintro
  iframe

/-- All actual UART arms preserve the complete live power interpretation and
advance trace custody using the explicitly supplied source permit. -/
theorem uart_update [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole future : List Observation) (generation : Nat) (era : Era.Record)
    (Nuart Nplic : Namespace) (names : UartGhost.Names) (g : State)
    (events : List Observation) (next : Devices.State) (live : ThreadLive g generation)
    (action : UartStep g.devices events next) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      uartInv capacity ghost Nuart era names -∗ plicInv capacity Nplic era -∗
      obsPermit capacity ghost Nuart fixed.observations names -∗
      MachineInterp.powerInterp capacity fixed g -∗
      PowerGhost.obsInterp capacity.power fixed.observations whole g (events ++ future) ={⊤}=∗
      MachineInterp.powerInterp capacity fixed {g with devices := next} ∗
      PowerGhost.obsInterp capacity.power fixed.observations whole {g with devices := next} future) := by
  iintro #Hcert #HuInv #HpInv #Hpermit Hp Ho
  have step := Step.uartLive (image := image) generation g events next live action
  cases action with
  | tx byte next pop =>
    iunfold PowerGhost.obsInterp at Ho
    icases Ho with ⟨%history, %total, %wf, Ha⟩
    iunfold uartInv at HuInv
    iunfold inv at HuInv
    imod HuInv $$ %(⊤ : CoPset) [] with ⟨Hbody, Hclose⟩
    · ipureintro; exact fun _ _ => CoPset.mem_full
    · imod Hbody
      iunfold uartBody at Hbody
      icases Hbody with ⟨%u, Hu, Hg⟩
      ihave %same := MachineInterp.power_read_uart capacity fixed g generation era live u $$ Hp Hcert Hu
      subst u
      imod MachineInterp.power_write_uart capacity fixed g generation era live g.devices.uart next $$ Hp Hcert Hu with ⟨Hp, Hu⟩
      imod UartGhost.tx_step ghost names g.devices.uart next byte pop $$ Hg with Hg
      iunfold obsPermit at Hpermit
      imod Hpermit $$ %history %(if Devices.Uart.loopback g.devices.uart then [] else [.uartOut byte]) %g.devices %next [] [] [] Hg Ha with ⟨Hg, Ha⟩
      · ipureintro; exact .tx byte next pop
      · ipureintro; simpa [live.1] using wf.1
      · ipureintro; exact wf.2.2 live.1
      · imod Hclose $$ [Hu Hg] with _
        · iintro !>; unfold uartBody; iexists next; iframe
        · imodintro
          isimp only [EraDevices.withUart, EraDevices.withDevices] at Hp
          iframe Hp
          iapply PowerGhost.obs_interp_close capacity.power image _ _ g _ _ [] history future whole step wf total fixed.observations $$ Ha
  | rx byte next push =>
    iunfold PowerGhost.obsInterp at Ho
    icases Ho with ⟨%history, %total, %wf, Ha⟩
    iunfold uartInv at HuInv
    iunfold inv at HuInv
    imod HuInv $$ %(⊤ : CoPset) [] with ⟨Hbody, Hclose⟩
    · ipureintro; exact fun _ _ => CoPset.mem_full
    · imod Hbody
      iunfold uartBody at Hbody
      icases Hbody with ⟨%u, Hu, Hg⟩
      ihave %same := MachineInterp.power_read_uart capacity fixed g generation era live u $$ Hp Hcert Hu
      subst u
      imod MachineInterp.power_write_uart capacity fixed g generation era live g.devices.uart next $$ Hp Hcert Hu with ⟨Hp, Hu⟩
      ihave Hg := UartGhost.rx_step ghost names g.devices.uart next byte push $$ Hg
      iunfold obsPermit at Hpermit
      imod Hpermit $$ %history %([.uartIn byte]) %g.devices %next [] [] [] Hg Ha with ⟨Hg, Ha⟩
      · ipureintro; exact .rx byte next push
      · ipureintro; simpa [live.1] using wf.1
      · ipureintro; exact wf.2.2 live.1
      · imod Hclose $$ [Hu Hg] with _
        · iintro !>; unfold uartBody; iexists next; iframe
        · imodintro
          isimp only [EraDevices.withUart, EraDevices.withDevices] at Hp
          iframe Hp
          iapply PowerGhost.obs_interp_close capacity.power image _ _ g _ _ [] history future whole step wf total fixed.observations $$ Ha
  | latch next level latched =>
    iunfold plicInv at HpInv
    iunfold inv at HpInv
    imod HpInv $$ %(⊤ : CoPset) [] with ⟨Hbody, Hclose⟩
    · ipureintro; exact fun _ _ => CoPset.mem_full
    · imod Hbody
      iunfold plicBody at Hbody
      icases Hbody with ⟨%p, Hplic, %ok⟩
      ihave %same := MachineInterp.power_read_plic capacity fixed g generation era live p $$ Hp Hcert Hplic
      subst p
      imod MachineInterp.power_write_plic capacity fixed g generation era live g.devices.plic next $$ Hp Hcert Hplic with ⟨Hp, Hplic⟩
      imod Hclose $$ [Hplic] with _
      · iintro !>; unfold plicBody; iexists next; iframe
        ipureintro; exact Devices.Plic.latch_plan _ _ _ latched ok
      · imodintro
        isimp only [EraDevices.withPlic, EraDevices.withDevices] at Hp
        iframe Hp
        isimp only [List.nil_append] at Ho
        iapply PowerGhost.obs_interp_silent capacity.power image _ _ g _ [] step fixed.observations whole future $$ Ho
  | idle =>
    imodintro
    isimp only [List.nil_append] at Ho
    iframe Hp
    iapply PowerGhost.obs_interp_silent capacity.power image _ _ g _ [] step fixed.observations whole future $$ Ho

/-- Only the source UART actor has this total idle alternative. -/
theorem uart_reducible [Platform] (image : BootImage) (generation : Nat) (g : State) :
    Step image (.uart generation) g [] (.uart generation) g [] := by
  by_cases live : ThreadLive g generation
  · exact Step.uartLive _ _ _ _ live .idle
  · exact Step.uartDead _ _ live

/-- Source `wp_uart_loop`, with all UART ghost resources and PLIC plan held in
native invariants. The permit is the explicit client trace protocol. -/
theorem wp_uart_loop [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (Nuart Nplic : Namespace)
    (names : UartGhost.Names) (post : Empty → IProp GF) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      uartInv capacity ghost Nuart era names -∗ plicInv capacity Nplic era -∗
      obsPermit capacity ghost Nuart fixed.observations names -∗
      DeadThread.threadWP capacity image fixed whole (.uart generation) post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  unfold DeadThread.threadWP
  iintro #Hcert #Hu #Hplic #Hpermit
  iloeb as IH
  iapply wp_lift_step (s := .NotStuck) (E := ⊤) (Φ := post) (by rfl)
  iintro %g %ns %events %future %nt Hstate
  dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS]
  iunfold MachineInterp.stateInterp at Hstate
  icases Hstate with ⟨Hp, Ho⟩
  iapply fupd_mask_intro (E2 := ∅) (by intro x hx; exact CoPset.mem_full)
  iintro Hback
  isplit
  · ipureintro
    exact ⟨[], .uart generation, g, [], uart_reducible image generation g⟩
  · iintro !> %e' %g' %forks %step _
    change Step image (.uart generation) g events e' g' forks at step
    imod Hback
    cases step with
    | uartDead _ _ dead =>
      imodintro
      simp only [List.nil_append, List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · iexact IH
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial
    | uartLive _ _ events next live action =>
      imod uart_update capacity ghost image fixed whole future generation era Nuart Nplic names g events next live action
        $$ Hcert Hu Hplic Hpermit Hp Ho with ⟨Hp, Ho⟩
      imodintro
      simp only [List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · iexact IH
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial

theorem wp_uart_loop_trivial [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (Nuart Nplic Nobs : Namespace)
    (names : UartGhost.Names) (post : Empty → IProp GF)
    (mask : (↑Nobs : CoPset) ⊆ ⊤ \ ↑Nuart) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      uartInv capacity ghost Nuart era names -∗ plicInv capacity Nplic era -∗
      ObservationInvariant.trivial capacity.power Nobs fixed.observations -∗
      DeadThread.threadWP capacity image fixed whole (.uart generation) post) := by
  iintro Hcert Hu Hp Hobs
  ihave Hpermit := trivial_permit capacity ghost Nuart Nobs fixed.observations names mask $$ Hobs
  iapply wp_uart_loop capacity ghost image fixed whole generation era Nuart Nplic names post $$ Hcert Hu Hp Hpermit

theorem ledger_callback (Nuart Nobs : Namespace) (names : UartGhost.Names)
    (R : List Observation → IProp GF)
    (tx : iprop(⊢ txLedgerLaw ghost Nuart Nobs names R))
    (rx : iprop(⊢ rxLedgerLaw ghost Nuart Nobs names R))
    (history events : List Observation) (d next : Devices.State)
    (action : UartStep d events next) (shape : TraceShape history true)
    (wire : outputBytes (openSegment history) = d.uart.wire) :
    iprop(⊢ R history -∗ UartGhost.ghosts ghost names next.uart
      ={(⊤ \ ↑Nuart) \ ↑Nobs}=∗ R (history ++ events) ∗ UartGhost.ghosts ghost names next.uart) := by
  iintro HR Hg
  cases action with
  | tx byte next pop =>
    cases loop : Devices.Uart.loopback d.uart with
    | false =>
      ihave Htx := tx
      iunfold txLedgerLaw at Htx
      imod Htx $$ %history %byte %d.uart %next [] [] [] [] Hg HR with ⟨Hg, HR⟩
      · ipureintro; exact pop
      · ipureintro; exact loop
      · ipureintro; exact shape
      · ipureintro; exact wire
      · imodintro; simp only [Bool.false_eq_true, ↓reduceIte]; iframe
    | true =>
      imodintro
      simp only [↓reduceIte, List.append_nil]
      iframe
  | rx byte next push =>
    ihave Hrx := rx
    iunfold rxLedgerLaw at Hrx
    imod Hrx $$ %history %byte %d.uart %next [] [] Hg HR with ⟨Hg, HR⟩
    · ipureintro; exact push
    · ipureintro; exact shape
    · imodintro; iframe
  | latch next level latched =>
    imodintro; simp only [List.append_nil]; iframe
  | idle =>
    imodintro; simp only [List.append_nil]; iframe

theorem ledger_permit (Nuart Nobs : Namespace) (γ : GName) (names : UartGhost.Names)
    (R : List Observation → IProp GF) (timeless : ∀ history, Timeless (R history))
    (mask : (↑Nobs : CoPset) ⊆ ⊤ \ ↑Nuart)
    (tx : iprop(⊢ txLedgerLaw ghost Nuart Nobs names R))
    (rx : iprop(⊢ rxLedgerLaw ghost Nuart Nobs names R)) :
    iprop(⊢ ObservationInvariant.ledger capacity.power Nobs γ R -∗
      obsPermit capacity ghost Nuart γ names) := by
  iintro #Hinv
  unfold obsPermit
  iintro !> %history %events %d %next %action %shape %wire Hg Ha
  imod ObservationInvariant.update capacity.power Nobs (⊤ \ ↑Nuart) γ R timeless mask history (history ++ events)
    (UartGhost.ghosts ghost names next)
    (ledger_callback ghost Nuart Nobs names R tx rx history events d {d with uart := next} action shape wire)
    $$ Hinv Ha Hg with ⟨Ha, Hg⟩
  imodintro
  iframe

theorem uart_initial_allocate (N : Namespace) (E : CoPset) (era : Era.Record) (u : Devices.Uart.State) :
    iprop(⊢ Device.uartFrag capacity.era.devices era.uart u ={E}=∗ ∃ names,
      uartInv capacity ghost N era names ∗ UartGhost.initialClients ghost names u) := by
  iintro Hu
  imod UartGhost.allocate ghost u with ⟨%names, Hg, Hclients⟩
  imod uart_allocate capacity ghost N E era names u $$ Hu Hg with Hinv
  imodintro
  iexists names
  iframe

theorem wp_uart_loop_ledger [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (Nuart Nplic Nobs : Namespace)
    (names : UartGhost.Names) (post : Empty → IProp GF)
    (R : List Observation → IProp GF) (timeless : ∀ history, Timeless (R history))
    (mask : (↑Nobs : CoPset) ⊆ ⊤ \ ↑Nuart)
    (tx : iprop(⊢ txLedgerLaw ghost Nuart Nobs names R))
    (rx : iprop(⊢ rxLedgerLaw ghost Nuart Nobs names R)) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      uartInv capacity ghost Nuart era names -∗ plicInv capacity Nplic era -∗
      ObservationInvariant.ledger capacity.power Nobs fixed.observations R -∗
      DeadThread.threadWP capacity image fixed whole (.uart generation) post) := by
  iintro Hcert Hu Hp Hobs
  ihave Hpermit := ledger_permit capacity ghost Nuart Nobs fixed.observations names R timeless mask tx rx $$ Hobs
  iapply wp_uart_loop capacity ghost image fixed whole generation era Nuart Nplic names post $$ Hcert Hu Hp Hpermit

theorem uartWPSpec [Platform] : UartWPSpec capacity ghost :=
  ⟨uart_allocate capacity ghost, uart_initial_allocate capacity ghost, plic_allocate capacity,
    trivial_permit capacity ghost, ledger_permit capacity ghost, wp_uart_loop capacity ghost,
    wp_uart_loop_trivial capacity ghost, wp_uart_loop_ledger capacity ghost⟩

end MachCSL.Logic.UartWP
