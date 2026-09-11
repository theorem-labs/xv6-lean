import MachCSL.Logic.PlicWPSpec
import MachCSL.Logic.EraStateLink
import Iris.ProgramLogic.Lifting

namespace MachCSL.Logic.PlicWP
open Iris Iris.Std Iris.BI Iris.ProgramLogic MachCSL.Machine
open Iris.Std.LawfulSet
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

instance wireBody_timeless names : Timeless (wireBody capacity.era.registers names) := by
  letI := capacity.era.registers.registers
  unfold wireBody wireCells Registers.regPointsto
  infer_instance
instance wireInv_persistent N names : Persistent (wireInv capacity.era.registers N names) := by
  unfold wireInv
  infer_instance

theorem wire_allocate (names : GlobalRegisters.Names) (N : Namespace) (E : CoPset)
    (seip meip : CPU → BitVec 1) :
    iprop(⊢ wireCells capacity.era.registers names seip meip ={E}=∗ wireInv capacity.era.registers N names) := by
  iintro H
  unfold wireInv
  iapply inv_alloc
  iintro !>
  unfold wireBody
  iexists seip, meip
  iexact H

/-- Extract one pair of pin cells and restore the exact remaining seven pairs. -/
theorem wire_access (names : GlobalRegisters.Names) (seip meip : CPU → BitVec 1) (cpu : CPU) :
    iprop(⊢ wireCells capacity.era.registers names seip meip -∗
      Registers.regPointsto capacity.era.registers (names cpu) .sig_seip (.own 1) (seip cpu) ∗
      Registers.regPointsto capacity.era.registers (names cpu) .sig_meip (.own 1) (meip cpu) ∗
      (∀ (s m : BitVec 1),
        Registers.regPointsto capacity.era.registers (names cpu) .sig_seip (.own 1) s -∗
        Registers.regPointsto capacity.era.registers (names cpu) .sig_meip (.own 1) m -∗
        wireCells capacity.era.registers names (updateHart seip cpu s) (updateHart meip cpu m))) := by
  unfold wireCells
  iintro H
  icases (BigSepS.bigSepS_delete (GlobalRegisters.mem_allCPUs cpu)).1 $$ H with ⟨⟨Hs, Hm⟩, Hrest⟩
  iframe Hs Hm
  iintro %s %m Hs Hm
  iapply (BigSepS.bigSepS_delete (GlobalRegisters.mem_allCPUs cpu)).2
  have hs : updateHart seip cpu s cpu = s := by simp [updateHart]
  have hm : updateHart meip cpu m cpu = m := by simp [updateHart]
  rw [hs, hm]
  iframe Hs Hm
  iapply BigSepS.bigSepS_mono $$ Hrest
  intro other member
  have ne : other ≠ cpu := by
    intro eq
    exact (mem_diff.mp member).2 (mem_singleton.mpr eq)
  simp only [updateHart, if_neg ne]
  exact .rfl

theorem plic_update (fixed : MachineInterp.FixedNames) (generation : Nat) (era : Era.Record)
    (N : Namespace) (g : State) (files : CPU → RegisterFile) (live : ThreadLive g generation)
    (action : PlicStep g.devices g.registers files) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      wireInv capacity.era.registers N era.registers -∗
      MachineInterp.powerInterp capacity fixed g ={⊤}=∗
      MachineInterp.powerInterp capacity fixed {g with registers := files}) := by
  iintro #Hcert #Hinv Hp
  iunfold wireInv at Hinv
  iunfold inv at Hinv
  imod Hinv $$ %(⊤ : CoPset) [] with ⟨Hbody, Hclose⟩
  · ipureintro; exact fun _ _ => CoPset.mem_full
  · imod Hbody
    iunfold wireBody at Hbody
    icases Hbody with ⟨%seip, %meip, Hw⟩
    cases action with
    | supervisor cpu =>
      ihave ⟨Hs, Hm, Hrest⟩ := wire_access capacity era.registers seip meip cpu $$ Hw
      imod MachineInterp.power_write_register capacity fixed g generation era live cpu .sig_seip
        (seip cpu) (boolBit (Devices.seip g.devices cpu.val)) $$ Hp Hcert Hs with ⟨Hp, Hs⟩
      ihave Hw := Hrest $$ %(boolBit (Devices.seip g.devices cpu.val)) %(meip cpu) Hs Hm
      imod Hclose $$ [Hw] with _
      · iintro !>; unfold wireBody; iexists _, _; iexact Hw
      · imodintro
        isimp only [EraState.writeRegister, EraState.withRegisters] at Hp
        iexact Hp
    | machine cpu =>
      ihave ⟨Hs, Hm, Hrest⟩ := wire_access capacity era.registers seip meip cpu $$ Hw
      imod MachineInterp.power_write_register capacity fixed g generation era live cpu .sig_meip
        (meip cpu) (boolBit (Devices.meip g.devices cpu.val)) $$ Hp Hcert Hm with ⟨Hp, Hm⟩
      ihave Hw := Hrest $$ %(seip cpu) %(boolBit (Devices.meip g.devices cpu.val)) Hs Hm
      imod Hclose $$ [Hw] with _
      · iintro !>; unfold wireBody; iexists _, _; iexact Hw
      · imodintro
        isimp only [EraState.writeRegister, EraState.withRegisters] at Hp
        iexact Hp

/-- Reducibility uses an actual supervisor-pin write on hart zero when live. -/
theorem plic_reducible [Platform] (image : BootImage) (generation : Nat) (g : State) :
    ∃ next, Step image (.plic generation) g [] (.plic generation) next [] := by
  by_cases live : ThreadLive g generation
  · exact ⟨_, Step.plicLive _ _ _ live (.supervisor 0)⟩
  · exact ⟨g, Step.plicDead _ _ live⟩

/-- Every PLIC successor is safe, with both pin cells borrowed from the wire
invariant after the actual arm is known. No PLIC invariant opening is needed. -/
theorem wp_plic_loop [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (generation : Nat) (era : Era.Record) (N : Namespace)
    (post : Empty → IProp GF) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      wireInv capacity.era.registers N era.registers -∗
      DeadThread.threadWP capacity image fixed whole (.plic generation) post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  unfold DeadThread.threadWP
  iintro #Hcert #Hw
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
    obtain ⟨next, step⟩ := plic_reducible image generation g
    exact ⟨[], .plic generation, next, [], step⟩
  · iintro !> %e' %g' %forks %step _
    change Step image (.plic generation) g events e' g' forks at step
    imod Hback
    cases step with
    | plicDead _ _ dead =>
      imodintro
      simp only [List.nil_append, List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · iexact IH
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial
    | plicLive _ _ files live action =>
      have actual := Step.plicLive (image := image) generation g files live action
      imod plic_update capacity fixed generation era N g files live action $$ Hcert Hw Hp with Hp
      isimp only [List.nil_append] at Ho
      ihave Ho := PowerGhost.obs_interp_silent capacity.power image _ _ g _ [] actual fixed.observations whole future $$ Ho
      imodintro
      simp only [List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · iexact IH
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial

/-- Source's uniform device-loop interface retains its unused PLIC invariant. -/
theorem wp_plic_loop_source [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (generation : Nat) (era : Era.Record) (N Nplic : Namespace)
    (post : Empty → IProp GF) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      UartWP.plicInv capacity Nplic era -∗ wireInv capacity.era.registers N era.registers -∗
      DeadThread.threadWP capacity image fixed whole (.plic generation) post) := by
  iintro Hcert _ Hw
  iapply wp_plic_loop capacity image fixed whole generation era N post $$ Hcert Hw

theorem plicWPSpec [Platform] : PlicWPSpec capacity :=
  ⟨wire_allocate capacity, wp_plic_loop capacity⟩

end MachCSL.Logic.PlicWP
