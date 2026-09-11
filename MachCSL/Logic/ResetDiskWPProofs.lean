import MachCSL.Logic.ResetDiskWPSpec
import MachCSL.Logic.StateInterpProofs
import MachCSL.Logic.DeviceProofs
import MachCSL.Logic.DeadThreadProofs
import MachCSL.Machine.JalDevicesProofs

namespace MachCSL.Logic.ResetDiskWP
open Iris Iris.Std Iris.BI Iris.ProgramLogic MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

theorem reset_or_dead (fixed : MachineInterp.FixedNames) (generation : Nat)
    (era : Era.Record) (g : State) (previous : Devices.Virtio.State) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed generation era -∗
      Device.virtioFrag capacity.era.devices era.virtio (Devices.Virtio.virtio_reset previous) -∗
      ⌜¬ ThreadLive g generation ∨ JalDevices.DiskReset g.devices⌝) := by
  iintro Hp Hcert Hv
  ihave %cases := MachineInterp.generation_cases capacity fixed g generation era $$ Hp Hcert
  rcases cases with older | live
  · ipureintro
    left
    intro live
    have := live.2
    omega
  · ihave ⟨Hera, _⟩ := MachineInterp.live_era_access capacity fixed g generation era live $$ Hp Hcert
    iunfold Era.interp at Hera
    icases Hera with ⟨_, _, Hd, _⟩
    iunfold Device.interp at Hd
    iunfold Era.Record.deviceNames at Hd
    icases Hd with ⟨_, _, Ha⟩
    ihave %same := Device.virtio_agree capacity.era.devices era.virtio g.devices.virtio
      (Devices.Virtio.virtio_reset previous) $$ Ha Hv
    ipureintro
    exact Or.inr ⟨previous, same.symm⟩

theorem disk_reducible [Platform] (image : BootImage) (generation : Nat) (g : State) :
    Step image (.disk generation) g [] (.disk generation) g [] := by
  by_cases live : ThreadLive g generation
  · have step := Step.diskLive (image := image) generation g g.devices Memory.empty g.log live (.idle)
      (Or.inl ⟨rfl, rfl⟩) (fun _ _ => rfl)
    simpa using step
  · exact .diskDead _ _ live

theorem wp_reset_disk [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (previous : Devices.Virtio.State) (post : Empty → IProp GF) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      Device.virtioFrag capacity.era.devices era.virtio (Devices.Virtio.virtio_reset previous) -∗
      DeadThread.threadWP capacity image fixed whole (.disk generation) post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  unfold DeadThread.threadWP
  iintro #Hcert
  iloeb as IH
  iintro Hv
  iapply wp_lift_step (s := .NotStuck) (E := ⊤) (Φ := post) (by rfl)
  iintro %g %ns %events %future %nt Hstate
  dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS]
  iunfold MachineInterp.stateInterp at Hstate
  ihave ⟨Hp, Ho⟩ := Hstate
  ihave %safe := reset_or_dead capacity fixed generation era g previous $$ Hp Hcert Hv
  iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
  iintro Hback
  isplit
  · ipureintro
    exact ⟨[], _, g, [], disk_reducible image generation g⟩
  · iintro !> %e' %g' %forks %step _
    have unchanged : e' = .disk generation ∧ g' = g ∧ forks = [] ∧ events = [] := by
      rcases safe with dead | reset
      · exact DeadThread.dead_step_unique image _ generation g rfl dead events e' g' forks step
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := JalDevices.disk_thread_idle image generation g events e' g' forks reset step
        exact ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := unchanged
    imod Hback
    imodintro
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
    iframe Hp Ho
    isplit
    · iapply IH $$ Hv
    · iapply BigSepL.bigSepL_nil.mpr
      itrivial

theorem resetDiskWPSpec [Platform] {hlc : HasLC} [InvGS_gen hlc GF] : ResetDiskWPSpec capacity :=
  ⟨wp_reset_disk capacity⟩

end MachCSL.Logic.ResetDiskWP
