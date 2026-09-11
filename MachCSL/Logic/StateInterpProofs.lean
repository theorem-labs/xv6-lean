import MachCSL.Logic.StateInterpSpec
import MachCSL.Logic.PowerGhostProofs
import MachCSL.Logic.EraRegistryProofs

namespace MachCSL.Logic.MachineInterp
open Iris Iris.Std Iris.BI MachCSL.Machine

theorem registryDomain_empty : RegistryDomain ∅ 0 := by
  intro generation
  simp

theorem registryDomain_fresh (entries : Era.RegistryMap Era.Record) (count : Nat)
    (domain : RegistryDomain entries count) : entries[count]? = none := by
  have absent : ¬ entries[count]?.isSome := by simpa using domain count
  cases h : entries[count]? with
  | none => rfl
  | some era => simp [h] at absent

theorem registryDomain_insert (entries : Era.RegistryMap Era.Record) (count : Nat)
    (era : Era.Record) (domain : RegistryDomain entries count) :
    RegistryDomain (PartialMap.insert entries count era) (count + 1) := by
  intro generation
  change (PartialMap.get? (PartialMap.insert entries count era) generation).isSome ↔ _
  rw [LawfulPartialMap.get?_insert]
  split
  · subst generation
    simp
  · have h := domain generation
    change entries[generation]?.isSome ↔ generation < count + 1
    rw [h]
    omega

variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance generationCertificate_persistent names generation era :
    Persistent (generationCertificate capacity names generation era) := by
  unfold generationCertificate
  infer_instance

/-- A started current-generation thread cannot be in a powered-off state.
This rules out treating live hardware failures as arbitrary dead-thread stutters. -/
theorem generation_cases (names : FixedNames) (g : State) (generation : Nat) (era : Era.Record) :
    iprop(⊢ powerInterp capacity names g -∗ generationCertificate capacity names generation era -∗
      ⌜generation < g.generation ∨ ThreadLive g generation⌝) := by
  unfold powerInterp PowerGhost.counterInterp generationCertificate FixedNames.power
  iintro ⟨⟨Hg, Hs⟩, _, _⟩ ⟨Hb, Hstarted, _⟩
  ihave %born := PowerGhost.gen_born_valid capacity.power names.generation g.generation generation $$ Hg Hb
  ihave %started := PowerGhost.gen_started_valid capacity.power names.started
    (PowerGhost.startCount g) generation $$ Hs Hstarted
  ipureintro
  by_cases dead : generation < g.generation
  · exact Or.inl dead
  · right
    have same : g.generation = generation := by omega
    refine ⟨?_, same⟩
    unfold PowerGhost.startCount at started
    cases h : g.power with
    | false => simp [h] at started; omega
    | true => rfl

/-- Open precisely the registered live era, retaining a wand that restores the
fixed interpretation. Other-generation registrations cannot select this era. -/
theorem live_era_access (names : FixedNames) (g : State) (generation : Nat)
    (era : Era.Record) (live : ThreadLive g generation) :
    iprop(⊢ powerInterp capacity names g -∗
      generationCertificate capacity names generation era -∗
      Era.interp capacity.era era g ∗
        (Era.interp capacity.era era g -∗ powerInterp capacity names g)) := by
  unfold powerInterp generationCertificate
  rw [live.1, live.2]
  simp only [↓reduceIte]
  iintro ⟨Hc, Hd, %entries, Hr, %domain, %current, %lookup, Hera⟩ ⟨_, _, Hregistered⟩
  ihave %registered := Era.registry_lookup capacity.registry names.registry entries
    generation era $$ Hr Hregistered
  have same : current = era := Option.some.inj (lookup.symm.trans registered)
  subst current
  isplitl [Hera]
  · iexact Hera
  · iintro Hera
    iframe
    ipureintro
    exact ⟨domain, lookup⟩

/-- Power loss advances the death counter and preserves the fixed disk and
complete registry. The discarded era's resources are affine. -/
theorem power_off (names : FixedNames) (g : State) (on : g.power = true) :
    iprop(powerInterp capacity names g ⊢ |==>
      (powerInterp capacity names (powerOff g) ∗
        PowerGhost.genDead capacity.power names.generation g.generation)) := by
  unfold powerInterp PowerGhost.counterInterp FixedNames.power
  iintro ⟨⟨Hg, Hs⟩, Hd, %entries, Hr, %domain, _⟩
  imod PowerGhost.gen_die capacity.power names.generation g.generation $$ Hg with ⟨Hg, Hdead⟩
  have count : PowerGhost.startCount (powerOff g) = PowerGhost.startCount g := by
    simp [PowerGhost.startCount, powerOff, on]
  imodintro
  rw [count]
  unfold powerOff
  simp only [Bool.false_eq_true, ↓reduceIte]
  iframe
  isplit
  · ipureintro
    exact domain
  · exact Iris.BI.true_intro

/-- Boot allocates a fresh era from the actual retained disk, registers its
complete record, and issues all machine client ownership and a persistent
generation certificate. No kernel auxiliary tokens are assumed or minted. -/
theorem power_on (eraSpec : Era.EraSpec capacity.era) (names : FixedNames)
    (image : BootImage) (g g' : State) (off : g.power = false)
    (shape : BootShape image g g') (memory : Tso.AddressMap MachCSL.Memory.Byte)
    (rep : MachCSL.Memory.FiniteMap.decode memory = g'.memory) (template : Era.Record) :
    iprop(powerInterp capacity names g ⊢ |==> ∃ era : Era.Record,
      ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ ∗
      powerInterp capacity names g' ∗
      generationCertificate capacity names g.generation era ∗
      Era.bootClients capacity.era era memory g' names.diskSize) := by
  have on := shape.2.2.1
  have gen := shape.1
  have disk := boot_disk_preserved image g g' shape
  have count : PowerGhost.startCount g = g.generation := by
    simp [PowerGhost.startCount, off]
  have count' : PowerGhost.startCount g' = g.generation + 1 := by
    simp [PowerGhost.startCount, on, gen]
  unfold powerInterp PowerGhost.counterInterp FixedNames.power
  rw [count, count']
  iintro ⟨⟨Hg, Hs⟩, Hd, %entries, Hr, %domain, _⟩
  ihave #Hb := PowerGhost.gen_born capacity.power names.generation g.generation $$ Hg
  imod PowerGhost.start_mark capacity.power names.started g.generation $$ Hs with ⟨Hs, Hstarted⟩
  imod eraSpec.allocate image g' memory template names.diskSize shape.2.2 rep with
    ⟨%era, %same, Hera, Hclients⟩
  imod Era.registry_insert capacity.registry names.registry entries g.generation era
    (registryDomain_fresh entries g.generation domain) $$ Hr with ⟨Hr, Hregistered⟩
  imodintro
  iexists era
  rw [disk, gen, on]
  unfold generationCertificate
  simp only [↓reduceIte]
  iframe
  isplit
  · ipureintro
    exact same
  iframe Hb
  ipureintro
  refine ⟨registryDomain_insert entries g.generation era domain, ?_⟩
  change PartialMap.get? (PartialMap.insert entries g.generation era) g.generation = some era
  rw [LawfulPartialMap.get?_insert]
  simp

/-- Initial powered-off allocation supplies the fixed interpretation, the full
durable-disk client range and the observation client. The initial history must
already describe the actual state's observations. -/
theorem initial_off_alloc (diskSpec : Disk.DiskSpec capacity.era.disk)
    (g : State) (off : g.power = false) (zero : g.generation = 0)
    (diskBytes : Nat) (history future : List Observation) (wf : ObservationsOK history g) :
    iprop(⊢ |==> ∃ names : FixedNames,
      ⌜names.diskSize = diskBytes⌝ ∗ stateInterp capacity names (history ++ future) g 0 future 1 ∗
      Disk.imageBytes capacity.era.disk names.durableDisk 0
        (Devices.Virtio.disk_read g.devices.virtio.v_disk 0 diskBytes) ∗
      PowerGhost.obsFrag capacity.power names.observations history) := by
  imod PowerGhost.fixed_alloc capacity.power g history future wf with ⟨%power, Hc, Ho, Hof⟩
  imod diskSpec.sizedAlloc g.devices.virtio.v_disk diskBytes with ⟨%disk, Hd, Hdf⟩
  imod Era.registry_alloc capacity.registry with ⟨%registry, Hr⟩
  imodintro
  iexists (FixedNames.mk power.generation power.started power.observations registry disk diskBytes)
  unfold stateInterp powerInterp FixedNames.power
  rw [off]
  simp only [Bool.false_eq_true, ↓reduceIte]
  iframe
  isplit
  · ipureintro
    simpa [PowerGhost.startCount, off, zero] using registryDomain_empty
  · exact Iris.BI.true_intro

theorem stateInterpSpec : StateInterpSpec capacity :=
  ⟨generation_cases capacity, live_era_access capacity, power_off capacity,
    power_on capacity, initial_off_alloc capacity⟩

end MachCSL.Logic.MachineInterp
