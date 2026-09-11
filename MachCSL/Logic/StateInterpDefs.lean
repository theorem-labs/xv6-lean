import MachCSL.Logic.EraRegistry
import MachCSL.Logic.PowerGhostDefs
import Iris.ProgramLogic.WeakestPre

/-! The fixed, era-independent state interpretation of RiscvPtsto.v.
Constructing this instance does not supply initial WPs or prove adequacy. -/
namespace MachCSL.Logic.MachineInterp
open Iris Iris.BI MachCSL.Machine

structure Capacity (GF : BundledGFunctors) where
  era : Era.Capacity GF
  registry : Era.RegistryCapacity GF
  observations : GhostVarG GF (List Observation)

/-- Generation and log-length ghosts share the one native mono-nat camera. -/
def Capacity.power {GF : BundledGFunctors} (c : Capacity GF) : PowerGhost.Capacity GF :=
  ⟨c.era.views.sharedNat, c.observations⟩

structure FixedNames where
  generation : GName
  started : GName
  observations : GName
  registry : GName
  durableDisk : GName
  diskSize : Nat

def FixedNames.power (names : FixedNames) : PowerGhost.Names :=
  ⟨names.generation, names.started, names.observations⟩

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Source registry domain `set_seq 0 start_count`: no future or omitted eras. -/
def RegistryDomain (entries : Era.RegistryMap Era.Record) (count : Nat) : Prop :=
  ∀ generation, entries[generation]?.isSome ↔ generation < count

/-- Durable authority is outside the current-era conditional, so power loss
does not discard the tie to the actual disk. -/
def powerInterp (names : FixedNames) (g : State) : IProp GF :=
  iprop(PowerGhost.counterInterp capacity.power names.power g ∗
    Disk.imageAuthSized capacity.era.disk names.durableDisk names.diskSize g.devices.virtio.v_disk ∗
    ∃ entries : Era.RegistryMap Era.Record,
      Era.registryAuth capacity.registry names.registry entries ∗
      ⌜RegistryDomain entries (PowerGhost.startCount g)⌝ ∗
      (if g.power then
        (∃ era : Era.Record, ⌜entries[g.generation]? = some era⌝ ∗ Era.interp capacity.era era g)
      else True))

/-- Exact source generation certificate: birth, completed start, and immutable
registration of this complete era record. -/
def generationCertificate (names : FixedNames) (generation : Nat) (era : Era.Record) : IProp GF :=
  iprop(PowerGhost.genBorn capacity.power names.generation generation ∗
    PowerGhost.genStarted capacity.power names.started generation ∗
    Era.registered capacity.registry names.registry generation era)

/-- The future trace and fixed runtime names remain unchanged across eras. -/
def stateInterp (names : FixedNames) (whole : List Observation) (g : State)
    (_steps : Nat) (future : List Observation) (_threads : Nat) : IProp GF :=
  iprop(powerInterp capacity names g ∗
    PowerGhost.obsInterp capacity.power names.observations whole g future)

/-- Exactly the source zero-later-per-step instance with trivial fork postcondition.
Its operational language is the same image-parametric concrete machine. -/
@[reducible] def irisGS [Platform] (image : BootImage) {hlc : HasLC} [InvGS_gen hlc GF]
    (names : FixedNames) (whole : List Observation) :
    @IrisGS_gen hlc Expr Empty State Observation (language image) GF := by
  letI := language image
  exact {
    invGS := inferInstance
    stateInterp := stateInterp capacity names whole
    numLatersPerStep := fun _ => 0
    forkPost := fun _ => iprop(True)
    stateInterp_mono := by
      intro g steps future threads
      unfold stateInterp
      iintro H
      imodintro
      iexact H }

end MachCSL.Logic.MachineInterp
