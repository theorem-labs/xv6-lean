import MachCSL.Logic.PowerWPDefs

/-! Explicit client obligation and operational conclusion of machine adequacy.
The client must establish the boot handler; this is not a closed kernel proof. -/
namespace MachCSL.Logic.MachineAdequacy
open Iris Iris.BI MachCSL.Machine

/-- Initial disk fragments belong to the actual powered-off state's durable
disk. The handler is required in the native world supplied by adequacy, for
every freshly allocated fixed name record and whole execution trace. -/
def BootInitializer {GF : BundledGFunctors} [Platform]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (initial : State)
    (diskBytes : Nat) (template : Era.Record) (N : Namespace) : Prop :=
  ∀ [InvGS GF] (fixed : MachineInterp.FixedNames) (whole : List Observation),
    fixed.diskSize = diskBytes →
    iprop(⊢ Disk.imageBytes capacity.era.disk fixed.durableDisk 0
      (Devices.Virtio.disk_read initial.devices.virtio.v_disk 0 diskBytes) -∗
      ObservationInvariant.trivial capacity.power N fixed.observations ={⊤}=∗
      PowerWP.bootHandler capacity image fixed whole template)

/-- Every thread has an actual machine transition. The same operational
trace has the source alternation, boot count, and current UART wire tie. -/
def SafeConfiguration [Platform] (image : BootImage) (threads : List Expr)
    (state : State) (events : List Observation) : Prop :=
  (∀ thread ∈ threads, ∃ observations next state' forks,
    Step image thread state observations next state' forks) ∧
  ObservationsOK events state

end MachCSL.Logic.MachineAdequacy
