import MachCSL.Logic.FsBootBytesDefs
import MachCSL.Logic.EraSpec
import Xv6.Fs.RecoveryDefs

/-! Canonical recovery of the current disk and coherent machine-era bootstrap
resource columns. These definitions assume neither replay success nor allocation. -/
namespace MachCSL.Logic.FsBootRecovery
open Iris Iris.Std Iris.BI MachCSL.Memory

abbrev Physical := Xv6.Fs.Disk
abbrev BlockMap := Xv6.Fs.DurableState.BlockMap
abbrev BlockSet := Xv6.Fs.BlockSet
abbrev Names := FsBlocks.Names

def recovered (disk : Physical) (covered : BlockSet) (start : Int) : BlockMap :=
  Xv6.Fs.Recovery.recover (Xv6.Fs.blocks disk) covered start

def committed (disk : Physical) (covered : BlockSet) (start : Int) : Xv6.Fs.Blocks :=
  Xv6.Fs.Recovery.view (Xv6.Fs.blocks disk) (recovered disk covered start)

def exceptions (disk : Physical) (start : Int) : BlockSet :=
  Xv6.Fs.Recovery.writeSet (Xv6.Fs.blocks disk) start

/-- Derived properties of the actual replay result; no independently chosen
committed map or stronger snapshot validity is supplied to the native rule. -/
structure Facts (disk : Physical) (covered : BlockSet) (start : Int) : Prop where
  full : Xv6.Fs.Recovery.Full (recovered disk covered start)
  viewFull : ∀ b, (committed disk covered start b).length = 1024
  domain : ∀ b, (recovered disk covered start)[b]?.isSome ↔ b ∈ Xv6.Fs.SnapshotHome.homeSet covered start
  restricted : Xv6.Fs.SnapshotHome.restrict (committed disk covered start)
    (Xv6.Fs.SnapshotHome.homeSet covered start) = recovered disk covered start
  raw : ∀ b, b ∈ Xv6.Fs.SnapshotHome.homeSet covered start → b ∉ exceptions disk start →
    committed disk covered start b = Xv6.Fs.blocks disk b
  slot : ∀ i b, (Xv6.Fs.Recovery.headerDecode (Xv6.Fs.blocks disk start)).2[i]? = some b →
    committed disk covered start b = Xv6.Fs.blocks disk (Xv6.Fs.SnapshotHome.logSlot start i)

/-- The same era disk camera is used structurally by every physical/logged
byte rule. The additional cache cameras are the existing block capacity. -/
structure Capacity (GF : BundledGFunctors) where
  era : Era.Capacity GF
  blocks : FsBlockGhost.Capacity GF

def Capacity.bytes {GF : BundledGFunctors} (capacity : Capacity GF) : FsBootBytes.Capacity GF :=
  ⟨capacity.blocks, capacity.era.disk⟩

/-- The template's fourteen protocol names are retained. Only the image name
is fixed to the actual era's already allocated physical byte authority. -/
def forEra (template : DiskClient.Names) (era : Era.Record) : DiskClient.Names :=
  { template with img := era.disk }

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- All five other machine boot client columns, verbatim and in source order. -/
def otherClients (era : Era.Record) (memory : Tso.AddressMap Byte) (state : Machine.State) : IProp GF :=
  iprop(GlobalRegisters.allInitialCells capacity.era.registers era.registers state.registers ∗
    Tso.Interp.bootClients capacity.era.tso era.tsoNames memory ∗
    ([∗map] a ↦ _byte ∈ memory, Heap.token capacity.era.heap ⟨era.heap, era.metadata⟩ a ⊤) ∗
    Device.fragments capacity.era.devices era.deviceNames state.devices ∗
    Reservations.allFragments capacity.era.reservations era.reservations state.reservations)

variable {hlc : HasLC} [InvGS_gen hlc GF]

def allocated (diskNames : DiskClient.Names) (disk : Physical) (covered : BlockSet) (start : Int)
    (device : BitVec 32) (link top : GName) (names : Names) : IProp GF :=
  FsBootBytes.allocated capacity.bytes diskNames disk covered
    (Xv6.Fs.SnapshotHome.homeSet covered start) device link top names
    (committed disk covered start) (exceptions disk start)

end MachCSL.Logic.FsBootRecovery
