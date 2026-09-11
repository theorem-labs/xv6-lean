import MachCSL.Logic.FsDurSnapshotDefs
import MachCSL.Logic.EraRegistry
import MachCSL.Logic.LockDefs
import MachCSL.Logic.FsBootRecoveryDefs
import Iris.Algebra.Lib.MonoList
import Iris.Instances.Lib.GhostVar

/-! FsCrash's exact native record, history, generation custody and P_fs.
The physical disk is an explicit index, not a field or inferred byte tie. -/
namespace MachCSL.Logic.FsCrash
open Iris Iris.Std Iris.Algebra Iris.BI MachCSL.Memory

abbrev BlockMap := Xv6.Fs.DurableState.BlockMap
abbrev BlockSet := Xv6.Fs.BlockSet
abbrev Physical := Xv6.Fs.Disk

structure Record where
  committed : BlockMap
  history : List BlockMap

structure RecordWF (record : Record) (physical : Xv6.Fs.Blocks) (covered : BlockSet) (start : Int) : Prop where
  recovery : Xv6.Fs.Recovery.Recovers physical record.committed covered start
  last : record.history.getLast? = some record.committed
  header : Xv6.Fs.Recovery.HeaderWF physical covered start

structure LogMirror where
  view : Xv6.Fs.Blocks

def MirrorOK (mirror : LogMirror) (physical : Xv6.Fs.Blocks) (covered : BlockSet) (start : Int) : Prop :=
  ∀ b, b ∈ covered ∪ Xv6.Fs.SnapshotHome.logRegion start → mirror.view b = physical b

def mirrorOf (physical : Xv6.Fs.Blocks) : LogMirror := ⟨physical⟩

def mirrorUpdate (mirror : LogMirror) (block : Int) (bytes : List Byte) : LogMirror :=
  ⟨fun b => if b = block then bytes else mirror.view b⟩

structure Names where
  history : GName
  swap : GName
  registry : GName
  started : GName

abbrev HistoryRA := MonoList (DiscreteO BlockMap)
abbrev HistoryRF := constOF HistoryRA
def historyFunctor : GFunctor := ⟨HistoryRF, inferInstance⟩
abbrev MirrorRF := GhostVarF LogMirror
def mirrorFunctor : GFunctor := ⟨MirrorRF, inferInstance⟩

structure Capacity (GF : BundledGFunctors) where
  history : ElemG GF HistoryRF
  mirror : GhostVarG GF LogMirror
  registry : Era.RegistryCapacity GF
  mono : ElemG GF MonoNatRF
  lock : Lock.Capacity GF
  disk : Disk.Capacity GF
  links : FsLink.Capacity GF
  tops : FsTop.Capacity GF

/-- Explicit same-camera witness for the later machine bootstrap wrapper. -/
structure BootstrapCapacity (GF : BundledGFunctors) where
  crash : Capacity GF
  boot : FsBootRecovery.Capacity GF
  sameDisk : boot.era.disk = crash.disk

def historyEmbed (history : List BlockMap) : List (DiscreteO BlockMap) := history.map DiscreteO.mk

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def historyAuth (name : GName) (history : List BlockMap) : IProp GF :=
  iOwn (E := capacity.history) name (MonoList.auth (.own 1) (historyEmbed history))
def historyLowerBound (name : GName) (history : List BlockMap) : IProp GF :=
  iOwn (E := capacity.history) name (MonoList.lb (historyEmbed history))
def receipt (names : Names) (disk : BlockMap) : IProp GF :=
  iprop(∃ pre : List BlockMap, historyLowerBound capacity names.history (pre ++ [disk]))

def bootToken (name : GName) : IProp GF := Lock.frag capacity.lock name none

def mirrorHalf (name : GName) (mirror : LogMirror) : IProp GF :=
  letI := capacity.mirror
  ghost_var name (.own (1 : Qp).half) mirror

def registered (names : Names) (generation : Nat) (era : Era.Record) : IProp GF :=
  Era.registered capacity.registry names.registry generation era

def counterAuth (name : GName) (value : Nat) : IProp GF :=
  letI : MonoNatG GF := ⟨capacity.mono, name⟩
  MonoNat.auth_own name (.own 1) (.ofNat value)
def counterLowerBound (name : GName) (value : Nat) : IProp GF :=
  letI : MonoNatG GF := ⟨capacity.mono, name⟩
  MonoNat.lb_own name (.ofNat value)
def started (names : Names) (generation : Nat) : IProp GF :=
  counterLowerBound capacity names.started (generation + 1)

def custody (names : Names) (covered : BlockSet) (start : Int) (disk : Physical)
    (generation : Nat) : IProp GF :=
  iprop(∃ (era : Era.Record) (mirror : LogMirror),
    registered capacity names generation era ∗ started capacity names generation ∗
    mirrorHalf capacity era.logMirror mirror ∗ ⌜MirrorOK mirror (Xv6.Fs.blocks disk) covered start⌝)

def armBranch (names : Names) (covered : BlockSet) (start : Int) (disk : Physical)
    (count : Nat) : IProp GF :=
  iprop(⌜count = 0⌝ ∨ ∃ generation : Nat, ⌜count = generation + 1⌝ ∗
    custody capacity names covered start disk generation)

def arm (names : Names) (covered : BlockSet) (start : Int) (disk : Physical) : IProp GF :=
  iprop(∃ count : Nat, counterAuth capacity names.swap count ∗ armBranch capacity names covered start disk count)

noncomputable def Pfs (names : Names) (covered : BlockSet) (start : Int) (disk : Physical) : IProp GF :=
  iprop(∃ record : Record, historyAuth capacity names.history record.history ∗
    ⌜RecordWF record (Xv6.Fs.blocks disk) covered start⌝ ∗ arm capacity names covered start disk ∗
    FsDurSnapshot.Pdur capacity.disk capacity.links capacity.tops record.committed)

noncomputable def named (swap registry started : GName) (covered : BlockSet)
    (start : Int) (disk : Physical) : IProp GF :=
  iprop(∃ names : Names, ⌜names.swap = swap ∧ names.registry = registry ∧ names.started = started⌝ ∗
    Pfs capacity names covered start disk)

/-- A whole supplied native epoch, not an accessor continuation or pure fact. -/
noncomputable def lend (covered : BlockSet) (start : Int) (disk : Physical) : IProp GF :=
  iprop(∃ committed : BlockMap, ⌜Xv6.Fs.Recovery.Recovers (Xv6.Fs.blocks disk) committed covered start⌝ ∗
    FsDurSnapshot.Pdur capacity.disk capacity.links capacity.tops committed)

end MachCSL.Logic.FsCrash
