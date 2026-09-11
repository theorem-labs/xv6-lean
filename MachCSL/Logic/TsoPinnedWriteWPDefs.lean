import MachCSL.Logic.MemoryWriteWPDefs
import MachCSL.Logic.TsoPinnedStoreDefs
import LeanPaperStock.PhysMemInterface

/-! Eight-byte pinned conditional RAM writes. The dependent event width is
fixed; generic request metadata is retained independently of that width. -/
namespace MachCSL.Logic.TsoPinnedWriteWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

abbrev pinWindow {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (a : PhysicalAddress) (word : BitVec 64) (dq : DFrac)
    (floors : Nat → Nat) (sets : Nat → Tso.ByteSet) : IProp GF :=
  TsoPinnedStore.pinWindow (MemoryWriteWP.storeCapacity capacity) (MemoryWriteWP.storeNames era)
    a 8 word dq floors sets

abbrev storedWindow {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (a : PhysicalAddress) (word : BitVec 64) (time : Nat)
    (floors : Nat → Nat) (sets : Nat → Tso.ByteSet) : IProp GF :=
  TsoPinnedStore.storedWindow (MemoryWriteWP.storeCapacity capacity) (MemoryWriteWP.storeNames era)
    a 8 word time floors sets

/-- Exact request produced by `write_ram Write_RISCV_conditional`. -/
def conditionalRequest (a : PhysicalAddress) (word : BitVec 64) : MemoryWriteWP.WriteRequest 8 :=
  { access_kind := .AK_explicit { variety := .AV_exclusive, strength := .AS_normal }
    va := none, pa := a, translation := (), size := 8, value := some word, tag := none }

/-- All raw success payloads map to true; the actual abort maps to false. -/
def booleanReply (result : MemoryWriteWP.WriteResult) : Bool :=
  match result with | .Ok _ => true | .Err () => false

/-- Actual successful exclusive-write fields. Blocking has no such effect. -/
structure Effect (before after : State) (cpu : CPU) (req : MemoryWriteWP.WriteRequest 8)
    (word : BitVec 64) : Prop where
  memory : after.memory = writeBytes before.memory req.pa 8 word
  log : after.log = before.log ++ [⟨snapshot req.pa 8 word, hartAgent cpu⟩]
  views : after.views = updateHart before.views cpu (before.log.length + 1)
  reservations : after.reservations = updateHart before.reservations cpu none
  registers : after.registers = before.registers
  devices : after.devices = before.devices
  image : after.image = before.image
  power : after.power = before.power
  generation : after.generation = before.generation

/-- The genuine post-event continuation receives every new pin and the exact
positive authored timestamp, cleared reservation and matching view receipt. -/
def continuation {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU)
    (a : PhysicalAddress) (word : BitVec 64) (floors : Nat → Nat) (sets : Nat → Tso.ByteSet)
    (next : SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  iprop(▷ (∀ time, storedWindow capacity era a word time floors sets -∗
    Tso.History.logElem capacity.era.history era.logEntries (time - 1)
      ⟨snapshot a 8 word, hartAgent cpu⟩ -∗ ⌜0 < time⌝ -∗
    Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
    Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) time -∗
    MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu next) post))

end MachCSL.Logic.TsoPinnedWriteWP
