import MachCSL.Logic.TsoContextBytesReadWPDefs
import MachCSL.Logic.MemoryWriteWPDefs

/-! Ordinary registered byte-window writes. Context resources are exactly the
same definitions as the read adapter; no camera or runtime name is added. -/
namespace MachCSL.Logic.TsoContextBytesWriteWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContextBytesReadWP

/-- Actual successful ordinary-write effects, retaining the single authored
message and the distinct reservation update. -/
structure Effect (before after : State) (cpu : CPU) (req : MemoryWriteWP.WriteRequest n)
    (word : BitVec (8 * n)) : Prop where
  memory : after.memory = writeBytes before.memory req.pa n word
  log : after.log = before.log ++ [⟨snapshot req.pa n word, hartAgent cpu⟩]
  views : after.views = before.views
  reservations : after.reservations = updateHart before.reservations cpu none
  registers : after.registers = before.registers
  devices : after.devices = before.devices
  image : after.image = before.image
  power : after.power = before.power
  generation : after.generation = before.generation

end MachCSL.Logic.TsoContextBytesWriteWP
