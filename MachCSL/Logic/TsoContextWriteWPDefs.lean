import MachCSL.Logic.TsoContextReadWPDefs
import MachCSL.Logic.MemoryWriteWPDefs

/-! Ordinary registered eight-byte writes. Context resources are exactly the
same definitions as the read adapter; no camera or runtime name is added. -/
namespace MachCSL.Logic.TsoContextWriteWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContextReadWP

/-- Actual successful ordinary-write effects, retaining the single authored
message and the distinct reservation update. -/
structure Effect (before after : State) (cpu : CPU) (req : MemoryWriteWP.WriteRequest 8)
    (word : BitVec 64) : Prop where
  memory : after.memory = writeBytes before.memory req.pa 8 word
  log : after.log = before.log ++ [⟨snapshot req.pa 8 word, hartAgent cpu⟩]
  views : after.views = before.views
  reservations : after.reservations = updateHart before.reservations cpu none
  registers : after.registers = before.registers
  devices : after.devices = before.devices
  image : after.image = before.image
  power : after.power = before.power
  generation : after.generation = before.generation

end MachCSL.Logic.TsoContextWriteWP
