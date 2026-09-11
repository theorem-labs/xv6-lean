import MachCSL.Machine.SpinlockDecodeDefs

namespace MachCSL.Machine.SpinlockControl
open LeanPaperStock.Functions

def csrStatic (rs : RegisterFile) : RegisterFile
  | .cur_privilege => .Machine
  | r => rs r

def csrAfter (rs : RegisterFile) : RegisterFile :=
  Sail.Registers.write rs .x5 (rs .mhartid)

def jumpStatic (rs : RegisterFile) : RegisterFile
  | .misa => 0x800000000014112d#64
  | r => rs r

def branchAfter (retry : Bool) (rs : RegisterFile) : RegisterFile :=
  if (if retry then rs .x15 != 0#64 else rs .x6 == 0#64) then
    Sail.Registers.write rs .nextPC
      (SpinlockImage.instructionAddress (if retry then ⟨6, by decide⟩ else ⟨16, by decide⟩))
  else rs

end MachCSL.Machine.SpinlockControl
