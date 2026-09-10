import MachCSL.Sail.Model

/-! Platform initialization from `iris/ArchReset.v` at the paper pin.
The boot program starts with arbitrary registers and performs only the explicit
board writes followed by actual generated reset and firmware code. A run and
reset postcondition still need to be proved; this is not a replacement literal
register table. The reset vector is parameterized for the shared JAL/xv6 machine. -/
namespace MachCSL.Machine

open LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free.PreSail

def boardWired (vector hart : BitVec 64) : SailM Unit := do
  set_pc_reset_address vector
  writeReg .mhartid hart

def boardRegisters (regions : List PMA_Region) : SailM Unit := do
  writeReg .pma_regions regions
  writeReg .mstatus 0xA00000000#64
  writeReg .misa 0x8000000000000000#64
  writeReg .mseccfg 0#64
  writeReg .menvcfg 0#64
  writeReg .htif_tohost_base none
  writeReg .mie 0#64
  writeReg .mideleg 0#64
  writeReg .senvcfg 0#64
  writeReg .sstateen0 0#32

def bootProgram (vector hart : BitVec 64) (regions : List PMA_Region) : SailM Unit := do
  boardWired vector hart
  boardRegisters regions
  init_model ""
  init_boot_requirements ()

end MachCSL.Machine
