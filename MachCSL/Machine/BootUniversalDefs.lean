import MachCSL.Machine.ColdBootFacts
import MachCSL.Machine.Boot

namespace MachCSL.Machine.BootUniversal

/-- Only fields explicitly fixed by board and generated reset. Counter
configuration and PMP address bits are intentionally absent. -/
def staticProjection (rs : RegisterFile) :=
  (rs .PC, rs .nextPC, rs .misa, rs .mstatus, rs .mie, rs .mideleg,
    rs .menvcfg, rs .elp, rs .mseccfg, rs .cur_privilege, rs .hart_state,
    rs .pma_regions, rs .htif_tohost_base)

def result (before : RegisterFile) (vector hart : BitVec 64) : Option (Unit × RegisterFile) :=
  registerRun 10000 (bootProgram vector hart pmaBoot) before


structure StaticBoot (vector : BitVec 64) (rs : RegisterFile) : Prop where
  pc : rs .PC = vector
  nextPC : rs .nextPC = vector
  misa : rs .misa = 0x800000000014112d#64
  mstatus : rs .mstatus = 0xA00000000#64
  mie : rs .mie = 0#64
  mideleg : rs .mideleg = 0#64
  menvcfg : rs .menvcfg = 0#64
  elp : rs .elp = 0#1
  mseccfg : rs .mseccfg = 0#64
  privilege : rs .cur_privilege = .Machine
  hartState : rs .hart_state = .HART_ACTIVE ()
  pma : rs .pma_regions = pmaBoot
  htif : rs .htif_tohost_base = none

end MachCSL.Machine.BootUniversal
