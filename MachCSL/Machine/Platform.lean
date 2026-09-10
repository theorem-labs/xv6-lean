import MachCSL.Machine.BootProgram
import MachCSL.Memory.Defs

/-! Board PMA table from `iris/RiscvLang.v:pma_boot*` at the paper pin.
The eventual boot proof must check this table against the generated initializer;
these transparent declarations alone do not establish that correspondence. -/
namespace MachCSL.Machine

def ramLow : Nat := 0x80000000
def ramHigh : Nat := 0x88000000
abbrev CPU := Fin 8
def hartAgent (cpu : CPU) : Memory.Agent := cpu.val
def diskAgent : Memory.Agent := 8

def pmaBootRom : PMA := {
  mem_type := .IOMemory
  cacheable := true
  coherent := false
  executable := false
  readable := true
  writable := false
  read_idempotent := true
  write_idempotent := true
  misaligned_exceptions := ⟨none, none, .AccessFault⟩
  atomic_support := .AMONone
  reservability := .RsrvNone
  supports_cbo_zero := false
  supports_pte_read := false
  supports_pte_write := false
  misaligned_atomicity_granule_size_exp := 0
  vector_misaligned_atomicity_granule_size_exp := 0 }

def pmaBootIo : PMA := { pmaBootRom with
  cacheable := false
  coherent := true
  writable := true
  read_idempotent := false
  write_idempotent := false }

def pmaBootRam : PMA := { pmaBootRom with
  mem_type := .MainMemory
  coherent := true
  executable := true
  writable := true
  atomic_support := .AMOCASQ
  reservability := .RsrvEventual
  supports_cbo_zero := true
  supports_pte_read := true
  supports_pte_write := true
  misaligned_atomicity_granule_size_exp := 4
  vector_misaligned_atomicity_granule_size_exp := 4 }

def pmaBoot : List PMA_Region := [
  ⟨0x1000#64, 0x1000#64, pmaBootRom, false⟩,
  ⟨0x2000000#64, 0x10000000#64, pmaBootIo, false⟩,
  ⟨BitVec.ofNat 64 ramLow, BitVec.ofNat 64 (ramHigh - ramLow), pmaBootRam, true⟩]

end MachCSL.Machine
