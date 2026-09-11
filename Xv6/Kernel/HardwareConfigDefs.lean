import Xv6.Kernel.KernelMapStaticDefs
import MachCSL.Machine.PmaClassDefs
import LeanPaperStock.SysRegs

/-! Exact persistent source hw_config and counter_caps from
RiscvFetchExec.v:281–333. These resources are supplied or persisted from
actual register cells, not inferred from a synthetic reference file. -/
namespace Xv6.Kernel.HardwareConfig
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := KernelMapStatic.Capacity

def misaC : BitVec 64 := 0x800000000014112d#64

structure Values where
  isa : BitVec 64
  security : BitVec 64
  regions : List PMA_Region
  landing : BitVec 1
  counters : BitVec 32
  hpm : RegisterType .mhpmcounter

def Facts (v : Values) : Prop :=
  _get_Misa_S v.isa = 1#1 ∧ _get_Misa_C v.isa = 1#1 ∧
  _get_Misa_U v.isa = 1#1 ∧ _get_Misa_M v.isa = 1#1 ∧
  PmaClass.allowsAll v.regions ∧
  pmm_mode_backwards (_get_Seccfg_PMM v.security) = .PMM_Disabled ∧
  bool_bit_backwards (_get_Seccfg_MLPE v.security) = false ∧
  (v.landing == landing_pad_bits_backwards .LP_EXPECTED) = false ∧
  _get_Misa_A v.isa = 1#1 ∧ v.isa = misaC ∧ v.security = 0#64

def bootValues (counters : BitVec 32) (hpm : RegisterType .mhpmcounter) : Values :=
  ⟨misaC, 0#64, pmaBoot, 0#1, counters, hpm⟩

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Exactly the six frozen hardware cells, and the two frozen counter cells.
mcounteren is separately owned by TimerCap after timerinit. -/
def cells (era : Era.Record) (cpu : CPU) (dq : DFrac) (v : Values) : IProp GF :=
  iprop(Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .misa dq v.isa ∗
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .mseccfg dq v.security ∗
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .pma_regions dq v.regions ∗
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .htif_tohost_base dq none ∗
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .elp dq v.landing ∗
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .senvcfg dq 0#64 ∗
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .scounteren dq v.counters ∗
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .mhpmcounter dq v.hpm)

def counterCaps (era : Era.Record) (cpu : CPU) : IProp GF :=
  iprop(∃ counters hpm,
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .scounteren .discard counters ∗
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .mhpmcounter .discard hpm)

noncomputable def config (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) : IProp GF :=
  iprop(∃ v, cells capacity era cpu .discard v ∗ ⌜Facts v⌝ ∗
    KernelMapStatic.claims capacity era.kernelMap ∗
    MachineInterp.generationCertificate capacity.machine fixed gen era)

end Xv6.Kernel.HardwareConfig
