import Xv6.Kernel.HardwareConfigDefs
import Xv6.Kernel.MycpuRegimeShellDefs

/-! Exact source IntrDefs.v595–667 supervisor configuration. SIE is not
fixed here; its native ghost half remains tied to the owned mstatus cell. -/
namespace Xv6.Kernel.Sconf
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MycpuRegimeShell.Capacity

def mieS : BitVec 64 := 0x220#64
def menvcfgS : BitVec 64 := 0xA000000000000000#64

def Delegated (delegation : BitVec 64) : Prop := mieS &&& ~~~delegation = 0#64

/-- All four source environment facts, in addition to the source literal.
No arbitrary environment is substituted for MENVCFG_S. -/
def EnvironmentFacts (environment : BitVec 64) : Prop :=
  (_get_MEnvcfg_PBMTE environment == 0#1) = true ∧
  pmm_mode_backwards (_get_MEnvcfg_PMM environment) = .PMM_Disabled ∧
  bool_bit_backwards (_get_MEnvcfg_LPE environment) = false ∧
  (_get_MEnvcfg_FIOM environment == 1#1) = false ∧ environment = menvcfgS

variable {GF : BundledGFunctors} (capacity : Capacity GF)

abbrev cell (era : Era.Record) (cpu : CPU) (r : Register) (value : RegisterType r) : IProp GF :=
  Registers.regPointsto capacity.machine.era.registers (era.registers cpu) r (.own 1) value
abbrev msOwn (era : Era.Record) (cpu : CPU) (ms : BitVec 64) : IProp GF :=
  SupervisorBits.msOwnAt capacity.supervisorBits era cpu ms

/-- Source MinstretInv.v341. Counter register ownership is not invented here. -/
def minstretInv : IProp GF := iprop(emp)

def interrupts (era : Era.Record) (cpu : CPU) : IProp GF :=
  iprop(∃ delegation : BitVec 64,
    cell capacity era cpu .mie mieS ∗ cell capacity era cpu .mideleg delegation ∗ ⌜Delegated delegation⌝)

def environment (era : Era.Record) (cpu : CPU) : IProp GF :=
  iprop(∃ value : BitVec 64, cell capacity era cpu .menvcfg value ∗ ⌜EnvironmentFacts value⌝)

noncomputable abbrev hardware (fixed : MachineInterp.FixedNames) (gen : Nat)
    (era : Era.Record) (cpu : CPU) : IProp GF :=
  HardwareConfig.config capacity.translation fixed gen era cpu

/-- Resource grouping for opening, with every source conjunct retained. -/
noncomputable def parts (fixed : MachineInterp.FixedNames) (gen : Nat)
    (era : Era.Record) (cpu : CPU) (ms : BitVec 64) : IProp GF :=
  iprop(hardware capacity fixed gen era cpu ∗ minstretInv (GF := GF) ∗
    cell capacity era cpu .cur_privilege .Supervisor ∗ msOwn capacity era cpu ms ∗
    interrupts capacity era cpu ∗ environment capacity era cpu)

noncomputable def sconf (fixed : MachineInterp.FixedNames) (gen : Nat)
    (era : Era.Record) (cpu : CPU) : IProp GF :=
  iprop(∃ ms : BitVec 64, parts capacity fixed gen era cpu ms)

/-- Source sconf_at is an accessor. Its closer accepts any replacement of
msOwn with all its real cell/ghost/fact resources, not a second sconf body. -/
noncomputable def sconfAt (fixed : MachineInterp.FixedNames) (gen : Nat)
    (era : Era.Record) (cpu : CPU) (ms : BitVec 64) : IProp GF :=
  iprop(msOwn capacity era cpu ms ∗
    (∀ replacement : BitVec 64, msOwn capacity era cpu replacement -∗ sconf capacity fixed gen era cpu))

end Xv6.Kernel.Sconf
