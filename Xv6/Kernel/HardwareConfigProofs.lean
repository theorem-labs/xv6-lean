import Xv6.Kernel.HardwareConfigSpec
import Xv6.Kernel.KernelMapStaticLink
import MachCSL.Machine.PmaClassProofs
import MachCSL.Logic.RegisterProofs
import MachCSL.Logic.StateInterpProofs

namespace Xv6.Kernel.HardwareConfig
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem boot (counters : BitVec 32) (hpm : RegisterType .mhpmcounter) : Facts (bootValues counters hpm) := by
  refine ⟨?_, ?_, ?_, ?_, PmaClass.boot, ?_, ?_, ?_, ?_, rfl, rfl⟩
  all_goals dsimp only [bootValues]
  all_goals first | decide | rfl


theorem pureSpec : PureSpec where
  boot := boot
  isa := fun _ facts => facts.2.2.2.2.2.2.2.2.2.1
  pma := fun _ facts => facts.2.2.2.2.1

variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance cells_persistent era cpu v : Persistent (cells capacity era cpu .discard v) := by
  unfold cells
  infer_instance

instance config_persistent fixed gen era cpu : Persistent (config capacity fixed gen era cpu) := by
  unfold config
  infer_instance

instance counters_persistent era cpu : Persistent (counterCaps capacity era cpu) := by
  unfold counterCaps
  infer_instance

theorem persist era cpu dq v : iprop(cells capacity era cpu dq v ⊢ |==> cells capacity era cpu .discard v) := by
  unfold cells
  iintro ⟨Hisa, Hsec, Hpma, Hhtif, Help, Hsenv, Hcounter, Hhpm⟩
  imod Registers.regPointsto_persist capacity.machine.era.registers (era.registers cpu) .misa dq v.isa $$ Hisa with Hisa
  imod Registers.regPointsto_persist capacity.machine.era.registers (era.registers cpu) .mseccfg dq v.security $$ Hsec with Hsec
  imod Registers.regPointsto_persist capacity.machine.era.registers (era.registers cpu) .pma_regions dq v.regions $$ Hpma with Hpma
  imod Registers.regPointsto_persist capacity.machine.era.registers (era.registers cpu) .htif_tohost_base dq none $$ Hhtif with Hhtif
  imod Registers.regPointsto_persist capacity.machine.era.registers (era.registers cpu) .elp dq v.landing $$ Help with Help
  imod Registers.regPointsto_persist capacity.machine.era.registers (era.registers cpu) .senvcfg dq 0#64 $$ Hsenv with Hsenv
  imod Registers.regPointsto_persist capacity.machine.era.registers (era.registers cpu) .scounteren dq v.counters $$ Hcounter with Hcounter
  imod Registers.regPointsto_persist capacity.machine.era.registers (era.registers cpu) .mhpmcounter dq v.hpm $$ Hhpm with Hhpm
  imodintro
  iframe

/-- Generic framing avoids normalizing the entire finite static map in
proofmode. Every public constructor instantiates P with the exact native
static claim bundle; P is not a public client obligation. -/
private noncomputable def bundle (P : IProp GF) (fixed : MachineInterp.FixedNames)
    (gen : Nat) (era : Era.Record) (cpu : CPU) : IProp GF :=
  iprop(∃ v, cells capacity era cpu .discard v ∗ ⌜Facts v⌝ ∗ P ∗
    MachineInterp.generationCertificate capacity.machine fixed gen era)

private theorem intro_config_generic (P : IProp GF) (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (dq : DFrac) (v : Values) (facts : Facts v) :
    iprop(⊢ cells capacity era cpu dq v -∗ P -∗
      MachineInterp.generationCertificate capacity.machine fixed gen era ==∗ bundle capacity P fixed gen era cpu) := by
  iintro Hcells Hmap Hcert
  imod persist capacity era cpu dq v $$ Hcells with Hcells
  imodintro
  unfold bundle
  iexists v
  iframe Hcells Hmap Hcert
  ipureintro
  exact facts

private theorem access_generic (P : IProp GF) [Persistent P] fixed gen era cpu :
    iprop(bundle capacity P fixed gen era cpu ⊢ ∃ v, cells capacity era cpu .discard v ∗ ⌜Facts v⌝ ∗
      P ∗
      MachineInterp.generationCertificate capacity.machine fixed gen era ∗ bundle capacity P fixed gen era cpu) := by
  haveI : Persistent (bundle capacity P fixed gen era cpu) := by unfold bundle; infer_instance
  iintro #Hconfig
  ihave Hparts := Hconfig
  iunfold bundle at Hparts
  icases Hparts with ⟨%v, Hcells, %facts, Hmap, Hcert⟩
  iexists v
  iframe Hcells Hmap Hcert Hconfig
  ipureintro
  exact facts

private theorem counters_generic (P : IProp GF) fixed gen era cpu : iprop(bundle capacity P fixed gen era cpu ⊢ counterCaps capacity era cpu) := by
  unfold bundle cells counterCaps
  iintro ⟨%v, ⟨_, _, _, _, _, _, Hcounter, Hhpm⟩, _, _, _⟩
  iexists v.counters, v.hpm
  iframe

private theorem isa_agree_generic (P : IProp GF) fixed gen era cpu dq value :
    iprop(⊢ bundle capacity P fixed gen era cpu -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .misa dq value -∗
      ⌜value = misaC⌝) := by
  unfold bundle cells
  iintro ⟨%v, ⟨Hisa, _, _, _, _, _, _, _⟩, %facts, _, _⟩ Hvalue
  ihave %same := Registers.regPointsto_agree capacity.machine.era.registers (era.registers cpu)
    .misa .discard dq v.isa value $$ [Hisa Hvalue]
  · iframe
  ipureintro
  exact same.symm.trans (pureSpec.isa v facts)

private theorem pma_agree_generic (P : IProp GF) fixed gen era cpu dq regions :
    iprop(⊢ bundle capacity P fixed gen era cpu -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .pma_regions dq regions -∗
      ⌜PmaClass.allowsAll regions⌝) := by
  unfold bundle cells
  iintro ⟨%v, ⟨_, _, Hpma, _, _, _, _, _⟩, %facts, _, _⟩ Hvalue
  ihave %same := Registers.regPointsto_agree capacity.machine.era.registers (era.registers cpu)
    .pma_regions .discard dq v.regions regions $$ [Hpma Hvalue]
  · iframe
  ipureintro
  exact same ▸ pureSpec.pma v facts

private theorem map_generic (P : IProp GF) fixed gen era cpu :
    iprop(bundle capacity P fixed gen era cpu ⊢ P) := by
  unfold bundle
  iintro ⟨%v, _, _, HP, _⟩
  iexact HP

theorem actual : Spec capacity where
  persistent := config_persistent capacity
  counters_persistent := counters_persistent capacity
  persist := persist capacity
  intro := fun fixed gen era cpu dq v facts =>
    intro_config_generic capacity (KernelMapStatic.claims capacity era.kernelMap) fixed gen era cpu dq v facts
  access := fun fixed gen era cpu =>
    access_generic capacity (KernelMapStatic.claims capacity era.kernelMap) fixed gen era cpu
  counters := fun fixed gen era cpu =>
    counters_generic capacity (KernelMapStatic.claims capacity era.kernelMap) fixed gen era cpu
  isa_agree := fun fixed gen era cpu dq value =>
    isa_agree_generic capacity (KernelMapStatic.claims capacity era.kernelMap) fixed gen era cpu dq value
  pma_agree := fun fixed gen era cpu dq regions =>
    pma_agree_generic capacity (KernelMapStatic.claims capacity era.kernelMap) fixed gen era cpu dq regions
  static := fun fixed gen era cpu vpn permission classified =>
    (map_generic capacity (KernelMapStatic.claims capacity era.kernelMap) fixed gen era cpu).trans
      ((KernelMapStatic.nativeSpec capacity).lookup era.kernelMap vpn permission classified)

end Xv6.Kernel.HardwareConfig
