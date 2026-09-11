import Xv6.Kernel.SconfDefs
import Xv6.Kernel.SupervisorTranslationDefs

/-! Exact disabled specialization of IntrDefs.sie_cap/sie_cap_gpr.
The source's process-pointer argument is unused at b=false and is omitted.
There is no enabled-arm placeholder or handler-correctness predicate. -/
namespace Xv6.Kernel.SieOffCapability
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev Tier := KernelDatum.Tier
abbrev File := HartTp.GprFile

def sp (file : File) : BitVec 64 := file 2#5
/-- Source trap_res false=0. No enabled reserve size is postulated here. -/
def trapReserve : Nat := 0

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Source sr_ktier_wit(strans_regime): identity claims cost no additional
receipt; full-tier access requires the real per-hart publication receipt. -/
def tierWitness (era : Era.Record) (cpu : CPU) : Tier → IProp GF
  | .identity => iprop(emp)
  | .full => SupervisorTranslation.kptOn capacity.translation era cpu

abbrev running (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId) : IProp GF :=
  TsoContextReadWP.running capacity.machine era cpu ξ
abbrev off (era : Era.Record) (cpu : CPU) : IProp GF :=
  SupervisorBits.offToken capacity.supervisorBits (SupervisorBits.namesOfEra era cpu)
abbrev stack (era : Era.Record) (tier : Tier) (ξ : TsoContext.CtxId)
    (pointer : BitVec 64) (n : Nat) : IProp GF :=
  KernelStack.own capacity.translation era tier ξ pointer n
abbrev active (era : Era.Record) (cpu : CPU) : IProp GF :=
  Sconf.cell capacity era cpu .hart_state (.HART_ACTIVE ())

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable abbrev timer (era : Era.Record) (cpu : CPU) : IProp GF :=
  TimerCap.capability capacity.machine.era.registers era cpu

/-- Exactly the five non-stack conjuncts. This explicit remainder is kept
through stack movement and contains the real same-hart translation slot. -/
noncomputable def rest (era : Era.Record) (cpu : CPU) (tier : Tier)
    (ξ : TsoContext.CtxId) : IProp GF :=
  iprop(SupervisorTranslation.sourceSlot capacity.translation era cpu ∗ off capacity era cpu ∗
    running capacity era cpu ξ ∗ timer capacity era cpu ∗ tierWitness capacity era cpu tier)

noncomputable def cap (era : Era.Record) (cpu : CPU) (tier : Tier)
    (ξ : TsoContext.CtxId) (file : File) (available : Nat) : IProp GF :=
  iprop(stack capacity era tier ξ (sp file) (trapReserve + available) ∗ rest capacity era cpu tier ξ)

noncomputable def gpr (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId) (file : File) (available : Nat) : IProp GF :=
  iprop(active capacity era cpu ∗ Sconf.sconf capacity fixed gen era cpu ∗
    cap capacity era cpu tier ξ file available ∗
    HartTp.pinnedFile capacity.machine.era.registers era cpu file)

noncomputable def gprAt (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId) (ms : BitVec 64)
    (file : File) (available : Nat) : IProp GF :=
  iprop(active capacity era cpu ∗ Sconf.sconfAt capacity fixed gen era cpu ms ∗
    cap capacity era cpu tier ξ file available ∗
    HartTp.pinnedFile capacity.machine.era.registers era cpu file)

end Xv6.Kernel.SieOffCapability
