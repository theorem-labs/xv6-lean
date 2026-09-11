import Xv6.Kernel.SupervisorTranslationDefs

namespace Xv6.Kernel.SupervisorTranslation
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

/-- Native one-shot and arm accessors only. Fresh allocation returns a name;
it cannot allocate ownership at an already supplied era name. No CSR write,
TLB flush, shared-tree publication or boot installation is a premise/result. -/
structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  pending_timeless : ∀ name, Timeless (pendingAt capacity name)
  shot_timeless : ∀ name, Timeless (shotAt capacity name)
  on_timeless : ∀ name, Timeless (onAt capacity name)
  on_persistent : ∀ name, Persistent (onAt capacity name)
  allocate : iprop(⊢ |==> ∃ name, pendingAt capacity name ∗ pendingAt capacity name)
  allocate_fresh : ∀ (P : GName → Prop), (∀ n, ∃ k, n ≤ k ∧ P k) →
    iprop(⊢ |==> ∃ name, ⌜P name⌝ ∗ pendingAt capacity name ∗ pendingAt capacity name)
  halves : ∀ name, iprop(pendingAt capacity name ∗ pendingAt capacity name ⊣⊢ readyAt capacity name)
  flip : ∀ era cpu, iprop(⊢ pending capacity era cpu -∗ pending capacity era cpu ==∗
    shot capacity era cpu ∗ kptOn capacity era cpu)
  receipt : ∀ era cpu, iprop(shot capacity era cpu ⊢ shot capacity era cpu ∗ kptOn capacity era cpu)
  on_pending_false : ∀ era cpu, iprop(⊢ kptOn capacity era cpu -∗ pending capacity era cpu -∗ ⌜False⌝)
  pending_shot_false : ∀ era cpu, iprop(⊢ pending capacity era cpu -∗ shot capacity era cpu -∗ ⌜False⌝)
  shot_exclusive : ∀ era cpu, iprop(⊢ shot capacity era cpu -∗ shot capacity era cpu -∗ ⌜False⌝)
  bare_intro : ∀ era cpu satp, BareSatp satp →
    iprop(⊢ KptResidue.satpCell capacity era cpu satp -∗
      KptResidue.pmpConfig capacity era cpu 0#44 -∗ bare capacity era cpu)
  bare_access : ∀ era cpu, iprop(bare capacity era cpu ⊢ ∃ satp,
    KptResidue.satpCell capacity era cpu satp ∗ ⌜BareSatp satp⌝ ∗
    KptResidue.pmpConfig capacity era cpu 0#44)
  intro_bare : ∀ era cpu (N : Namespace) value,
    iprop(⊢ pending capacity era cpu -∗ bare capacity era cpu -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .stvec (.own 1) value -∗
      slot capacity era cpu N)
  intro_kpt : ∀ era cpu (N : Namespace) root,
    iprop(⊢ shot capacity era cpu -∗ KptResidue.residue capacity era cpu N root -∗ slot capacity era cpu N)
  access_bare : ∀ era cpu (N : Namespace),
    iprop(⊢ pending capacity era cpu -∗ slot capacity era cpu N -∗
      pending capacity era cpu ∗ pending capacity era cpu ∗ bare capacity era cpu ∗ stvec capacity era cpu)
  access_kpt : ∀ era cpu (N : Namespace),
    iprop(⊢ kptOn capacity era cpu -∗ slot capacity era cpu N -∗ ∃ root,
      KptResidue.residue capacity era cpu N root ∗
      (KptResidue.residue capacity era cpu N root -∗ slot capacity era cpu N))

end Xv6.Kernel.SupervisorTranslation
