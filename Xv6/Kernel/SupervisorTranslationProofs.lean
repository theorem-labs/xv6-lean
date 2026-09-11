import Xv6.Kernel.SupervisorTranslationSpec

namespace Xv6.Kernel.SupervisorTranslation
open Iris Iris.BI MachCSL.Machine MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance pending_timeless name : Timeless (pendingAt capacity name) := by
  unfold pendingAt; letI := capacity.monoNat name; infer_instance
instance shot_timeless name : Timeless (shotAt capacity name) := by
  unfold shotAt; letI := capacity.monoNat name; infer_instance
instance on_timeless name : Timeless (onAt capacity name) := by
  unfold onAt; letI := capacity.monoNat name; infer_instance
instance on_persistent name : Persistent (onAt capacity name) := by
  unfold onAt; letI := capacity.monoNat name; infer_instance

theorem halves name : iprop(pendingAt capacity name ∗ pendingAt capacity name ⊣⊢ readyAt capacity name) := by
  unfold pendingAt readyAt
  letI := capacity.monoNat name
  have law := Fractional.fractional (Φ := fun q => MonoNat.auth_own (GF := GF) name (.own q) (.ofNat 0))
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at law
  exact law.symm

theorem allocate_fresh (P : GName → Prop) (fresh : ∀ n, ∃ k, n ≤ k ∧ P k) :
    iprop(⊢ |==> ∃ name, ⌜P name⌝ ∗ pendingAt capacity name ∗ pendingAt capacity name) := by
  letI := capacity.monoNat 0
  have alloc : iprop(⊢ |==> ∃ name, ⌜P name⌝ ∗ readyAt capacity name ∗
      @MonoNat.lb_own GF (capacity.monoNat name) name (.ofNat 0)) :=
    MonoNat.own_alloc_strong (GF := GF) P (.ofNat 0) fresh
  imod alloc with ⟨%name, Hpure, Hauth, _⟩
  imodintro
  iexists name
  iframe Hpure
  iapply (halves capacity name).mpr
  iexact Hauth

theorem allocate : iprop(⊢ |==> ∃ name, pendingAt capacity name ∗ pendingAt capacity name) := by
  imod allocate_fresh capacity (fun _ => True) (fun n => ⟨n, Nat.le_refl n, trivial⟩)
    with ⟨%name, _, H1, H2⟩
  imodintro
  iexists name
  iframe

theorem flip era cpu : iprop(⊢ pending capacity era cpu -∗ pending capacity era cpu ==∗
    shot capacity era cpu ∗ kptOn capacity era cpu) := by
  iintro H1 H2
  ihave Hready := (halves capacity (era.supervisorTranslation cpu)).mp $$ [H1 H2]
  · iframe H1 H2
  unfold shot kptOn shotAt onAt
  iunfold readyAt at Hready
  letI := capacity.monoNat (era.supervisorTranslation cpu)
  iapply MonoNat.own_update (era.supervisorTranslation cpu) (.ofNat 0) (.ofNat 1) (show (0 : Nat) ≤ 1 from Nat.zero_le _) $$ Hready

theorem receipt era cpu : iprop(shot capacity era cpu ⊢ shot capacity era cpu ∗ kptOn capacity era cpu) := by
  unfold shot kptOn shotAt onAt
  letI := capacity.monoNat (era.supervisorTranslation cpu)
  iintro Hauth
  ihave #Hreceipt := MonoNat.lb_own_get (era.supervisorTranslation cpu) (.own 1) (.ofNat 1) $$ Hauth
  iframe Hauth Hreceipt

theorem on_pending_false era cpu : iprop(⊢ kptOn capacity era cpu -∗ pending capacity era cpu -∗ ⌜False⌝) := by
  unfold kptOn pending onAt pendingAt
  letI := capacity.monoNat (era.supervisorTranslation cpu)
  iintro Hlb Hauth
  ihave %valid := MonoNat.auth_lb_own_valid (era.supervisorTranslation cpu)
    (.own (1 : Qp).half) (.ofNat 0) (.ofNat 1) $$ Hauth Hlb
  ipureintro
  have impossible : (1 : Nat) ≤ 0 := valid.2
  omega

theorem pending_shot_false era cpu : iprop(⊢ pending capacity era cpu -∗ shot capacity era cpu -∗ ⌜False⌝) := by
  unfold pending shot pendingAt shotAt
  letI := capacity.monoNat (era.supervisorTranslation cpu)
  iintro Hpending Hshot
  ihave %valid := MonoNat.auth_own_agree (era.supervisorTranslation cpu)
    (.own (1 : Qp).half) (.own 1) (.ofNat 0) (.ofNat 1) $$ Hpending Hshot
  ipureintro
  have impossible : (0 : Nat) = 1 := congrArg Iris.MaxNat.toNat valid.2
  omega

theorem shot_exclusive era cpu : iprop(⊢ shot capacity era cpu -∗ shot capacity era cpu -∗ ⌜False⌝) := by
  unfold shot shotAt
  letI := capacity.monoNat (era.supervisorTranslation cpu)
  exact MonoNat.auth_own_exclusive (era.supervisorTranslation cpu) (.ofNat 1) (.ofNat 1)

theorem bare_intro era cpu satp (mode : BareSatp satp) :
    iprop(⊢ KptResidue.satpCell capacity era cpu satp -∗
      KptResidue.pmpConfig capacity era cpu 0#44 -∗ bare capacity era cpu) := by
  unfold bare
  iintro Hsatp Hpmp
  iexists satp
  iframe
  ipureintro
  exact mode

theorem bare_access era cpu : iprop(bare capacity era cpu ⊢ ∃ satp,
    KptResidue.satpCell capacity era cpu satp ∗ ⌜BareSatp satp⌝ ∗
    KptResidue.pmpConfig capacity era cpu 0#44) := .rfl

variable {hlc : HasLC} [InvGS_gen hlc GF]

theorem intro_bare era cpu (N : Namespace) value :
    iprop(⊢ pending capacity era cpu -∗ bare capacity era cpu -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .stvec (.own 1) value -∗
      slot capacity era cpu N) := by
  unfold slot stvec
  iintro Hpending Hbare Hstvec
  ileft
  iframe Hpending Hbare
  iexists value
  iexact Hstvec

theorem intro_kpt era cpu (N : Namespace) root :
    iprop(⊢ shot capacity era cpu -∗ KptResidue.residue capacity era cpu N root -∗ slot capacity era cpu N) := by
  unfold slot
  iintro Hshot Hres
  iright
  iframe Hshot
  iexists root
  iexact Hres

theorem access_bare era cpu (N : Namespace) :
    iprop(⊢ pending capacity era cpu -∗ slot capacity era cpu N -∗
      pending capacity era cpu ∗ pending capacity era cpu ∗ bare capacity era cpu ∗ stvec capacity era cpu) := by
  unfold slot
  iintro Hpending Hslot
  icases Hslot with (Hbare | Hkpt)
  · icases Hbare with ⟨Hpending2, Hbare, Hstvec⟩
    iframe
  · icases Hkpt with ⟨Hshot, _⟩
    ihave %impossible := pending_shot_false capacity era cpu $$ Hpending Hshot
    exact False.elim impossible

theorem access_kpt era cpu (N : Namespace) :
    iprop(⊢ kptOn capacity era cpu -∗ slot capacity era cpu N -∗ ∃ root,
      KptResidue.residue capacity era cpu N root ∗
      (KptResidue.residue capacity era cpu N root -∗ slot capacity era cpu N)) := by
  iintro #Hon Hslot
  iunfold slot at Hslot
  icases Hslot with (Hbare | Hkpt)
  · icases Hbare with ⟨Hpending, _⟩
    ihave %impossible := on_pending_false capacity era cpu $$ Hon Hpending
    exact False.elim impossible
  · icases Hkpt with ⟨Hshot, ⟨%root, Hres⟩⟩
    iexists root
    iframe Hres
    iintro Hres
    iapply intro_kpt capacity era cpu N root $$ Hshot Hres

end Xv6.Kernel.SupervisorTranslation
