import MachCSL.Logic.InvariantSpec
import Iris.ProgramLogic.Adequacy

namespace MachCSL.Logic.Invariant
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI
open HeapView DisjointLeibnizSet Iris.Std.PartialMap Iris.Std.LawfulPartialMap

variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem native_preS (names : Names) : (names.native capacity).toInvGpreS = capacity.preS := rfl
theorem native_world (names : Names) : (names.native capacity).toWsatGS.inv = capacity.world := rfl
theorem native_enabled (names : Names) : (names.native capacity).toWsatGS.enabled = capacity.enabled := rfl
theorem native_disabled (names : Names) : (names.native capacity).toWsatGS.disabled = capacity.disabled := rfl
theorem native_credit (names : Names) : (names.native capacity).toLcGS.lc_elem = capacity.credit := rfl

/-- Native `wsat_alloc` and `lc_alloc` construction with the input capacity retained explicitly. -/
theorem allocate (n : Nat) : iprop(⊢ |==> ∃ names : Names, allocated capacity names n) := by
  imod (iOwn_alloc (E := capacity.world) (Auth (.own 1) ∅) auth_one_valid) with ⟨%γ, H⟩
  imod (iOwn_alloc (E := capacity.enabled) (valid ⊤) ⟨⟩) with ⟨%γe, He⟩
  imod (iOwn_alloc (E := capacity.disabled) (valid ∅) ⟨⟩) with ⟨%γd, Hd⟩
  imod (iOwn_alloc (E := capacity.credit) ((● n) • (◯ n))
    (_root_.Auth.auth_both_valid.mpr ⟨fun _ => .rfl, ⟨⟩⟩)) with ⟨%γc, Hc⟩
  icases (iOwn_op (E := capacity.credit)) $$ Hc with ⟨Hauth, Hfrag⟩
  imodintro
  iexists (⟨γ, γe, γd, γc⟩ : Names)
  unfold allocated world enabled creditSupply credits
  iclear Hd
  isplitl [H]
  · unfold wsat
    iexists (∅ : InvMap (IProp GF))
    isplitl [H]
    · have empty : liftInv (∅ : InvMap (IProp GF)) = ∅ := by simp only [liftInv, map_empty]
      rw [invMap, empty]
      iexact H
    · iapply BigSepM.bigSepM_empty
      itrivial
  · unfold ownE lc_supply lc
    iframe He Hauth Hfrag

theorem allocated_native (names : Names) (n : Nat) :
    allocated capacity names n ⊣⊢
      iprop(wsat (W := (names.native capacity).toWsatGS) ∗
        ownE (W := (names.native capacity).toWsatGS) ⊤ ∗
        lc_supply (LC := (names.native capacity).toLcGS) n ∗
        lc (LC := (names.native capacity).toLcGS) n) := .rfl

/-- Allocation retains any already-owned application resources. -/
theorem allocate_frame (n : Nat) (R : IProp GF) :
    iprop(R ⊢ |==> ∃ names : Names, allocated capacity names n ∗ R) := by
  iintro HR
  imod allocate capacity n with ⟨%names, Hworld⟩
  imodintro
  iexists names
  iframe Hworld HR

theorem machineGS_invGS [Platform] (machineCapacity : MachineInterp.Capacity GF)
    (names : Names) (image : Machine.BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Machine.Observation) :
    (machineGS capacity machineCapacity names image fixed whole).invGS = names.native capacity := rfl

theorem machineGS_stateInterp [Platform] (machineCapacity : MachineInterp.Capacity GF)
    (names : Names) (image : Machine.BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Machine.Observation) (g : Machine.State) (steps : Nat)
    (future : List Machine.Observation) (threads : Nat) :
    (machineGS capacity machineCapacity names image fixed whole).stateInterp g steps future threads =
      MachineInterp.stateInterp machineCapacity fixed whole g steps future threads := rfl

theorem machineGS_numLaters [Platform] (machineCapacity : MachineInterp.Capacity GF)
    (names : Names) (image : Machine.BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Machine.Observation) (step : Nat) :
    (machineGS capacity machineCapacity names image fixed whole).numLatersPerStep step = 0 := rfl

/-- Native adequacy still consumes one step credit per step when extra laters are zero. -/
theorem zeroLater_steps_sum (start n : Nat) : Iris.ProgramLogic.steps_sum (fun _ => 0) start n = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [Iris.ProgramLogic.steps_sum, ih, Nat.add_comm]

theorem machineGS_steps_sum [Platform] (machineCapacity : MachineInterp.Capacity GF)
    (names : Names) (image : Machine.BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Machine.Observation) (start n : Nat) :
    Iris.ProgramLogic.steps_sum
      (machineGS capacity machineCapacity names image fixed whole).numLatersPerStep start n = n :=
  zeroLater_steps_sum start n

theorem invariantSpec : InvariantSpec capacity where
  allocate := allocate capacity

end MachCSL.Logic.Invariant
