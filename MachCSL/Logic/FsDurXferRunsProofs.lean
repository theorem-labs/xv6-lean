import MachCSL.Logic.FsDurXferRunsPureProofs
import MachCSL.Logic.FsDurBytesLedgerProofs

namespace MachCSL.Logic.FsDurXferRuns
open Iris Iris.Std Iris.BI Iris.CMRA MachCSL.Memory
variable {GF : BundledGFunctors} (view : FsView.View GF)

theorem phi_map_q_of_range dq run :
    FsView.byteRangeQ view dq (runBlock run) (runOffset run) (runBytes run) ⊣⊢ phiMapQ view dq (runMap run) := by
  have law := BigSepM.bigSepM_map_seqZ (M' := Disk.ImageMap)
    (Φ := fun a v => view.phi dq a v) (start := runBlock run * 1024 + runOffset run) (l := runBytes run)
  exact law.symm

theorem phi_map_of_range run :
    FsView.byteRange view (runBlock run) (runOffset run) (runBytes run) ⊣⊢ phiMap view (runMap run) :=
  phi_map_q_of_range view (.own 1) run

theorem phi_runs_nil : phiRuns view [] ⊣⊢ emp := .rfl
theorem phi_runs_cons_range run runs : phiRuns view (run :: runs) ⊣⊢
    FsView.byteRange view (runBlock run) (runOffset run) (runBytes run) ∗ phiRuns view runs := .rfl

theorem phi_runs_cons run runs : phiRuns view (run :: runs) ⊣⊢ phiMap view (runMap run) ∗ phiRuns view runs := by
  rw [(phi_runs_cons_range view run runs).to_eq, (phi_map_of_range view run).to_eq]
  exact .rfl

theorem phi_runs_app left right : phiRuns view (left ++ right) ⊣⊢ phiRuns view left ∗ phiRuns view right := by
  unfold phiRuns
  exact BigSepL.bigSepL_append

theorem phi_runs_q_cons run runs : phiRunsQ view (run :: runs) ⊣⊢
    FsView.byteRangeQ view run.1 (runBlock run.2) (runOffset run.2) (runBytes run.2) ∗ phiRunsQ view runs := .rfl

theorem phi_runs_q_at dq runs : phiRunsQ view (atShare dq runs) ⊣⊢ phiRuns (FsView.gammaQ view dq) runs := by
  unfold phiRunsQ atShare phiRuns
  rw [BigSepL.bigSepL_map]
  exact .rfl

theorem phi_map_disj_q (exclusive : FsView.PhiExcl view) (dq1 dq2 : DFrac) left right
    (invalid : ¬✓ (dq1 • dq2)) :
    phiMapQ view dq1 left ∗ phiMapQ view dq2 right ⊢ ⌜PartialMap.disjoint (M := Disk.ImageMap) left right⌝ := by
  unfold PartialMap.disjoint phiMapQ
  iintro ⟨Hl, Hr⟩
  iapply pure_forall.mpr
  iintro %address
  iapply pure_imp.mpr
  iintro %overlap
  obtain ⟨byte1, found1⟩ := Option.isSome_iff_exists.mp overlap.1
  obtain ⟨byte2, found2⟩ := Option.isSome_iff_exists.mp overlap.2
  ihave H1 := BigSepM.bigSepM_lookup (M := Disk.ImageMap) found1 $$ Hl
  ihave H2 := BigSepM.bigSepM_lookup (M := Disk.ImageMap) found2 $$ Hr
  ihave %valid := exclusive address byte1 byte2 dq1 dq2 $$ [$H1 $H2]
  ipureintro
  exact invalid valid

theorem phi_map_disj (exclusive : FsView.PhiExcl view) left right :
    phiMap view left ∗ phiMap view right ⊢ ⌜PartialMap.disjoint (M := Disk.ImageMap) left right⌝ :=
  phi_map_disj_q view exclusive (.own 1) (.own 1) left right (dfrac_full_pair _)

theorem phi_runs_q_disj (exclusive : FsView.PhiExcl view) runs (ok : SharesOK runs) :
    phiRunsQ view runs ⊢ ⌜RunsDisjoint (strip runs)⌝ := by
  iintro H
  unfold RunsDisjoint
  iapply pure_forall.mpr
  iintro %k
  iapply pure_forall.mpr
  iintro %j
  iapply pure_forall.mpr
  iintro %r1
  iapply pure_forall.mpr
  iintro %r2
  iapply pure_imp.mpr
  iintro %different
  iapply pure_imp.mpr
  iintro %getK
  iapply pure_imp.mpr
  iintro %getJ
  rw [strip, List.getElem?_map, Option.map_eq_some_iff] at getK getJ
  obtain ⟨q1, found1, rfl⟩ := getK
  obtain ⟨q2, found2, rfl⟩ := getJ
  unfold phiRunsQ
  ihave ⟨H1, Hrest⟩ := (BigSepL.bigSepL_delete_cond found1).mp $$ H
  ihave H2 := BigSepL.bigSepL_lookup found2 $$ Hrest
  rw [if_neg different.symm]
  have law := phi_map_disj_q view exclusive q1.1 q2.1 (runMap q1.2) (runMap q2.2)
    (dfrac_nvalid_pair q1.1 q2.1 (ok k q1 found1) (ok j q2 found2))
  rw [← (phi_map_q_of_range view q1.1 q1.2).to_eq, ← (phi_map_q_of_range view q2.1 q2.2).to_eq] at law
  iapply law $$ [$H1 $H2]

theorem phi_runs_disj (exclusive : FsView.PhiExcl view) runs : phiRuns view runs ⊢ ⌜RunsDisjoint runs⌝ := by
  have law := phi_runs_q_disj view exclusive (atShare (.own 1) runs)
    (sharesOK_atShare (.own 1) runs (dfrac_full_pair _))
  rw [strip_atShare] at law
  have eq : phiRunsQ view (atShare (.own 1) runs) = phiRuns view runs := by
    rw [(phi_runs_q_at view (.own 1) runs).to_eq]
    rfl
  rwa [eq] at law

theorem phi_runs_union runs (disjoint : RunsDisjoint runs) : phiRuns view runs ⊣⊢ phiMap view (runUnion runs) := by
  induction runs with
  | nil => exact .rfl
  | cons run runs ih =>
    rw [(phi_runs_cons view run runs).to_eq, (ih ((runsDisjoint_cons run runs).mp disjoint).1).to_eq, runUnion_cons]
    exact (FsDurBytes.byteLedger_union view _ _ (runsDisjoint_head run runs disjoint)).symm

theorem phi_map_q_in authority bytes (agree : PhiAgree view authority bytes) dq owned :
    authority ∗ phiMapQ view dq owned ⊢ ⌜PartialMap.submap (M := Disk.ImageMap) owned bytes⌝ := by
  unfold phiMapQ PartialMap.submap
  iintro ⟨Ha, Hm⟩
  iapply pure_forall.mpr
  iintro %address
  iapply pure_forall.mpr
  iintro %byte
  iapply pure_imp.mpr
  iintro %found
  ihave Hbyte := BigSepM.bigSepM_lookup (M := Disk.ImageMap) found $$ Hm
  iapply agree dq address byte $$ [$Ha $Hbyte]

theorem phi_map_in authority bytes (agree : PhiAgree view authority bytes) owned :
    authority ∗ phiMap view owned ⊢ ⌜PartialMap.submap (M := Disk.ImageMap) owned bytes⌝ :=
  phi_map_q_in view authority bytes agree (.own 1) owned

theorem phi_runs_in authority bytes (agree : PhiAgree view authority bytes) runs (disjoint : RunsDisjoint runs) :
    authority ∗ phiRuns view runs ⊢ ⌜PartialMap.submap (M := Disk.ImageMap) (runUnion runs) bytes⌝ := by
  rw [(phi_runs_union view runs disjoint).to_eq]
  exact phi_map_in view authority bytes agree _

theorem phi_runs_q_in authority bytes (agree : PhiAgree view authority bytes) runs :
    authority ∗ phiRunsQ view runs ⊢ ⌜PartialMap.submap (M := Disk.ImageMap) (runUnion (strip runs)) bytes⌝ := by
  iintro ⟨Ha, Hr⟩
  unfold PartialMap.submap
  iapply pure_forall.mpr
  iintro %address
  iapply pure_forall.mpr
  iintro %byte
  iapply pure_imp.mpr
  iintro %found
  obtain ⟨k, run, get, inMap⟩ := runUnion_lookup (strip runs) address byte found
  rw [strip, List.getElem?_map, Option.map_eq_some_iff] at get
  obtain ⟨qrun, get, rfl⟩ := get
  unfold phiRunsQ
  ihave Hrun := BigSepL.bigSepL_lookup get $$ Hr
  have law := phi_map_q_in view authority bytes agree qrun.1 (runMap qrun.2)
  rw [← (phi_map_q_of_range view qrun.1 qrun.2).to_eq] at law
  ihave %subset := law $$ [$Ha $Hrun]
  ipureintro
  exact subset address byte inMap

theorem runSpec : RunSpec view where
  disjoint runs exclusive := phi_runs_disj view exclusive runs
  union := phi_runs_union view
  included authority bytes runs agree := phi_runs_in view authority bytes agree runs
  mixedDisjoint runs exclusive := phi_runs_q_disj view exclusive runs
  mixedIncluded authority bytes runs agree := phi_runs_q_in view authority bytes agree runs

/-- The existing native snapshot byte authority supplies source agreement. -/
theorem snap_gamma_agree (capacity : Disk.Capacity GF) g gl gt bytes :
    PhiAgree (FsView.snapGamma capacity g gl gt) (Disk.mapAuth capacity g bytes) bytes := by
  letI := capacity.image
  intro dq address byte
  unfold Disk.mapAuth FsView.snapGamma
  iintro ⟨Ha, Hb⟩
  iapply ghost_map_lookup (H := Disk.ImageMap) (GF := GF) $$ Ha Hb

end MachCSL.Logic.FsDurXferRuns
