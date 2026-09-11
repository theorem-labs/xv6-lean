import MachCSL.Machine.JalLoopPlanCycle
import MachCSL.Machine.JalLoopPlanFetch
import MachCSL.Machine.BootPmpPlan

/-! Fetch decomposition at the actual universal static reset facts. PMP checks
form an explicit event-plan boundary, supplied by the actual OFF-only PMP proof. -/
namespace MachCSL.Machine.JalLoopPlan
open MachCSL.Logic.EventWP LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def accessSnapshot : JalLoop.Snapshot
  | .pma_regions => some pmaBoot
  | .mstatus => some 0xA00000000#64
  | .cur_privilege => some .Machine
  | .misa => some 0x800000000014112d#64
  | .htif_tohost_base => some none
  | .PC => some jalImage.vector
  | _ => none

private theorem accessSnapshot_covers (rs : RegisterFile) (static : Static rs) :
    JalLoop.Covers accessSnapshot rs := by
  intro r value found
  cases r <;> simp only [accessSnapshot, Option.some.injEq] at found
  all_goals first | contradiction | subst value
  · exact static.pma
  · exact static.htif
  · exact static.pc
  · exact static.mstatus
  · exact static.misa
  · exact static.privilege

private def codeAccessInfo : Phys_Mem_Access_Info := ⟨.CannotSplit, 0⟩

private theorem pma_checked :
    snapshotPlanRun (fun _ _ => none) accessSnapshot 100
      (pmaCheck (.Physaddr jalImage.vector) 4 (.InstructionFetch ()) .PBMT_PMA false) =
      some (.Ok codeAccessInfo) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem translate_checked :
    snapshotPlanRun (fun _ _ => none) accessSnapshot 100
      (translateAddr (.Virtaddr jalImage.vector) (.InstructionFetch ())) =
      some (.Ok (.Physaddr jalImage.vector, .PBMT_PMA, ())) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem mmio_checked :
    snapshotPlanRun (fun _ _ => none) accessSnapshot 100
      (within_mmio_readable (.Physaddr jalImage.vector) 4) = some false := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem pma_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static rs) :
    Returns reads rs (pmaCheck (.Physaddr jalImage.vector) 4 (.InstructionFetch ()) .PBMT_PMA false)
      (.Ok codeAccessInfo) rs :=
  snapshotPlanRun_plan reads (fun _ _ => none) (fun _ _ _ h => by cases h)
    accessSnapshot rs (accessSnapshot_covers rs static) _ _ _ pma_checked

theorem translate_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static rs) :
    Returns reads rs (translateAddr (.Virtaddr jalImage.vector) (.InstructionFetch ()))
      (.Ok (.Physaddr jalImage.vector, .PBMT_PMA, ())) rs :=
  snapshotPlanRun_plan reads (fun _ _ => none) (fun _ _ _ h => by cases h)
    accessSnapshot rs (accessSnapshot_covers rs static) _ _ _ translate_checked

private theorem mmio_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static rs) :
    Returns reads rs (within_mmio_readable (.Physaddr jalImage.vector) 4) false rs :=
  snapshotPlanRun_plan reads (fun _ _ => none) (fun _ _ _ h => by cases h)
    accessSnapshot rs (accessSnapshot_covers rs static) _ _ _ mmio_checked

private theorem pma_priority_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static rs) :
    Returns reads rs (check_pma_with_pmp_priority (.InstructionFetch ()) .PBMT_PMA .Machine
      (.Physaddr jalImage.vector) 4 false) (.Ok codeAccessInfo) rs := by
  unfold check_pma_with_pmp_priority
  refine (pma_plan reads rs static).bind ?_
  exact pure_plan reads rs _

theorem read_ram_plan (rs : RegisterFile) :
    Returns CodeRead rs (read_ram .Read_plain (.Physaddr jalImage.vector) 4 false) (0x6f#32, ()) rs := by
  apply ExecPlan.readMem (word := 0x6f#32) (by decide) (by decide) ⟨rfl, rfl, rfl⟩
  exact pure_plan CodeRead rs _

theorem checked_mem_read_plan (rs : RegisterFile) (static : Static rs)
    (pmp : Returns CodeRead rs
      (pmpCheck (.Physaddr jalImage.vector) 4 (.InstructionFetch ()) .Machine) none rs) :
    Returns CodeRead rs
      (checked_mem_read (.InstructionFetch ()) .PBMT_PMA .Machine
        (.Physaddr jalImage.vector) 4 false false false false) (.Ok (0x6f#32, ())) rs := by
  unfold checked_mem_read _root_.Sail.SailME.run PreSail.PreSailME.run
  refine Returns.bind (value := Except.ok (.Ok (0x6f#32, ()))) ?_
    (pure_plan CodeRead rs _)
  apply Returns.exceptBind (middle := rs) (a := codeAccessInfo)
  · refine ((pma_priority_plan CodeRead rs static).liftExcept
      (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))).bind ?_
    exact pure_plan CodeRead rs _
  refine Returns.exceptBind (middle := rs) (a := ((1, 4) : Int × Int))
    (pure_plan CodeRead rs _) ?_
  refine Returns.exceptBind (middle := rs) (a := read_kind.Read_plain)
    (pure_plan CodeRead rs _) ?_
  refine Returns.exceptBind (middle := rs) (a := (0x6f#32, true, (0 : Nat))) ?_
    (pure_plan CodeRead rs _)
  refine Returns.exceptBind (middle := rs) (a := (0x6f#32, true, (0 : Nat))) ?_
    (pure_plan CodeRead rs _)
  simp only [untilFuelM]
  refine Returns.exceptBind (middle := rs) (a := (0x6f#32, true, (0 : Nat))) ?_
    (pure_plan CodeRead rs _)
  refine (pmp.liftExcept
    (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))).bind ?_
  refine ((mmio_plan CodeRead rs static).liftExcept
    (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))).bind ?_
  simp only [ExceptT.bindCont]
  refine Returns.exceptBind (middle := rs) (a := 0x6f#32) ?_
    (pure_plan CodeRead rs _)
  refine ((read_ram_plan rs).liftExcept
    (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))).bind ?_
  exact pure_plan CodeRead rs _

theorem mem_read_plan (rs : RegisterFile) (static : Static rs) (off : BootPmp.Off rs) :
    Returns CodeRead rs
      (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr jalImage.vector) 4 false false false)
      (.Ok 0x6f#32) rs := by
  unfold mem_read
  refine (read_plan CodeRead rs .mstatus (by decide)).bind ?_
  refine (read_plan CodeRead rs .cur_privilege (by decide)).bind ?_
  rw [static.mstatus, static.privilege]
  unfold effectivePrivilege
  change Returns CodeRead rs
    (mem_read_priv (.InstructionFetch ()) .PBMT_PMA .Machine
      (.Physaddr jalImage.vector) 4 false false false) (.Ok 0x6f#32) rs
  unfold mem_read_priv mem_read_priv_meta
  refine Returns.bind (middle := rs) (value := _root_.Sail.Result.Ok (0x6f#32, ())) ?_
    (pure_plan CodeRead rs _)
  refine (checked_mem_read_plan rs static
    (BootPmp.check_off_plan CodeRead rs off _ _ _)).bind ?_
  exact pure_plan CodeRead rs _

theorem fetch_bytes_plan (rs : RegisterFile) (static : Static rs) (off : BootPmp.Off rs) :
    Returns CodeRead rs (fetch_bytes jalImage.vector jalImage.vector 4)
      (.FetchBytes_Success 0x6f#32) rs := by
  unfold fetch_bytes _root_.Sail.SailME.run PreSail.PreSailME.run
  refine Returns.bind (value := Except.ok (.FetchBytes_Success 0x6f#32)) ?_
    (pure_plan CodeRead rs _)
  refine Returns.exceptBind (middle := rs) (a := (.Physaddr jalImage.vector, page_based_mem_type.PBMT_PMA)) ?_ ?_
  · refine ((translate_plan CodeRead rs static).liftExcept (FetchBytes_Result 4)).bind ?_
    exact pure_plan CodeRead rs _
  · refine ((mem_read_plan rs static off).liftExcept (FetchBytes_Result 4)).bind ?_
    exact pure_plan CodeRead rs _

private theorem zca_checked :
    snapshotPlanRun (fun _ _ => none) accessSnapshot 100 (currentlyEnabled .Ext_Zca) = some true := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem ziccif_checked :
    snapshotPlanRun (fun _ _ => none) accessSnapshot 100 (currentlyEnabled .Ext_Ziccif) = some true := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem zca_plan (rs : RegisterFile) (static : Static rs) :
    Returns CodeRead rs (currentlyEnabled .Ext_Zca) true rs :=
  snapshotPlanRun_plan CodeRead (fun _ _ => none) (fun _ _ _ h => by cases h)
    accessSnapshot rs (accessSnapshot_covers rs static) _ _ _ zca_checked

private theorem ziccif_plan (rs : RegisterFile) (static : Static rs) :
    Returns CodeRead rs (currentlyEnabled .Ext_Ziccif) true rs :=
  snapshotPlanRun_plan CodeRead (fun _ _ => none) (fun _ _ _ h => by cases h)
    accessSnapshot rs (accessSnapshot_covers rs static) _ _ _ ziccif_checked

/-- Actual fetch under every postboot static/OFF family. No PMP address value
or unrelated config bit is fixed, and the four-byte resource contract is exact. -/
theorem universal_fetch_plan [Platform] (rs : RegisterFile) (static : Static rs)
    (off : BootPmp.Off rs) : Returns CodeRead rs (fetch ()) (.F_Base 0x6f#32) rs := by
  unfold fetch _root_.Sail.SailME.run PreSail.PreSailME.run
  refine Returns.bind (value := Except.ok (.F_Base 0x6f#32)) ?_ (pure_plan CodeRead rs _)
  refine (read_plan CodeRead rs .PC (by decide)).bind ?_
  refine (read_plan CodeRead rs .PC (by decide)).bind ?_
  rw [static.pc]
  refine (read_plan CodeRead rs .PC (by decide)).bind ?_
  refine (read_plan CodeRead rs .PC (by decide)).bind ?_
  refine ((zca_plan rs static).liftExcept FetchResult).bind ?_
  rw [static.pc]
  refine (read_plan CodeRead rs .PC (by decide)).bind ?_
  refine ((ziccif_plan rs static).liftExcept FetchResult).bind ?_
  rw [static.pc]
  refine (read_plan CodeRead rs .PC (by decide)).bind ?_
  refine (read_plan CodeRead rs .PC (by decide)).bind ?_
  rw [static.pc]
  refine ((fetch_bytes_plan rs static off).liftExcept FetchResult).bind ?_
  exact pure_plan CodeRead rs _

end MachCSL.Machine.JalLoopPlan
