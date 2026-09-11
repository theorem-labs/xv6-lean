import MachCSL.Machine.SpinlockAccessDefs

namespace MachCSL.Machine.SpinlockAccess
open LeanPaperStock.Functions MachCSL.Logic.EventWP JalLoopPlan
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem Static.ofBoot (rs : RegisterFile) (vector : BitVec 64)
    (boot : BootUniversal.StaticBoot vector rs) : Static rs :=
  ⟨boot.misa, boot.mstatus, boot.menvcfg, boot.mseccfg, boot.privilege, boot.pma, boot.htif⟩

private def staticSnapshot : JalLoop.Snapshot
  | .misa => some 0x800000000014112d#64
  | .mstatus => some 0xA00000000#64
  | .menvcfg => some 0#64
  | .mseccfg => some 0#64
  | .cur_privilege => some .Machine
  | .pma_regions => some pmaBoot
  | .htif_tohost_base => some none
  | _ => none

private def addressSnapshot : JalLoop.Snapshot
  | .x10 => some SpinlockImage.lockAddress
  | r => staticSnapshot r

private theorem staticSnapshot_covers (rs : RegisterFile) (static : Static rs) :
    JalLoop.Covers staticSnapshot rs := by
  intro r value found
  cases r <;> simp only [staticSnapshot, Option.some.injEq] at found
  all_goals first | contradiction | subst value
  all_goals first | exact static.pma | exact static.htif | exact static.menvcfg | exact static.mseccfg | exact static.mstatus | exact static.misa | exact static.privilege

private theorem addressSnapshot_covers (rs : RegisterFile) (static : Static rs)
    (base : rs .x10 = SpinlockImage.lockAddress) : JalLoop.Covers addressSnapshot rs := by
  intro r value found
  cases r <;> simp only [addressSnapshot, staticSnapshot, Option.some.injEq] at found
  all_goals first | contradiction | subst value
  all_goals first | exact base | exact static.pma | exact static.htif | exact static.menvcfg | exact static.mseccfg | exact static.mstatus | exact static.misa | exact static.privilege

private theorem pma_checked (location : Location) (mode : Mode) :
    snapshotPlanRun (fun _ _ => none) staticSnapshot 1000
      (pmaCheck (.Physaddr (address location)) 4 (access mode) .PBMT_PMA mode.exclusive) =
      some (.Ok accessInfo) := by
  cases location <;> cases mode
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem translate_checked (location : Location) (mode : Mode) :
    snapshotPlanRun (fun _ _ => none) staticSnapshot 1000
      (translateAddr (.Virtaddr (address location)) (access mode)) =
      some (.Ok (.Physaddr (address location), .PBMT_PMA, ())) := by
  cases location <;> cases mode
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem transform_checked (location : Location) (mode : Mode) :
    snapshotPlanRun (fun _ _ => none) addressSnapshot 1000
      (get_transformed_data_addr (.Regidx 10#5) (offset location) (access mode) 4) =
      some (.Ext_DataAddr_OK (.Virtaddr (address location))) := by
  cases location <;> cases mode
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem readable_checked (location : Location) :
    snapshotPlanRun (fun _ _ => none) staticSnapshot 1000
      (within_mmio_readable (.Physaddr (address location)) 4) = some false := by
  cases location
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem writable_checked (location : Location) :
    snapshotPlanRun (fun _ _ => none) staticSnapshot 1000
      (within_mmio_writable (.Physaddr (address location)) 4) = some false := by
  cases location
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

theorem pma_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static rs)
    (location : Location) (mode : Mode) :
    Returns reads rs
      (pmaCheck (.Physaddr (address location)) 4 (access mode) .PBMT_PMA mode.exclusive)
      (.Ok accessInfo) rs :=
  snapshotPlanRun_plan reads (fun _ _ => none) (fun _ _ _ h => by cases h)
    staticSnapshot rs (staticSnapshot_covers rs static) _ _ _ (pma_checked location mode)

theorem translate_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static rs)
    (location : Location) (mode : Mode) :
    Returns reads rs (translateAddr (.Virtaddr (address location)) (access mode))
      (.Ok (.Physaddr (address location), .PBMT_PMA, ())) rs :=
  snapshotPlanRun_plan reads (fun _ _ => none) (fun _ _ _ h => by cases h)
    staticSnapshot rs (staticSnapshot_covers rs static) _ _ _ (translate_checked location mode)

theorem transform_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static rs)
    (base : rs .x10 = SpinlockImage.lockAddress) (location : Location) (mode : Mode) :
    Returns reads rs (get_transformed_data_addr (.Regidx 10#5) (offset location) (access mode) 4)
      (.Ext_DataAddr_OK (.Virtaddr (address location))) rs :=
  snapshotPlanRun_plan reads (fun _ _ => none) (fun _ _ _ h => by cases h)
    addressSnapshot rs (addressSnapshot_covers rs static base) _ _ _ (transform_checked location mode)

theorem readable_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static rs)
    (location : Location) :
    Returns reads rs (within_mmio_readable (.Physaddr (address location)) 4) false rs :=
  snapshotPlanRun_plan reads (fun _ _ => none) (fun _ _ _ h => by cases h)
    staticSnapshot rs (staticSnapshot_covers rs static) _ _ _ (readable_checked location)

theorem writable_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static rs)
    (location : Location) :
    Returns reads rs (within_mmio_writable (.Physaddr (address location)) 4) false rs :=
  snapshotPlanRun_plan reads (fun _ _ => none) (fun _ _ _ h => by cases h)
    staticSnapshot rs (staticSnapshot_covers rs static) _ _ _ (writable_checked location)

theorem pmp_plan (reads : ReadAllowed) (rs : RegisterFile) (off : BootPmp.Off rs)
    (location : Location) (mode : Mode) :
    Returns reads rs (pmpCheck (.Physaddr (address location)) 4 (access mode) .Machine) none rs :=
  BootPmp.check_off_plan reads rs off _ _ _

theorem pma_priority_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static rs)
    (location : Location) (mode : Mode) :
    Returns reads rs
      (check_pma_with_pmp_priority (access mode) .PBMT_PMA .Machine
        (.Physaddr (address location)) 4 mode.exclusive) (.Ok accessInfo) rs := by
  unfold check_pma_with_pmp_priority
  refine (pma_plan reads rs static location mode).bind ?_
  exact pure_plan reads rs _

theorem address_aligned (location : Location) :
    is_aligned_vaddr (.Virtaddr (address location)) 4 = true := by
  cases location
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

theorem read_request_ram (location : Location) (exclusive : Bool) :
    deviceAddress (readRequest location exclusive).pa = false := by
  cases location <;> cases exclusive
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

theorem read_request_exclusive (location : Location) (exclusive : Bool) :
    accessExclusive (readRequest location exclusive).access_kind = exclusive := by
  cases exclusive <;> rfl

theorem write_request_ram (location : Location) (exclusive : Bool) (word : BitVec 32) :
    deviceAddress (writeRequest location exclusive word).pa = false := by
  cases location <;> cases exclusive
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

theorem write_request_exclusive (location : Location) (exclusive : Bool) (word : BitVec 32) :
    accessExclusive (writeRequest location exclusive word).access_kind = exclusive := by
  cases exclusive <;> rfl

/-- The generated effective-address announcement checks real PMA/PMP and
emits no memory-write event: `write_ram_ea` is the actual pure builtin. -/
theorem write_ea_plan (reads : ReadAllowed) (rs : RegisterFile) (static : Static rs)
    (off : BootPmp.Off rs) (location : Location) (mode : Mode) :
    Returns reads rs
      (mem_write_ea (.Physaddr (address location)) 4 (access mode) .PBMT_PMA
        false false mode.exclusive) (.Ok ()) rs := by
  have hpma := pma_priority_plan reads rs static location mode
  have hpmp := pmp_plan reads rs off location mode
  have hkind : Returns reads rs (write_kind_of_flags false false mode.exclusive)
      (writeKind mode.exclusive) rs := by
    cases mode <;> exact pure_plan reads rs _
  cases location <;> cases mode
  all_goals
    with_unfolding_all
      unfold mem_write_ea _root_.Sail.SailME.run _root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.PreSailME.run
      refine Returns.bind (value := Except.ok (.Ok ())) ?_ (pure_plan reads rs _)
      refine (read_plan reads rs .mstatus (by decide)).bind ?_
      refine (read_plan reads rs .cur_privilege (by decide)).bind ?_
      rw [static.mstatus, static.privilege]
      unfold effectivePrivilege
      refine Returns.exceptBind (middle := rs) (a := accessInfo) ?_ ?_
      · refine (hpma.liftExcept
          (_root_.Sail.Result Unit (physaddr × ExceptionType))).bind ?_
        exact pure_plan reads rs _
      refine Returns.exceptBind (middle := rs) (a := ((1, 4) : Int × Int))
        (pure_plan reads rs _) ?_
      refine Returns.exceptBind (hkind.liftExcept (_root_.Sail.Result Unit (physaddr × ExceptionType))) ?_
      refine Returns.exceptBind (middle := rs) (a := ((true, 0) : Bool × Nat)) ?_
        (pure_plan reads rs _)
      simp only [untilFuelM]
      refine Returns.exceptBind (middle := rs) (a := ((true, 0) : Bool × Nat)) ?_
        (pure_plan reads rs _)
      refine (hpmp.liftExcept
        (_root_.Sail.Result Unit (physaddr × ExceptionType))).bind ?_
      exact pure_plan reads rs _

end MachCSL.Machine.SpinlockAccess
