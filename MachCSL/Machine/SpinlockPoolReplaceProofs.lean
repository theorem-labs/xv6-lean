import MachCSL.Machine.SpinlockPoolHartFrames

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.SpinlockProtocol

theorem cursors_replace_hart {left right : Pool} {g g' : State} {gen : Nat} {cpu : CPU}
    {program program' : SailM Unit} {c c' : Cursor} {w w' : Words}
    (shape : Shape (left ++ (.hart gen cpu program, .hart c) :: right) g)
    (live : ThreadLive g gen) (frame : HartFrame g g' cpu)
    (old : LiveCursors (left ++ (.hart gen cpu program, .hart c) :: right) g w)
    (control : CursorControl g' cpu program' c') (phase : PhaseOK g' w' cpu c')
    (owners : OtherOwners w w' cpu) :
    LiveCursors (left ++ (.hart gen cpu program', .hart c') :: right) g' w' := by
  intro generation other residual cursor member active
  have activeOld : ThreadLive g generation := by
    simpa only [ThreadLive, frame.power, frame.generation] using active
  have sameGeneration : generation = gen := activeOld.2.symm.trans live.2
  subst generation
  rcases List.mem_append.mp member with inLeft | selectedOrRight
  · have different := context_different_cpu shape live (List.mem_append_left right inLeft)
    obtain ⟨oldControl, oldPhase⟩ := old gen other residual cursor (List.mem_append_left _ inLeft) activeOld
    exact ⟨control_other frame different oldControl, phase_other frame different owners oldPhase⟩
  · rcases List.mem_cons.mp selectedOrRight with selected | inRight
    · have sameCursor : cursor = c' := Label.hart.inj (congrArg Prod.snd selected)
      have sameExpr := Expr.hart.inj (congrArg Prod.fst selected)
      obtain ⟨_, rfl, rfl⟩ := sameExpr
      subst cursor
      exact ⟨control, phase⟩
    · have different := context_different_cpu shape live (List.mem_append_right left inRight)
      obtain ⟨oldControl, oldPhase⟩ :=
        old gen other residual cursor (List.mem_append_right _ (List.mem_cons_of_mem _ inRight)) activeOld
      exact ⟨control_other frame different oldControl, phase_other frame different owners oldPhase⟩

theorem owner_replace_hart {left right : Pool} {g g' : State} {gen : Nat} {cpu : CPU}
    {program program' : SailM Unit} {c c' : Cursor} {w w' : Words}
    (live : ThreadLive g gen) (frame : HartFrame g g' cpu)
    (old : OwnerPresent (left ++ (.hart gen cpu program, .hart c) :: right) g w)
    (selected : ∀ B, w'.owner = some (cpu, B) → HolderPosition c'.phase = some B)
    (back : OtherOwnersBack w w' cpu) :
    OwnerPresent (left ++ (.hart gen cpu program', .hart c') :: right) g' w' := by
  intro other B owner
  by_cases same : other = cpu
  · subst other
    refine ⟨program', c', ?_, selected B owner⟩
    rw [frame.generation, live.2]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  · obtain ⟨residual, cursor, member, held⟩ := old other B (back other B same owner)
    refine ⟨residual, cursor, ?_, held⟩
    rw [frame.generation]
    rcases List.mem_append.mp member with inLeft | selectedOrRight
    · exact List.mem_append_left _ inLeft
    · rcases List.mem_cons.mp selectedOrRight with equal | inRight
      · have sameExpr := Expr.hart.inj (congrArg Prod.fst equal)
        exact False.elim (same sameExpr.2.1)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ inRight)

/-- Assemble the whole pool invariant from concrete selected-hart effects and
the proved other-hart frame. The resource-free owner equalities are discharged
by each event's explicit effect record, never assumed by the final Covers rule. -/
theorem pool_replace_hart [Platform] {left right : Pool} {g g' : State} {gen : Nat} {cpu : CPU}
    {program program' : SailM Unit} {c c' : Cursor} {w w' : Words}
    (inv : PoolInv (left ++ (.hart gen cpu program, .hart c) :: right, g))
    (live : ThreadLive g gen)
    (oldCursors : LiveCursors (left ++ (.hart gen cpu program, .hart c) :: right) g w)
    (oldOwner : OwnerPresent (left ++ (.hart gen cpu program, .hart c) :: right) g w)
    (step : Step SpinlockImage.image (.hart gen cpu program) g [] (.hart gen cpu program') g' [])
    (control : CursorControl g' cpu program' c') (phase : PhaseOK g' w' cpu c')
    (words : WordsOK g' w') (devices : g'.devices = g.devices)
    (code : SpinlockCodeIntegrity.CodeUnwritten g'.log)
    (owners : OtherOwners w w' cpu) (back : OtherOwnersBack w w' cpu)
    (selected : ∀ B, w'.owner = some (cpu, B) → HolderPosition c'.phase = some B) :
    PoolInv (left ++ (.hart gen cpu program', .hart c') :: right, g') := by
  have frame := live_hart_frame live step
  refine ⟨shape_replace_hart inv.1 frame.generation frame.power, ?_⟩
  intro on
  obtain ⟨memory, reservations, image, reset, _, _, _, _, _⟩ := inv.2 live.1
  refine ⟨step_memory_ok _ _ _ _ _ _ _ memory step,
    step_reservations_ok _ _ _ _ _ _ _ reservations step,
    frame.image.trans image, ?_, code, w', words,
    cursors_replace_hart inv.1 live frame oldCursors control phase owners,
    owner_replace_hart live frame oldOwner selected back⟩
  simpa only [ResetVirtio, devices] using reset

end MachCSL.Machine.SpinlockPool
