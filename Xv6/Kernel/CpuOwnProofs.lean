import Xv6.Kernel.CpuOwnResources

namespace Xv6.Kernel.CpuOwn
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem open_own era cpu ξ depth baseEnabled process held :
    iprop(ownOff capacity era cpu ξ depth baseEnabled process held ⊣⊢
      cells capacity era cpu ξ depth baseEnabled process ∗
      LockSet.cpuLevel capacity.heldSets era cpu depth held ∗ hartCsrs capacity era cpu ∗
      count capacity era cpu depth baseEnabled) := by
  unfold ownOff privateState
  exact sep_assoc.trans (sep_congr_right sep_assoc)

theorem init_boot era cpu ξ process noff intena scratch delegation
    (noff_eq : noff = noffValue 0) (delegation_eq : delegation = medelegS) :
    iprop(⊢ word4 capacity era ξ (noffAddress cpu) (.own 1) noff -∗
      word4 capacity era ξ (intenaAddress cpu) (.own 1) intena -∗ off capacity era cpu -∗
      curProc capacity era cpu ξ process -∗ LockSet.cpuLocks capacity.heldSets era cpu ∅ -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .sscratch (.own 1) scratch -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .medeleg .discard delegation -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .mstateen0 .discard 0#64 -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .sstateen0 .discard 0#32 -∗
      ownOff capacity era cpu ξ 0 false process ∅) := by
  subst noff delegation
  iintro Hnoff Hint Hcount Hproc Hlocks Hscratch Hdeleg Hmstate Hsstate
  unfold ownOff privateState cells hartCsrs
  simp only
  iframe Hnoff Hproc Hdeleg Hmstate Hsstate
  isplitl [Hint Hlocks Hscratch]
  · isplitl [Hint]
    · isplit
      · ipureintro; decide
      · iexists intena; iexact Hint
    isplitl [Hlocks]
    · unfold LockSet.cpuLevel
      iunfold LockSet.cpuLocks at Hlocks
      iapply LockSet.level_intro capacity.heldSets (era.heldLocks cpu) 0 ∅ (by simp) $$ Hlocks
    · iexists scratch; iexact Hscratch
  · iapply (count_init capacity era cpu).mp $$ Hcount

/-- The source contradiction uses the actual full first noff byte, even
when the two resources claim different contexts or values. -/
theorem exclusive era cpu ξ ξ' depth depth' baseEnabled baseEnabled' process process' held held' :
    iprop(⊢ ownOff capacity era cpu ξ depth baseEnabled process held -∗
      ownOff capacity era cpu ξ' depth' baseEnabled' process' held' -∗ False) := by
  unfold ownOff privateState cells
  iintro ⟨⟨⟨_,Hnoff,_⟩,_⟩,_⟩ ⟨⟨⟨_,Hnoff',_⟩,_⟩,_⟩
  iunfold word4 at Hnoff Hnoff'
  icases Hnoff with ⟨_,Hbytes⟩
  icases Hnoff' with ⟨_,Hbytes'⟩
  ihave Hbyte := BigSepL.bigSepL_lookup (i := 0) (x := 0) (by rfl) $$ Hbytes
  ihave Hbyte' := BigSepL.bigSepL_lookup (i := 0) (x := 0) (by rfl) $$ Hbytes'
  ihave ⟨Hphys,_⟩ := KernelDatum.identity_access capacity.execution.translation era ξ
    (addressAdd (noffAddress cpu) 0) (.own 1) (nthByte (noffValue depth) 0) $$ Hbyte
  ihave ⟨Hphys',_⟩ := KernelDatum.identity_access capacity.execution.translation era ξ'
    (addressAdd (noffAddress cpu) 0) (.own 1) (nthByte (noffValue depth') 0) $$ Hbyte'
  isimp only [KernelDatum.physicalByte,TsoContext.physPointsto,Tso.physBytePointsto] at Hphys Hphys'
  icases Hphys with ⟨%time,⟨Hraw,_⟩,_⟩
  icases Hphys' with ⟨%time',⟨Hraw',_⟩,_⟩
  letI := capacity.machine.era.heap.ledger.bytes
  ihave %different := ghost_map_elem_ne $$ Hraw Hraw'
  ipureintro
  exact different rfl

theorem bound era cpu ξ depth baseEnabled process held :
    iprop(ownOff capacity era cpu ξ depth baseEnabled process held ⊢
      ⌜depth < 2^31⌝ ∗ ownOff capacity era cpu ξ depth baseEnabled process held) := by
  unfold ownOff privateState cells
  iintro ⟨⟨⟨%bound,Hcells⟩,Hlocks,Hcsrs⟩,Hcount⟩
  iframe Hcells Hlocks Hcsrs Hcount
  ipureintro
  exact ⟨bound,bound⟩

theorem size_le era cpu ξ depth baseEnabled process held :
    iprop(ownOff capacity era cpu ξ depth baseEnabled process held ⊢
      ⌜held.size ≤ depth⌝ ∗ ownOff capacity era cpu ξ depth baseEnabled process held) := by
  unfold ownOff privateState LockSet.cpuLevel LockSet.level
  iintro ⟨⟨Hcells,⟨Hlocks,%size⟩,Hcsrs⟩,Hcount⟩
  iframe Hcells Hlocks Hcsrs Hcount
  ipureintro
  exact ⟨size,size⟩

theorem zero_empty era cpu ξ baseEnabled process held :
    iprop(ownOff capacity era cpu ξ 0 baseEnabled process held ⊢
      ⌜held = ∅⌝ ∗ ownOff capacity era cpu ξ 0 baseEnabled process held) := by
  iintro Hown
  ihave ⟨%size,Hown⟩ := size_le capacity era cpu ξ 0 baseEnabled process held $$ Hown
  iframe Hown
  ipureintro
  exact LockRank.size_le_zero_empty held size

theorem csrs_access era cpu ξ depth baseEnabled process held :
    iprop(ownOff capacity era cpu ξ depth baseEnabled process held ⊢
      hartCsrs capacity era cpu ∗
      (hartCsrs capacity era cpu -∗ ownOff capacity era cpu ξ depth baseEnabled process held)) := by
  unfold ownOff privateState
  iintro ⟨⟨Hcells,Hlocks,Hcsrs⟩,Hcount⟩
  iframe Hcsrs
  iintro Hcsrs
  iframe

theorem proc_access era cpu ξ depth baseEnabled process held :
    iprop(ownOff capacity era cpu ξ depth baseEnabled process held ⊢
      curProc capacity era cpu ξ process ∗
      (∀ replacement : Word, curProc capacity era cpu ξ replacement -∗
        ownOff capacity era cpu ξ depth baseEnabled replacement held)) := by
  unfold ownOff privateState cells
  iintro ⟨⟨⟨Hbound,Hnoff,Hint,Hproc⟩,Hlocks,Hcsrs⟩,Hcount⟩
  iframe Hproc
  iintro %replacement Hproc
  iframe

theorem locks_access era cpu ξ depth baseEnabled process held :
    iprop(ownOff capacity era cpu ξ depth baseEnabled process held ⊢
      LockSet.cpuLocks capacity.heldSets era cpu held ∗ ⌜held.size ≤ depth⌝ ∗
      (∀ replacement : Held, ⌜replacement.size ≤ depth⌝ -∗
        LockSet.cpuLocks capacity.heldSets era cpu replacement -∗
        ownOff capacity era cpu ξ depth baseEnabled process replacement)) := by
  unfold ownOff privateState LockSet.cpuLevel LockSet.level LockSet.cpuLocks
  iintro ⟨⟨Hcells,⟨Hlocks,%size⟩,Hcsrs⟩,Hcount⟩
  iframe Hlocks
  isplit
  · ipureintro; exact size
  iintro %replacement %size' Hlocks
  iframe Hcells Hlocks Hcsrs Hcount
  ipureintro
  exact size'

theorem index_off era cpu ξ depth baseEnabled process held :
    iprop(⊢ off capacity era cpu -∗ ownOff capacity era cpu ξ depth baseEnabled process held -∗
      ⌜(if depth = 0 then baseEnabled else false) = false⌝ ∗
      off capacity era cpu ∗ ownOff capacity era cpu ξ depth baseEnabled process held) := by
  unfold ownOff count off SieOffCapability.off SupervisorBits.offToken
  iintro Hoff ⟨Hprivate,Hcount⟩
  ihave %index := (SupervisorBits.actual capacity.execution.supervisorBits).countIndex
    (SupervisorBits.namesOfEra era cpu) depth baseEnabled false $$ Hoff Hcount
  iframe Hoff Hprivate Hcount
  ipureintro
  exact index

theorem actual : Spec capacity where
  word4_unfold := word4_unfold capacity
  word4_access := word4_access capacity
  open_own := open_own capacity
  init_boot := init_boot capacity
  exclusive := exclusive capacity
  bound := bound capacity
  size_le := size_le capacity
  zero_empty := zero_empty capacity
  csrs_access := csrs_access capacity
  proc_access := proc_access capacity
  locks_access := locks_access capacity
  index_off := index_off capacity
  count_init := count_init capacity
  count_retune := count_retune capacity
  count_push := count_push capacity
  count_pop := count_pop capacity
  count_dec := count_dec capacity
  count_pack := count_pack capacity

end Xv6.Kernel.CpuOwn
