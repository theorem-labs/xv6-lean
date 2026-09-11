import Xv6.Kernel.CpuOwnDefs

namespace Xv6.Kernel.CpuOwn
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

structure PureSpec : Prop where
  cpu_address : ∀ cpu, (cpuPointer cpu).toNat = 0x800123e8 + 128 * cpu.val
  noff_address : ∀ cpu, (noffAddress cpu).toNat = 0x800123e8 + 128 * cpu.val + 120
  intena_address : ∀ cpu, (intenaAddress cpu).toNat = 0x800123e8 + 128 * cpu.val + 124
  aligned : ∀ cpu, TsoContextWord.Aligned (procAddress cpu) ∧
    Aligned4 (noffAddress cpu) ∧ Aligned4 (intenaAddress cpu)
  count_unsigned : ∀ depth, depth < 2^31 → (noffValue depth).toNat = depth
  count_signed : ∀ depth, depth < 2^31 → (noffValue depth).toInt = (depth : Int)
  count_injective : ∀ depth depth', depth < 2^31 → depth' < 2^31 →
    noffValue depth = noffValue depth' → depth = depth'

/-- Native resources only. Reconstruction wands are outputs funded by the
opened resources; no caller-supplied restoration predicate, WP, handler or
boot allocation is a premise. Count-only laws do not update physical cells. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  word4_unfold : ∀ era ξ address dq value,
    iprop(word4 capacity era ξ address dq value ⊣⊢
      ⌜Aligned4 address⌝ ∗ [∗list] j ∈ List.range 4,
        KernelDatum.byte capacity.execution.translation era .identity ξ
          (addressAdd address j) dq (nthByte value j))
  word4_access : ∀ era ξ address dq value,
    iprop(word4 capacity era ξ address dq value ⊢
      ⌜Aligned4 address⌝ ∗ TsoContextBytesReadWP.window capacity.machine era ξ address 4 dq value ∗
      (∀ replacement : SmallWord, TsoContextBytesReadWP.window capacity.machine era ξ address 4 dq replacement -∗
        word4 capacity era ξ address dq replacement))
  open_own : ∀ era cpu ξ depth baseEnabled process held,
    iprop(ownOff capacity era cpu ξ depth baseEnabled process held ⊣⊢
      cells capacity era cpu ξ depth baseEnabled process ∗
      LockSet.cpuLevel capacity.heldSets era cpu depth held ∗ hartCsrs capacity era cpu ∗
      count capacity era cpu depth baseEnabled)
  init_boot : ∀ era cpu ξ process noff intena scratch delegation,
    noff = noffValue 0 → delegation = medelegS →
    iprop(⊢ word4 capacity era ξ (noffAddress cpu) (.own 1) noff -∗
      word4 capacity era ξ (intenaAddress cpu) (.own 1) intena -∗ off capacity era cpu -∗
      curProc capacity era cpu ξ process -∗ LockSet.cpuLocks capacity.heldSets era cpu ∅ -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .sscratch (.own 1) scratch -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .medeleg .discard delegation -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .mstateen0 .discard 0#64 -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .sstateen0 .discard 0#32 -∗
      ownOff capacity era cpu ξ 0 false process ∅)
  exclusive : ∀ era cpu ξ ξ' depth depth' baseEnabled baseEnabled' process process' held held',
    iprop(⊢ ownOff capacity era cpu ξ depth baseEnabled process held -∗
      ownOff capacity era cpu ξ' depth' baseEnabled' process' held' -∗ False)
  bound : ∀ era cpu ξ depth baseEnabled process held,
    iprop(ownOff capacity era cpu ξ depth baseEnabled process held ⊢
      ⌜depth < 2^31⌝ ∗ ownOff capacity era cpu ξ depth baseEnabled process held)
  size_le : ∀ era cpu ξ depth baseEnabled process held,
    iprop(ownOff capacity era cpu ξ depth baseEnabled process held ⊢
      ⌜held.size ≤ depth⌝ ∗ ownOff capacity era cpu ξ depth baseEnabled process held)
  zero_empty : ∀ era cpu ξ baseEnabled process held,
    iprop(ownOff capacity era cpu ξ 0 baseEnabled process held ⊢
      ⌜held = ∅⌝ ∗ ownOff capacity era cpu ξ 0 baseEnabled process held)
  csrs_access : ∀ era cpu ξ depth baseEnabled process held,
    iprop(ownOff capacity era cpu ξ depth baseEnabled process held ⊢
      hartCsrs capacity era cpu ∗
      (hartCsrs capacity era cpu -∗ ownOff capacity era cpu ξ depth baseEnabled process held))
  proc_access : ∀ era cpu ξ depth baseEnabled process held,
    iprop(ownOff capacity era cpu ξ depth baseEnabled process held ⊢
      curProc capacity era cpu ξ process ∗
      (∀ replacement : Word, curProc capacity era cpu ξ replacement -∗
        ownOff capacity era cpu ξ depth baseEnabled replacement held))
  locks_access : ∀ era cpu ξ depth baseEnabled process held,
    iprop(ownOff capacity era cpu ξ depth baseEnabled process held ⊢
      LockSet.cpuLocks capacity.heldSets era cpu held ∗ ⌜held.size ≤ depth⌝ ∗
      (∀ replacement : Held, ⌜replacement.size ≤ depth⌝ -∗
        LockSet.cpuLocks capacity.heldSets era cpu replacement -∗
        ownOff capacity era cpu ξ depth baseEnabled process replacement))
  index_off : ∀ era cpu ξ depth baseEnabled process held,
    iprop(⊢ off capacity era cpu -∗ ownOff capacity era cpu ξ depth baseEnabled process held -∗
      ⌜(if depth = 0 then baseEnabled else false) = false⌝ ∗
      off capacity era cpu ∗ ownOff capacity era cpu ξ depth baseEnabled process held)
  count_init : ∀ era cpu, iprop(off capacity era cpu ⊣⊢ count capacity era cpu 0 false)
  count_retune : ∀ era cpu depth baseEnabled replacement,
    iprop(count capacity era cpu (depth + 1) baseEnabled ⊣⊢ count capacity era cpu (depth + 1) replacement)
  count_push : ∀ era cpu depth baseEnabled,
    iprop(⊢ off capacity era cpu -∗ count capacity era cpu depth baseEnabled -∗
      ⌜depth = 0 → baseEnabled = false⌝ ∗ off capacity era cpu ∗ count capacity era cpu (depth + 1) baseEnabled)
  count_pop : ∀ era cpu depth,
    iprop(count capacity era cpu (depth + 1) false ⊣⊢ count capacity era cpu depth false)
  count_dec : ∀ era cpu depth baseEnabled,
    iprop(count capacity era cpu (depth + 2) baseEnabled ⊣⊢ count capacity era cpu (depth + 1) baseEnabled)
  count_pack : ∀ era cpu depth baseEnabled,
    iprop(off capacity era cpu ⊣⊢ count capacity era cpu (depth + 1) baseEnabled)

end Xv6.Kernel.CpuOwn
