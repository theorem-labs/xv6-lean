import Xv6.Kernel.MycpuBareWitnessSpec

namespace Xv6.Kernel.MycpuBareWitness
open MachCSL MachCSL.Machine MachCSL.Memory LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
attribute [local instance] platform

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem entry_config : MycpuBare.EntryConfig entry where
  privilege := rfl
  active := rfl
  landing := rfl
  misa := rfl
  environment := rfl
  sie := rfl
  mprv := rfl
  mxr := rfl
  sxl := rfl
  delegated := rfl
  bare := rfl
  tor := by constructor <;> first | rfl | decide
  htif := rfl
  pma := rfl
  pc := rfl

theorem cached_image : cachedImage = image := by
  funext a
  unfold cachedImage
  split
  · rename_i h
    have j : a.toNat - 0x800018ba < 34 := by omega
    have addr : a = BitVec.ofInt 64 (MycpuDecode.base + ((a.toNat - 0x800018ba : Nat) : Int)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofInt, MycpuDecode.base]
      have low : 0 ≤ (2147489978 : Int) + ↑(a.toNat - 2147489978) := by omega
      have high : (2147489978 : Int) + ↑(a.toNat - 2147489978) < 18446744073709551616 := by omega
      change a.toNat = ((2147489978 + ↑(a.toNat - 2147489978)) % (18446744073709551616 : Int)).toNat
      rw [Int.emod_eq_of_lt low high]
      omega
    have bytes := MycpuFetchBytes.ram_byte (a.toNat - 0x800018ba) j
    rw [← addr] at bytes
    exact bytes.symm
  · split
    · rename_i h
      unfold image loadedRam
      rw [if_pos (by unfold ramLow; unfold ramHigh at h ⊢; omega)]
      change some 0 = some (Xv6.Machine.bootByte (a.toNat : Int))
      rw [Xv6.Machine.bootByte_after_file _ (by omega)]
    · rfl

/-- Every write accepted by the evaluator is a genuine RAM NodeStep. -/
theorem write_node (s : LocalState Devices.State)
    (req : Logic.MemoryWriteWP.WriteRequest n) (word : BitVec (8*n))
    (k : Logic.MemoryWriteWP.WriteResult → SailM Unit)
    (present : req.value = some word) (ram : deviceAddress req.pa = false)
    (ordinary : accessExclusive req.access_kind = false) :
    NodeStep Devices.bus (fun _ => False) (hartAgent cpu) image s
      (.impure (.writeMem n req) k) (k (.Ok none)) (storeState s req word) := by
  simp only [NodeStep, present, ram, Bool.false_eq_true, ↓reduceIte]
  refine Or.inr ⟨?_, trivial, ?_⟩
  · intro a _ impossible
    exact impossible
  · simp only [storeState, ordinary, Bool.false_eq_true, ↓reduceIte]

/-- Sound for every accepted program and supplied local state, with no certificate
oracle for memory. The real common view is used for every RAM read. -/
theorem run_sound (fuel : Nat) (program : SailM Unit) (s t : LocalState Devices.State)
    (bound : s.view ≤ s.log.length) (checked : run fuel program s = some t) :
    NodeSteps Devices.bus (fun _ => False) (hartAgent cpu) image program s (.pure ()) t := by
  induction fuel generalizing program s t with
  | zero => simp [run] at checked
  | succ fuel ih =>
    cases hp : SpinlockWitness.pauseRun
        (Memory.read cachedImage s.log (hartAgent cpu) s.view) 2000 program s.registers with
    | none => simp [run, hp] at checked
    | some result =>
      obtain ⟨rest, regs⟩ := result
      have segment :=  SpinlockWitness.pauseRun_sound Devices.bus (fun _ => False)
        (hartAgent cpu) image (Memory.read cachedImage s.log (hartAgent cpu) s.view)
        2000 program s rest regs bound (by intro a; rw [cached_image]) hp
      cases rest with
      | pure value =>
        cases value
        have same : { s with registers := regs } = t := by simpa [run, hp] using checked
        subst t
        exact segment
      | impure event k =>
        cases event <;> simp only [run, hp] at checked <;> try dsimp only at checked
        all_goals try contradiction
        case writeMem n req =>
          change (if deviceAddress req.pa || accessExclusive req.access_kind then none else
            match req.value with
            | none => none
            | some word => run fuel (k (.Ok none)) (storeState { s with registers := regs } req word)) = some t at checked
          split at checked
          · contradiction
          · rename_i gates
            have ram : deviceAddress req.pa = false := by cases h : deviceAddress req.pa <;> simp_all
            have ordinary : accessExclusive req.access_kind = false := by
              cases h : accessExclusive req.access_kind <;> simp_all
            cases present : req.value with
            | none => simp [present] at checked
            | some word =>
              simp only [present] at checked
              have step := write_node { s with registers := regs } req word k present ram ordinary
              have nextbound : (storeState { s with registers := regs } req word).view ≤
                  (storeState { s with registers := regs } req word).log.length := by
                simp only [storeState, List.length_append, List.length_singleton]
                omega
              exact SpinlockWitness.nodeSteps_trans segment (.cons step (ih _ _ _ nextbound checked))

theorem cycles_steps {n : Nat} {s t : LocalState Devices.State} (h : Cycles n s t) :
    NodeSteps Devices.bus (fun _ => False) (hartAgent cpu) image (.pure ()) s (.pure ()) t := by
  induction h with
  | nil s => exact .nil _ _
  | cons first _ ih =>
    exact .cons (restart_step Devices.bus (fun _ => False) (hartAgent cpu) image _ false)
      (SpinlockWitness.nodeSteps_trans first ih)

end Xv6.Kernel.MycpuBareWitness
