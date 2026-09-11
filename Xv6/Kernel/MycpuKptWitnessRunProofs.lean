import Xv6.Kernel.MycpuKptWitnessSpec
import Xv6.Kernel.MycpuBareWitnessRunProofs

namespace Xv6.Kernel.MycpuKptWitness
open MachCSL MachCSL.Machine MachCSL.Memory LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
attribute [local instance] platform
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem cached_image : cachedImage = image := by
  funext a
  simp only [cachedImage, image, MycpuBareWitness.cached_image]

/-- Every write accepted by the evaluator is a genuine RAM NodeStep. -/
theorem write_node (baseImage : ByteMap 64) (writer : CPU) (s : LocalState Devices.State)
    (req : Logic.MemoryWriteWP.WriteRequest n) (word : BitVec (8*n))
    (k : Logic.MemoryWriteWP.WriteResult → SailM Unit)
    (present : req.value = some word) (ram : deviceAddress req.pa = false)
    (ordinary : accessExclusive req.access_kind = false) :
    NodeStep Devices.bus (fun _ => False) (hartAgent writer) baseImage s
      (.impure (.writeMem n req) k) (k (.Ok none)) (storeState writer s req word) := by
  simp only [NodeStep, present, ram, Bool.false_eq_true, ↓reduceIte]
  refine Or.inr ⟨?_, trivial, ?_⟩
  · intro a _ impossible
    exact impossible
  · simp only [storeState, ordinary, Bool.false_eq_true, ↓reduceIte]

/-- Sound for every accepted program and supplied local state, with no certificate
oracle for memory. The real common view is used for every RAM read. -/
theorem run_sound (baseImage cache : ByteMap 64) (writer : CPU) (cache_eq : cache = baseImage) (fuel : Nat) (program : SailM Unit) (s t : LocalState Devices.State)
    (bound : s.view ≤ s.log.length) (checked : run cache writer fuel program s = some t) :
    NodeSteps Devices.bus (fun _ => False) (hartAgent writer) baseImage program s (.pure ()) t := by
  induction fuel generalizing program s t with
  | zero => simp [run] at checked
  | succ fuel ih =>
    cases hp : SpinlockWitness.pauseRun
        (Memory.read cache s.log (hartAgent writer) s.view) 2000 program s.registers with
    | none => simp [run, hp] at checked
    | some result =>
      obtain ⟨rest, regs⟩ := result
      have segment :=  SpinlockWitness.pauseRun_sound Devices.bus (fun _ => False)
        (hartAgent writer) baseImage (Memory.read cache s.log (hartAgent writer) s.view)
        2000 program s rest regs bound (by intro a; rw [cache_eq]) hp
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
            | some word => run cache writer fuel (k (.Ok none)) (storeState writer { s with registers := regs } req word)) = some t at checked
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
              have step := write_node baseImage writer { s with registers := regs } req word k present ram ordinary
              have nextbound : (storeState writer { s with registers := regs } req word).view ≤
                  (storeState writer { s with registers := regs } req word).log.length := by
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

end Xv6.Kernel.MycpuKptWitness
