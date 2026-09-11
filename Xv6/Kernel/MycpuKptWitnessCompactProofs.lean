import Xv6.Kernel.MycpuKptWitnessResultProofs
namespace Xv6.Kernel.MycpuKptWitness
open MachCSL MachCSL.Machine MachCSL.Memory

/-- Flat expected projections for kernel normalization. The following theorem
checks this entire file against the original source-ordered checkpoint. -/
def compact (k : Nat) (r : Register) : RegisterType r :=
  match r with
  | .PC | .nextPC => MycpuBare.pcAt entry k
  | .x2 => if 0 < k ∧ k ≤ 12 then 0x8003fff0#64 else 0x80040000#64
  | .x8 => if 4 ≤ k ∧ k ≤ 11 then 0x80040000#64 else 0x123456789abcdef0#64
  | .x15 => if k < 5 then 0#64 else if k < 7 then 3#64 else 0x180#64
  | .x10 => if k < 8 then 0#64 else if k = 8 then 0x800128c8#64
      else if k = 9 then 0x800123e8#64 else 0x80012568#64
  | .minstret => BitVec.ofNat 64 k
  | .minstret_increment => decide (0 < k)
  | .tlb => tlbAt k
  | r => entry r

def compactState (k : Nat) : LocalState Devices.State :=
  { stateAt k with registers := compact k }

private def changed : List Register :=
  [.PC, .nextPC, .x1, .x2, .x8, .x15, .x10, .minstret, .minstret_increment, .tlb]

private theorem compact_other (k : Nat) (r : Register) (outside : r ∉ changed) :
    compact k r = entry r := by
  cases r <;> simp_all [changed, compact]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem compact_eq (i : Fin 15) : compact i.val = checkpoint i.val := by
  funext r
  by_cases member : r ∈ changed
  · simp only [changed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals obtain ⟨k,hk⟩ := i
    all_goals
      match k with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
      | 3 => rfl
      | 4 => rfl
      | 5 => rfl
      | 6 => rfl
      | 7 => rfl
      | 8 => rfl
      | 9 => rfl
      | 10 => rfl
      | 11 => rfl
      | 12 => rfl
      | 13 => rfl
      | 14 => rfl
      | _ + 15 => omega
  · have ne (key : Register) (hk : key ∈ changed) : r ≠ key := by
      intro eq; subst r; exact member hk
    rw [checkpoint_other i.val r (ne .tlb (by decide)) (ne .minstret (by decide))]
    rw [MycpuBare.reference_other entry i.val r (ne .PC (by decide)) (by
      intro body
      simp only [MycpuBare.bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at body
      rcases body with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact member (by decide))]
    exact compact_other i.val r member

theorem compact_state_eq (i : Fin 15) : compactState i.val = stateAt i.val := by
  unfold compactState
  rw [compact_eq i]
  rfl

end Xv6.Kernel.MycpuKptWitness
