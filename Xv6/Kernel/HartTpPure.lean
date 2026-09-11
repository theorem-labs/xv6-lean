import Xv6.Kernel.HartTpSpec

namespace Xv6.Kernel.HartTp
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

theorem physical_none (index : Index) : physical index = none ↔ index = 0#5 := by
  have checked : ∀ i : Index, physical i = none ↔ i = 0#5 := by decide
  exact checked index

theorem physical_injective : Function.Injective physical := by
  unfold Function.Injective
  decide

theorem physical_injective_keys (a b : Index) (r s : TypedRegister)
    (ha : physical a = some r) (hb : physical b = some s) (same : r.val = s.val) : a = b := by
  apply physical_injective
  rw [ha, hb, Subtype.ext same]

theorem all_indices (index : Index) : index ∈ indices := by
  exact List.mem_map.mpr ⟨index.toFin, List.mem_finRange _, rfl⟩

theorem unique_indices : indices.Nodup := by decide

theorem unique_physical : physicalKeys.Nodup := by decide

theorem physical_count : physicalKeys.length = 31 := rfl

theorem read_program (index : Index) :
    LeanPaperStock.Functions.rX_bits (.Regidx index) = readAt index := by
  have member : index ∈ [0#5, 1#5, 2#5, 3#5, 4#5, 5#5, 6#5, 7#5, 8#5, 9#5, 10#5, 11#5, 12#5, 13#5, 14#5, 15#5, 16#5, 17#5, 18#5, 19#5, 20#5, 21#5, 22#5, 23#5, 24#5, 25#5, 26#5, 27#5, 28#5, 29#5, 30#5, 31#5] := all_indices index
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst index; rfl

@[simp] theorem set_same (values : GprFile) (index : Index) (value : Word) :
    set values index value index = value := by simp [set]

theorem set_other (values : GprFile) (index other : Index) (value : Word) (different : other ≠ index) :
    set values index value other = values other := by simp [set, different]

theorem set_current (values : GprFile) (index : Index) : set values index (values index) = values := by
  funext other
  simp only [set]
  split <;> simp_all

theorem pinned_tp (cpu : CPU) (values : GprFile) : rget cpu values tp = hartWord cpu := by
  simp [rget, pin]

theorem read_other (cpu : CPU) (values : GprFile) (index : Index) (different : index ≠ tp) :
    rget cpu values index = values index := set_other values tp index _ different

theorem hart_independent (a b : CPU) (values : GprFile) (index : Index) (different : index ≠ tp) :
    rget a values index = rget b values index := by rw [read_other a _ _ different, read_other b _ _ different]

theorem pin_id (cpu : CPU) (values : GprFile) (equal : values tp = hartWord cpu) : pin cpu values = values := by
  unfold pin
  rw [← equal, set_current]

theorem pin_set (cpu : CPU) (values : GprFile) (index : Index) (value : Word) (different : index ≠ tp) :
    set (pin cpu values) index value = pin cpu (set values index value) := by
  funext other
  simp only [pin, set]
  by_cases hi : other = index <;> by_cases ht : other = tp <;> simp_all

theorem pureSpec : PureSpec where
  zero := physical_none
  physicalInjective := physical_injective_keys
  allIndices := all_indices
  uniqueIndices := unique_indices
  uniquePhysical := unique_physical
  physicalCount := physical_count
  readProgram := read_program
  pinnedTp := pinned_tp
  readOther := read_other
  hartIndependent := hart_independent
  pinId := pin_id
  pinSet := pin_set

end Xv6.Kernel.HartTp
