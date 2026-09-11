import Xv6.Kernel.MycpuCycleBodyDefs
import Xv6.Kernel.MycpuScalarProofs
import Xv6.Kernel.MycpuMemoryPlan
import Xv6.Kernel.MycpuReturnProofs

namespace Xv6.Kernel.MycpuCycleBody
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

private theorem widen_read {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {req : MemoryReadWP.ReadRequest 8} {program : SailM α} {tail}
    (cut : SupervisorRead.Boundary small rs req program tail)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : SupervisorRead.Boundary large rs req program tail := by
  induction cut with
  | event => exact .event
  | «prefix» first _ ih => exact .prefix (widen first members) ih

private theorem widen_write {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {req : MemoryWriteWP.WriteRequest 8} {program : SailM α} {tail}
    (cut : SupervisorWrite.Boundary small rs req program tail)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : SupervisorWrite.Boundary large rs req program tail := by
  induction cut with
  | event => exact .event
  | «prefix» first _ ih => exact .prefix (widen first members) ih

theorem footprint_unique (s : Shares) : RegisterFootprint.Unique (footprint s) := by
  simp [RegisterFootprint.Unique, footprint, MycpuActive.footprint, MycpuFetch.footprint,
    SupervisorBareFetch.footprint, SupervisorBare.footprint, SupervisorFetchRead.footprint,
    SupervisorRetirement.retirementFootprint, SupervisorClock.clockFootprint]

theorem footprint_length (s : Shares) : (footprint s).length = 28 := rfl

def setupMembers (s : Shares) : SupervisorRetirement.SetupMembers (footprint s) where
  privilege := s.bare.translation.privilege
  inhibit := .discard
  config := .discard
  readPrivilege := by simp [footprint, MycpuActive.footprint, MycpuFetch.footprint,
    activeShares, SupervisorBareFetch.footprint, SupervisorBare.footprint]
  readInhibit := by simp [footprint, SupervisorRetirement.retirementFootprint]
  readConfig := by simp [footprint, SupervisorRetirement.retirementFootprint]
  writeFlag := by simp [footprint, SupervisorRetirement.retirementFootprint]

def completeMembers (s : Shares) : SupervisorRetirement.CompleteMembers (footprint s) where
  hart := s.hart
  next := .own 1
  readHart := by simp [footprint]
  readNext := by simp [footprint, MycpuActive.footprint]
  writePC := by simp [footprint, MycpuActive.footprint, MycpuFetch.footprint, activeShares]
  writeCounter := by simp [footprint, SupervisorRetirement.retirementFootprint]
  readFlag := .own 1
  readFlagMember := by simp [footprint, SupervisorRetirement.retirementFootprint]

theorem clock_members (s : Shares) (r : Register)
    (member : r ∈ SupervisorClock.clockRegisters) : (r, .own 1) ∈ footprint s := by
  simp only [SupervisorClock.clockRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [footprint, SupervisorClock.clockFootprint]

theorem scalar_members (s : Shares) (cell : Register × DFrac)
    (h : cell ∈ MycpuScalar.footprint (.own 1) s.tp) : cell ∈ footprint s := by
  simp only [MycpuScalar.footprint, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [footprint, MycpuActive.footprint, MycpuFetch.footprint, activeShares]

theorem memory_members (s : Shares) (slot : MycpuMemory.Slot) (cell : Register × DFrac)
    (h : cell ∈ MycpuMemory.footprint slot (memoryShares s) (.own 1)) : cell ∈ footprint s := by
  simp only [MycpuMemory.footprint, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (rfl | rfl | rfl) | h
  · simp [footprint, MycpuActive.footprint, memoryShares, activeShares]
  · simp [footprint, memoryShares]
  · cases slot <;> simp [footprint, MycpuMemory.dataRegister]
  · simp only [footprint, MycpuActive.footprint, MycpuFetch.footprint,
      List.mem_append, activeShares, memoryShares] at *
    simp only [h, or_true, true_or]

theorem return_members (s : Shares) (cell : Register × DFrac)
    (h : cell ∈ MycpuReturn.footprint (returnShares s)) : cell ∈ footprint s := by
  simp only [MycpuReturn.footprint, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    simp [footprint, MycpuActive.footprint, MycpuFetch.footprint, returnShares, activeShares,
      SupervisorBareFetch.footprint, SupervisorBare.footprint]

theorem scalar_plan [Platform] (s : Shares) (i : Fin 9) (rs : RegisterFile) :
    RegisterPlan.Returns (footprint s) rs (MycpuScalar.body i)
      (.Retire_Success ()) (MycpuScalar.after i rs) :=
  widen (MycpuScalar.body_plan (.own 1) s.tp i rs) (scalar_members s)

theorem return_plan [Platform] (s : Shares) (rs : RegisterFile) (config : MycpuReturn.Config rs) :
    RegisterPlan.Returns (footprint s) rs MycpuReturn.body
      (.Retire_Success ()) (MycpuReturn.after rs) :=
  widen (MycpuReturn.body_plan (returnShares s) rs config) (return_members s)

theorem store_boundary [Platform] (s : Shares) (slot : MycpuMemory.Slot)
    (rs : RegisterFile) region (config : MycpuMemory.WriteConfig slot rs region)
    (aligned : TsoContextWord.Aligned (MycpuMemory.address slot rs)) :
    SupervisorWrite.OneWrite (footprint s) rs (MycpuMemory.address slot rs) (MycpuMemory.dataValue slot rs)
      (MycpuMemory.storeBody slot) (fun _ => .Retire_Success ()) := by
  obtain ⟨tail, cut, success, error⟩ := MycpuMemory.store_boundary slot (memoryShares s) rs region config aligned
  exact ⟨tail, widen_write cut (memory_members s slot), success, error⟩

theorem load_boundary [Platform] (s : Shares) (slot : MycpuMemory.Slot)
    (rs : RegisterFile) region (config : MycpuMemory.ReadConfig slot rs region)
    (aligned : TsoContextWord.Aligned (MycpuMemory.address slot rs)) :
    ∃ tail, SupervisorRead.Boundary (footprint s) rs
      (SupervisorRead.request (MycpuMemory.address slot rs)) (MycpuMemory.loadBody slot) tail ∧
      (∀ word tag, tail (.Ok (word, tag)) = MycpuMemory.loadTail slot word) ∧
      tail (.Err ()) = _root_.Sail.ConcurrencyInterfaceV1.Free.fail .Exit := by
  obtain ⟨tail, cut, success, error⟩ := MycpuMemory.load_boundary slot (memoryShares s) rs region config aligned
  exact ⟨tail, widen_read cut (memory_members s slot), success, error⟩

theorem load_tail_plan (s : Shares) (slot : MycpuMemory.Slot) (rs : RegisterFile) word :
    RegisterPlan.Returns (footprint s) rs (MycpuMemory.loadTail slot word)
      (.Retire_Success ()) (MycpuMemory.after slot rs word) :=
  widen (MycpuMemory.load_tail_plan slot (memoryShares s) rs word) (memory_members s slot)

theorem scalar_tail_eq [Platform] (i : Fin 9) :
    MycpuActive.executeTail (MycpuScalar.index i) =
      (MycpuScalar.body i >>= fun result => pure (.Step_Execute (result, MycpuActive.instbits (MycpuScalar.index i)))) := by
  unfold MycpuActive.executeTail MycpuScalar.body
  rw [BootPmp.sail_bind_assoc]
  congr 1
  funext result
  cases result <;> rfl

theorem store_tail_eq [Platform] (slot : MycpuMemory.Slot) :
    MycpuActive.executeTail (MycpuMemory.storeIndex slot) =
      (MycpuMemory.storeBody slot >>= fun result => pure (.Step_Execute (result, MycpuActive.instbits (MycpuMemory.storeIndex slot)))) := by
  unfold MycpuActive.executeTail MycpuMemory.storeBody
  rw [BootPmp.sail_bind_assoc]
  congr 1
  funext result
  cases result <;> rfl

theorem load_tail_eq [Platform] (slot : MycpuMemory.Slot) :
    MycpuActive.executeTail (MycpuMemory.loadIndex slot) =
      (MycpuMemory.loadBody slot >>= fun result => pure (.Step_Execute (result, MycpuActive.instbits (MycpuMemory.loadIndex slot)))) := by
  unfold MycpuActive.executeTail MycpuMemory.loadBody
  rw [BootPmp.sail_bind_assoc]
  congr 1
  funext result
  cases result <;> rfl

theorem return_tail_eq [Platform] :
    MycpuActive.executeTail ⟨13, by decide⟩ =
      (MycpuReturn.body >>= fun result => pure (.Step_Execute (result, MycpuActive.instbits ⟨13, by decide⟩))) := rfl

end Xv6.Kernel.MycpuCycleBody
