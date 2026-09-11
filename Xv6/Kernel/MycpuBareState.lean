import Xv6.Kernel.MycpuBareDefs
import Xv6.Kernel.MycpuCycleLink
import Xv6.Kernel.MycpuRegisterSequenceLink

namespace Xv6.Kernel.MycpuBare
open Iris MachCSL.Memory MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

/-- Bookkeeping omits only the real control/clock writes. This is a relation
between symbolic files, not a physical execution assumption. -/
def ignored : List Register := [.PC, .nextPC, .minstret_increment, .minstret, .mcycle, .mtime, .mip]
def CoreEq (a b : RegisterFile) : Prop := ∀ r, r ∉ ignored → b r = a r

theorem CoreEq.refl (rs : RegisterFile) : CoreEq rs rs := fun _ _ => rfl

theorem CoreEq.trans {a b c : RegisterFile} (ab : CoreEq a b) (bc : CoreEq b c) : CoreEq a c :=
  fun r h => (bc r h).trans (ab r h)

theorem CoreEq.symm {a b : RegisterFile} (ab : CoreEq a b) : CoreEq b a :=
  fun r h => (ab r h).symm

theorem CoreEq.write {a b : RegisterFile} (same : CoreEq a b) (r : Register) (v : RegisterType r) :
    CoreEq (MachCSL.Sail.Registers.write a r v) (MachCSL.Sail.Registers.write b r v) := by
  intro key outside
  by_cases equal : r = key
  · subst key
    simp
  · simp only [MachCSL.Sail.Registers.write_other _ _ _ _ equal]
    exact same key outside

theorem CoreEq.write_ignored (rs : RegisterFile) (r : Register) (v : RegisterType r) (member : r ∈ ignored) :
    CoreEq rs (MachCSL.Sail.Registers.write rs r v) := by
  intro key outside
  exact MachCSL.Sail.Registers.write_other rs r key v (fun eq => outside (eq ▸ member))

theorem started_core (rs : RegisterFile) : CoreEq rs (MycpuCycle.started rs) :=
  CoreEq.write_ignored rs .minstret_increment _ (by decide)

theorem prepared_core (rs : RegisterFile) (i : Fin 14) : CoreEq rs (MycpuActive.prepared i rs) :=
  CoreEq.write_ignored rs .nextPC _ (by decide)

theorem completed_core (before after : RegisterFile) (completed : MycpuCycle.Completed before after) :
    CoreEq before after := by
  intro r outside
  simp only [ignored, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  apply MycpuCycleShell.completed_other before after completed r outside.1 outside.2.2.2.1
  simp [SupervisorClock.clockRegisters, outside.2.2.2.2]

/-- Exact pre-retirement family files. The saved load words are parameters from
the native stack resource, specialized here to the values stored by the prologue. -/
def bodyFile (entry : RegisterFile) (k : Nat) (rs : RegisterFile) : RegisterFile :=
  match k with
  | 0 => MycpuCycle.scalarBeforeFinish ⟨0, by decide⟩ rs
  | 1 => MycpuCycle.storeBeforeFinish .ra rs
  | 2 => MycpuCycle.storeBeforeFinish .s0 rs
  | 3 => MycpuCycle.scalarBeforeFinish ⟨1, by decide⟩ rs
  | 4 => MycpuCycle.scalarBeforeFinish ⟨2, by decide⟩ rs
  | 5 => MycpuCycle.scalarBeforeFinish ⟨3, by decide⟩ rs
  | 6 => MycpuCycle.scalarBeforeFinish ⟨4, by decide⟩ rs
  | 7 => MycpuCycle.scalarBeforeFinish ⟨5, by decide⟩ rs
  | 8 => MycpuCycle.scalarBeforeFinish ⟨6, by decide⟩ rs
  | 9 => MycpuCycle.scalarBeforeFinish ⟨7, by decide⟩ rs
  | 10 => MycpuCycle.loadBeforeFinish .ra rs (entry .x1)
  | 11 => MycpuCycle.loadBeforeFinish .s0 rs (entry .x8)
  | 12 => MycpuCycle.scalarBeforeFinish ⟨8, by decide⟩ rs
  | _ => MycpuCycle.returnBeforeFinish rs

def reference (entry : RegisterFile) : Nat → RegisterFile
  | 0 => entry
  | k + 1 => SupervisorRetirement.tickPCAfter (bodyFile entry k (reference entry k))

structure Phase (entry : RegisterFile) (k : Nat) (rs : RegisterFile) : Prop where
  core : CoreEq (reference entry k) rs
  pc : rs .PC = reference entry k .PC
  nextPC : 0 < k → rs .nextPC = reference entry k .nextPC

set_option linter.unusedSimpArgs false in
/-- Equal data projections and PC suffice for the actual body register effects. -/
theorem body_core (entry : RegisterFile) (k : Nat) (a b : RegisterFile)
    (core : CoreEq a b) (pc : b .PC = a .PC) :
    CoreEq (bodyFile entry k a) (bodyFile entry k b) := by
  have h1 := core .x1 (by decide)
  have h2 := core .x2 (by decide)
  have h4 := core .x4 (by decide)
  have h10 := core .x10 (by decide)
  have h15 := core .x15 (by decide)
  intro r outside
  have same := core r outside
  simp only [ignored, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  unfold bodyFile
  split <;>
    simp [MycpuCycle.scalarBeforeFinish, MycpuCycle.storeBeforeFinish, MycpuCycle.loadBeforeFinish,
      MycpuCycle.returnBeforeFinish, MycpuCycleEntry.scalarAfter, MycpuCycleEntry.loadAfter,
      MycpuCycleEntry.returnAfter, MycpuScalar.after, MycpuMemory.after, MycpuReturn.after,
      MycpuActive.prepared, MycpuCycle.started, MycpuCycleShell.started, SupervisorRetirement.setupAfter,
      MachCSL.Sail.Registers.write, Ne.symm outside.2.1, Ne.symm outside.2.2.1,
      same, h1, h2, h4, h10, h15, pc]

theorem body_next (entry : RegisterFile) (k : Nat) (a b : RegisterFile)
    (core : CoreEq a b) (pc : b .PC = a .PC) :
    bodyFile entry k b .nextPC = bodyFile entry k a .nextPC := by
  have h1 := core .x1 (by decide)
  unfold bodyFile
  split <;>
    simp [MycpuCycle.scalarBeforeFinish, MycpuCycle.storeBeforeFinish, MycpuCycle.loadBeforeFinish,
      MycpuCycle.returnBeforeFinish, MycpuCycleEntry.scalarAfter, MycpuCycleEntry.loadAfter,
      MycpuCycleEntry.returnAfter, MycpuScalar.after, MycpuMemory.after, MycpuReturn.after,
      MycpuActive.prepared, MycpuCycle.started, MycpuCycleShell.started, SupervisorRetirement.setupAfter,
      MachCSL.Sail.Registers.write, h1, pc]

theorem phase_zero (entry : RegisterFile) : Phase entry 0 entry :=
  ⟨CoreEq.refl _, rfl, fun h => by omega⟩

/-- Every actual post-clock result advances the bookkeeping relation. -/
theorem phase_next (entry : RegisterFile) (k : Nat) (before after : RegisterFile)
    (phase : Phase entry k before)
    (done : MycpuCycle.Completed (bodyFile entry k before) after) : Phase entry (k+1) after := by
  have next := body_next entry k (reference entry k) before phase.core phase.pc
  have pc := MycpuCycleShell.completed_pc _ _ done
  refine ⟨?_, ?_, ?_⟩
  · exact (CoreEq.write_ignored (bodyFile entry k (reference entry k)) .PC _ (by decide)).symm.trans
      ((body_core entry k _ _ phase.core phase.pc).trans (completed_core _ _ done))
  · simpa [reference, SupervisorRetirement.tickPCAfter, MachCSL.Sail.Registers.write] using pc.1.trans next
  · intro _
    simpa [reference, SupervisorRetirement.tickPCAfter, MachCSL.Sail.Registers.write] using pc.2.trans next

def bodyWrites : List Register := [.nextPC, .minstret_increment, .x1, .x2, .x8, .x10, .x15]

theorem body_other (entry : RegisterFile) (k : Nat) (rs : RegisterFile) (r : Register)
    (outside : r ∉ bodyWrites) : bodyFile entry k rs r = rs r := by
  have ne (key : Register) (h : key ∈ bodyWrites) : key ≠ r := fun eq => outside (eq ▸ h)
  unfold bodyFile
  split <;>
    simp [MycpuCycle.scalarBeforeFinish, MycpuCycle.storeBeforeFinish, MycpuCycle.loadBeforeFinish,
      MycpuCycle.returnBeforeFinish, MycpuCycleEntry.scalarAfter, MycpuCycleEntry.loadAfter,
      MycpuCycleEntry.returnAfter, MycpuScalar.after, MycpuMemory.after, MycpuReturn.after,
      MycpuActive.prepared, MycpuCycle.started, MycpuCycleShell.started, SupervisorRetirement.setupAfter,
      MachCSL.Sail.Registers.write, ne .nextPC (by decide), ne .minstret_increment (by decide),
      ne .x1 (by decide), ne .x2 (by decide), ne .x8 (by decide), ne .x10 (by decide), ne .x15 (by decide)]

theorem reference_other (entry : RegisterFile) (k : Nat) (r : Register)
    (notPC : r ≠ .PC) (outside : r ∉ bodyWrites) : reference entry k r = entry r := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold reference SupervisorRetirement.tickPCAfter
    rw [MachCSL.Sail.Registers.write_other _ _ _ _ (Ne.symm notPC), body_other _ _ _ _ outside, ih]

theorem reference_stable (entry : RegisterFile) (k : Nat) : Stable entry (reference entry k) := by
  intro r member
  have disjoint : List.Disjoint stableRegisters (.PC :: bodyWrites) := by simp [List.Disjoint, stableRegisters, bodyWrites]
  apply reference_other
  · intro eq; exact disjoint member (by simp [eq])
  · intro present; exact disjoint member (List.mem_cons_of_mem _ present)

theorem phase_stable (entry : RegisterFile) (k : Nat) (rs : RegisterFile) (phase : Phase entry k rs) :
    Stable entry rs := by
  intro r member
  have disjoint : List.Disjoint stableRegisters ignored := by simp [List.Disjoint, stableRegisters, ignored]
  exact (phase.core r (fun h => disjoint member h)).trans (reference_stable entry k r member)

theorem stable_config {entry rs : RegisterFile} (config : SupervisorConfig entry) (same : Stable entry rs) :
    SupervisorConfig rs := by
  have h (r : Register) (member : r ∈ stableRegisters) := same r member
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | simpa only [h .cur_privilege (by decide)] using config.privilege
    | simpa only [h .hart_state (by decide)] using config.active
    | simpa only [h .elp (by decide)] using config.landing
    | simpa only [h .misa (by decide)] using config.misa
    | simpa only [h .menvcfg (by decide)] using config.environment
    | simpa only [h .mstatus (by decide)] using config.sie
    | simpa only [h .mstatus (by decide)] using config.mprv
    | simpa only [h .mstatus (by decide)] using config.mxr
    | simpa only [h .mstatus (by decide)] using config.sxl
    | simpa only [h .mie (by decide), h .mideleg (by decide)] using config.delegated
    | simpa only [h .satp (by decide)] using config.bare
    | simpa only [h .htif_tohost_base (by decide)] using config.htif
    | simpa only [h .pma_regions (by decide)] using config.pma
    | skip
  rcases config.tor with ⟨tor, positive, execute, write, read, covers⟩
  constructor <;> simp_all [SupervisorPmp.entry0, SupervisorPmp.upper0, h .pmpcfg_n (by decide), h .pmpaddr_n (by decide)]

def pcAt (entry : RegisterFile) (k : Nat) : BitVec 64 :=
  if bound : k < 14 then MycpuDecode.address ⟨k, bound⟩ else MycpuReturn.retPC (entry .x1)

def stepWidth (k : Nat) : Nat := if k = 7 ∨ k = 8 then 4 else 2

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
theorem body_values (entry : RegisterFile) (k : Nat) (rs : RegisterFile) :
    bodyFile entry k rs .x1 = (if k = 10 then entry .x1 else rs .x1) ∧
    bodyFile entry k rs .x2 = (if k = 0 then rs .x2 + (-16#64) else if k = 12 then rs .x2 + 16#64 else rs .x2) ∧
    bodyFile entry k rs .x4 = rs .x4 ∧
    bodyFile entry k rs .x8 = (if k = 3 then rs .x2 + 16#64 else if k = 11 then entry .x8 else rs .x8) ∧
    bodyFile entry k rs .x10 = (if k = 7 then rs .PC + 0x11000#64 else if k = 8 then rs .x10 + sign_extend (m := 64) 0xb20#12
      else if k = 9 then rs .x10 + rs .x15 else rs .x10) ∧
    bodyFile entry k rs .x15 = (if k = 4 then rs .x4 else if k = 5 then
      sign_extend (m := 64) (_root_.Sail.BitVec.extractLsb (rs .x15) 31 0)
      else if k = 6 then _root_.Sail.shift_bits_left (rs .x15) 7#6 else rs .x15) ∧
    bodyFile entry k rs .nextPC = (if k < 13 then rs .PC + BitVec.ofNat 64 (stepWidth k)
      else MycpuReturn.retPC (rs .x1)) := by
  rcases k with _ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | (k)))))))))))))
  all_goals
    simp [bodyFile, MycpuCycle.scalarBeforeFinish, MycpuCycle.storeBeforeFinish,
      MycpuCycle.loadBeforeFinish, MycpuCycle.returnBeforeFinish, MycpuCycleEntry.scalarAfter,
      MycpuCycleEntry.loadAfter, MycpuCycleEntry.returnAfter, MycpuScalar.after, MycpuMemory.after,
      MycpuReturn.after, MycpuActive.prepared, MycpuCycle.started, MycpuCycleShell.started,
      SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write, stepWidth,
      MycpuDecode.width, MycpuScalar.index, MycpuMemory.storeIndex, MycpuMemory.loadIndex,
      _root_.Sail.BitVec.addInt]
  all_goals try simp only [show sign_extend (m := 64) 0#12 = 0#64 from rfl, BitVec.add_zero]
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | exact ⟨trivial, rfl⟩ | intro impossible; omega

end Xv6.Kernel.MycpuBare
