import Xv6.Kernel.MycpuCycleEntryDefs
import Xv6.Kernel.MycpuActiveLink
import Xv6.Kernel.MycpuFetchLink
import Xv6.Kernel.MycpuCycleBodyPlan

namespace Xv6.Kernel.MycpuCycleEntry
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

private theorem active_members (s : Shares) (cell : Register × DFrac)
    (h : cell ∈ MycpuActive.footprint (MycpuCycleBody.activeShares s)) :
    cell ∈ MycpuCycleBody.footprint s := by
  simp only [MycpuCycleBody.footprint, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl h)))

private theorem fetch_members (s : Shares) (cell : Register × DFrac)
    (h : cell ∈ MycpuFetch.footprint (MycpuCycleBody.activeShares s).fetch) :
    cell ∈ MycpuCycleBody.footprint s := by
  apply active_members s cell
  exact List.mem_append_left _ h

private theorem boundary_weaken {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {n : Nat} {req : MemoryReadWP.ReadRequest n} {program : SailM α} {tail}
    (cut : SupervisorFetchRead.Boundary small rs req program tail)
    (members : ∀ cell, cell ∈ small → cell ∈ large) :
    SupervisorFetchRead.Boundary large rs req program tail := by
  induction cut with
  | event => exact .event
  | «prefix» first _ ih => exact .prefix (MycpuActive.plan_weaken first members) ih

theorem dispatch_plan (s : Shares) (rs : RegisterFile)
    (priv : rs .cur_privilege = .Supervisor) (disabled : SupervisorInterrupt.Disabled rs) :
    RegisterPlan.Returns (MycpuCycleBody.footprint s) rs
      (_root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.readReg .cur_privilege >>= dispatchInterrupt)
      none rs :=
  MycpuActive.plan_weaken (MycpuActive.dispatch_plan (MycpuCycleBody.activeShares s) rs priv disabled)
    (active_members s)

theorem fetch_cut [Platform] (s : Shares) (rs : RegisterFile) (i : Fin 14) region
    (config : MycpuFetch.Config rs i region) :
    MycpuFetch.FixedRead (MycpuCycleBody.footprint s) rs (MycpuDecode.address i)
      (MycpuFetchBytes.width i) (MycpuFetchBytes.word i) (fetch ()) (MycpuFetch.result i) := by
  obtain ⟨tail, cut, success, error⟩ := MycpuFetch.fetch_cut
    (MycpuCycleBody.activeShares s).fetch rs i region config
  exact ⟨tail, boundary_weaken cut (fetch_members s), success, error⟩

theorem prepare_prefix [Platform] (s : Shares) (rs : RegisterFile) (i : Fin 14) region stepNo
    (config : Config rs i region) :
    MycpuActive.Prefix (MycpuCycleBody.footprint s) rs
      (MycpuActive.afterFetch stepNo (MycpuFetch.result i)) (MycpuActive.executeTail i) (prepared i rs) :=
  MycpuActive.Prefix.weaken
    (MycpuActive.prepare_prefix (MycpuCycleBody.activeShares s) rs i region stepNo config) (active_members s)

theorem prepared_address (slot : MycpuMemory.Slot) (i : Fin 14) (rs : RegisterFile) :
    MycpuMemory.address slot (prepared i rs) = MycpuMemory.address slot rs := by
  simp [MycpuMemory.address, prepared, MycpuActive.prepared, MachCSL.Sail.Registers.write]

theorem prepared_data (slot : MycpuMemory.Slot) (i : Fin 14) (rs : RegisterFile) :
    MycpuMemory.dataValue slot (prepared i rs) = MycpuMemory.dataValue slot rs := by
  cases slot <;> simp [MycpuMemory.dataValue, prepared, MycpuActive.prepared, MachCSL.Sail.Registers.write]

private theorem prepared_transform (i : Fin 14) (rs : RegisterFile)
    (config : SupervisorAddress.Config rs .Bare) : SupervisorAddress.Config (prepared i rs) .Bare := by
  rcases config with ⟨privilege, mprv, mxr, pmm, sxl, decoded⟩
  constructor <;> simp_all [prepared, MycpuActive.prepared, MachCSL.Sail.Registers.write]

private theorem prepared_bare (i : Fin 14) (rs : RegisterFile)
    (config : SupervisorBare.Config rs) : SupervisorBare.Config (prepared i rs) := by
  rcases config with ⟨privilege, sxl, mode⟩
  constructor <;> simp_all [prepared, MycpuActive.prepared, MachCSL.Sail.Registers.write]

private theorem prepared_tor (i : Fin 14) (rs : RegisterFile)
    (config : SupervisorPmp.TorRam rs) : SupervisorPmp.TorRam (prepared i rs) := by
  rcases config with ⟨mode, positive, execute, write, read, covers⟩
  constructor <;> simp_all [SupervisorPmp.entry0, SupervisorPmp.upper0, prepared, MycpuActive.prepared, MachCSL.Sail.Registers.write]

theorem prepared_write_config (slot : MycpuMemory.Slot) (i : Fin 14) (rs : RegisterFile) region
    (config : MycpuMemory.WriteConfig slot rs region) :
    MycpuMemory.WriteConfig slot (prepared i rs) region := by
  refine ⟨prepared_transform i rs config.transform, ?_⟩
  refine ⟨prepared_bare i rs config.memory.bare, ?_, prepared_tor i rs config.memory.tor, ?_, ?_, ?_, config.memory.writable⟩
  · simpa [prepared, MycpuActive.prepared, MachCSL.Sail.Registers.write] using config.memory.mprv
  · simpa only [prepared_address] using config.memory.range
  · simpa [prepared, MycpuActive.prepared, MachCSL.Sail.Registers.write] using config.memory.disabled
  · rw [prepared_address]
    simpa [prepared, MycpuActive.prepared, MachCSL.Sail.Registers.write] using config.memory.matched

theorem prepared_read_config (slot : MycpuMemory.Slot) (i : Fin 14) (rs : RegisterFile) region
    (config : MycpuMemory.ReadConfig slot rs region) :
    MycpuMemory.ReadConfig slot (prepared i rs) region := by
  refine ⟨prepared_transform i rs config.transform, ?_⟩
  refine ⟨prepared_bare i rs config.memory.bare, ?_, prepared_tor i rs config.memory.tor, ?_, ?_, ?_, config.memory.readable⟩
  · simpa [prepared, MycpuActive.prepared, MachCSL.Sail.Registers.write] using config.memory.mprv
  · simpa only [prepared_address] using config.memory.range
  · simpa [prepared, MycpuActive.prepared, MachCSL.Sail.Registers.write] using config.memory.disabled
  · rw [prepared_address]
    simpa [prepared, MycpuActive.prepared, MachCSL.Sail.Registers.write] using config.memory.matched

theorem prepared_return_config (i : Fin 14) (rs : RegisterFile)
    (config : MycpuReturn.Config rs) : MycpuReturn.Config (prepared i rs) := by
  rcases config with ⟨privilege, lpe, compressed⟩
  constructor <;> simp_all [prepared, MycpuActive.prepared, MachCSL.Sail.Registers.write]

/-- Preserve every actual interrupt/fetch branch while grouping dispatch. -/
theorem factor [Platform] (stepNo : Nat) : run_hart_active stepNo =
    ((_root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.readReg .cur_privilege >>= dispatchInterrupt) >>=
      fun pending => match pending with
      | some (intr, priv) => pure (.Step_Pending_Interrupt (intr, priv))
      | none => fetch () >>= MycpuActive.afterFetch stepNo) := by
  rw [MycpuActive.factor, BootPmp.sail_bind_assoc]
  congr 1

/-- The four public families cover every concrete instruction index. -/
theorem index_complete : ∀ i : Fin 14,
    (∃ j : Fin 9, MycpuScalar.index j = i) ∨
    i = MycpuMemory.storeIndex .ra ∨ i = MycpuMemory.storeIndex .s0 ∨
    i = MycpuMemory.loadIndex .ra ∨ i = MycpuMemory.loadIndex .s0 ∨ i = ⟨13, by decide⟩ := by decide

end Xv6.Kernel.MycpuCycleEntry
