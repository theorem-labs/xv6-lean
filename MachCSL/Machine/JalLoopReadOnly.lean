import MachCSL.Machine.JalLoopEval

/-! Syntactic read-only event trees are finite executions at the unchanged
register file. This property retains all read events; it is not a tree erasure. -/
namespace MachCSL.Machine.JalLoop
open _root_.Sail.ConcurrencyInterfaceV1.Free
open LeanPaperStock.Functions

inductive ReadOnly : SailM α → Prop where
  | pure (value : α) : ReadOnly (.pure value)
  | read (r : Register) (k : RegisterType r → SailM α)
      (rest : ∀ value, ReadOnly (k value)) : ReadOnly (.impure (.readReg r) k)

theorem ReadOnly.bind {program : SailM α} {next : α → SailM β}
    (first : ReadOnly program) (rest : ∀ value, ReadOnly (next value)) :
    ReadOnly (program >>= next) := by
  induction first with
  | pure value => exact rest value
  | read r k _ ih => exact .read r _ ih

theorem ReadOnly.exec {program : SailM α} (reads : ReadOnly program) (rs : RegisterFile) :
    ∃ value, RegisterExec program rs value rs := by
  induction reads with
  | pure value => exact ⟨value, (registerExec_pure value rs rs).mpr rfl⟩
  | read r k _ ih =>
    obtain ⟨value, run⟩ := ih (rs r)
    exact ⟨value, (registerExec_read rs r).bind run⟩

theorem ReadOnly.unit_exec {program : SailM Unit} (reads : ReadOnly program) (rs : RegisterFile) :
    RegisterExec program rs () rs := by
  obtain ⟨value, run⟩ := reads.exec rs
  cases value
  exact run

theorem readReg_readOnly (r : Register) : ReadOnly (PreSail.readReg r) :=
  .read r _ (fun value => .pure value)

theorem currentlyEnabled_zicsr_readOnly : ReadOnly (currentlyEnabled .Ext_Zicsr) := by
  unfold currentlyEnabled
  exact .pure _

theorem currentlyEnabled_s_readOnly : ReadOnly (currentlyEnabled .Ext_S) := by
  unfold currentlyEnabled
  apply (readReg_readOnly .misa).bind
  intro value
  apply currentlyEnabled_zicsr_readOnly.bind
  intro enabled
  exact .pure _

theorem external_interrupts_readOnly : ReadOnly (external_interrupts_pending ()) := by
  unfold external_interrupts_pending
  apply (readReg_readOnly .sig_meip).bind
  intro meip
  apply currentlyEnabled_s_readOnly.bind
  intro enabled
  cases enabled
  · exact .pure _
  · apply (readReg_readOnly .sig_seip).bind
    intro seip
    exact .pure _

theorem read_mip_readOnly (mode : XipReadType) : ReadOnly (read_mip mode) := by
  cases mode with
  | IncludePlatformInterrupts =>
    unfold read_mip
    apply (readReg_readOnly .mip).bind
    intro pending
    apply external_interrupts_readOnly.bind
    intro external
    exact .pure _
  | ExcludePlatformInterrupts => exact readReg_readOnly .mip

theorem mip_callback_readOnly (value : BitVec 64) :
    ReadOnly (csr_name_write_callback "mip" value) := by
  unfold csr_name_write_callback csr_name_map_backwards
  exact .pure _

/-- The source's changed-mip callback retains its reads but does not modify RF. -/
theorem mip_read_callback_exec (rs : RegisterFile) :
    RegisterExec (do
      let value ← read_mip .IncludePlatformInterrupts
      csr_name_write_callback "mip" value) rs () rs :=
  ((read_mip_readOnly .IncludePlatformInterrupts).bind mip_callback_readOnly).unit_exec rs

end MachCSL.Machine.JalLoop
