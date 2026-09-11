import MachCSL.Logic.SupervisorClockSpec
import MachCSL.Logic.RegisterPlanProofs
import MachCSL.Machine.JalLoopReadOnly

namespace MachCSL.Logic.SupervisorClock
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

theorem OffClock.refl (rs : RegisterFile) : OffClock rs rs := fun _ _ => rfl

theorem OffClock.trans {before middle after : RegisterFile}
    (first : OffClock before middle) (second : OffClock middle after) : OffClock before after :=
  fun r outside => (second r outside).trans (first r outside)

theorem OffClock.write (rs : RegisterFile) (r : Register) (value : RegisterType r)
    (inside : r ∈ clockRegisters) : OffClock rs (Sail.Registers.write rs r value) := by
  intro other outside
  have ne : other ≠ r := fun same => outside (same ▸ inside)
  simp [Sail.Registers.write, Ne.symm ne]

theorem Framed.bind {fp : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {next : α → SailM β}
    (first : Framed fp rs program)
    (rest : ∀ value after, Framed fp after (next value)) : Framed fp rs (program >>= next) :=
  RegisterPlan.Plan.bind first fun value after frame =>
    (rest value after).mono fun _ _ later => frame.trans later

theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    Framed fp rs (pure value) := .pure (.refl rs)

theorem read_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (r : Register) :
    Framed fp rs (PreSail.readReg r) := .readAny fun _ => .pure (.refl rs)

theorem write_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (r : Register) (value : RegisterType r) (member : (r, .own 1) ∈ fp)
    (inside : r ∈ clockRegisters) : Framed fp rs (PreSail.writeReg r value) :=
  .write member (.pure (OffClock.write rs r value inside))

/-- Reuse the existing syntactic callback tree; each read is independently
universal, including the PLIC-owned hardware pins. -/
theorem readonly_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    {program : SailM α} (readonly : JalLoop.ReadOnly program) : Framed fp rs program := by
  induction readonly with
  | pure value => exact pure_plan fp rs value
  | read r k _ ih => exact .readAny ih

theorem callback_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) :
    Framed fp rs (do
      let value ← read_mip .IncludePlatformInterrupts
      csr_name_write_callback "mip" value) :=
  readonly_plan fp rs (JalLoop.ReadOnly.bind
    (JalLoop.read_mip_readOnly .IncludePlatformInterrupts) JalLoop.mip_callback_readOnly)

private theorem changed_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (old : BitVec 64) : Framed fp rs (do
      let pending ← PreSail.readReg .mip
      if old != pending then do
        let value ← read_mip .IncludePlatformInterrupts
        csr_name_write_callback "mip" value
      else Pure.pure ()) := by
  refine Framed.bind (read_plan fp rs .mip) ?_
  intro pending rs
  split
  · exact callback_plan fp rs
  · exact pure_plan fp rs ()

/-- Both timer branches and the entire changed-mip callback are retained. -/
theorem clint_plan (fp : RegisterFootprint.Footprint)
    (mipFull : (.mip, .own 1) ∈ fp) (rs : RegisterFile) :
    Framed fp rs (clint_dispatch false) := by
  unfold clint_dispatch
  refine Framed.bind (read_plan fp rs .mip) ?_
  intro old rs
  refine Framed.bind (read_plan fp rs .mip) ?_
  intro pending rs
  refine Framed.bind (read_plan fp rs .mtimecmp) ?_
  intro deadline rs
  refine Framed.bind (read_plan fp rs .mtime) ?_
  intro time rs
  refine Framed.bind (write_plan fp rs .mip
    (_root_.Sail.BitVec.updateSubrange pending 7 7 (bool_to_bit (zopz0zIzJ_u deadline time)))
    mipFull (by simp [clockRegisters])) ?_
  intro _ rs
  rw [show currentlyEnabled .Ext_Sstc = Pure.pure (hartSupports .Ext_Sstc) by
    unfold currentlyEnabled
    rfl]
  refine Framed.bind (pure_plan fp rs (hartSupports .Ext_Sstc)) ?_
  intro enabled rs
  refine Framed.bind (read_plan fp rs .menvcfg) ?_
  intro env rs
  simp only [show get_config_print_clint () = false from rfl,
    Bool.false_eq_true, ↓reduceIte, Bool.or_false]
  split
  · refine Framed.bind (read_plan fp rs .mip) ?_
    intro pending rs
    refine Framed.bind (read_plan fp rs .stimecmp) ?_
    intro deadline rs
    refine Framed.bind (read_plan fp rs .mtime) ?_
    intro time rs
    refine Framed.bind (write_plan fp rs .mip
      (_root_.Sail.BitVec.updateSubrange pending 5 5 (bool_to_bit (zopz0zIzJ_u deadline time)))
      mipFull (by simp [clockRegisters])) ?_
    intro _ rs
    exact changed_plan fp rs old
  · exact changed_plan fp rs old

/-- Actual generated eager inhibit/config reads are preserved. -/
theorem should_inc_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (priv : Privilege) :
    Framed fp rs (should_inc_mcycle priv) := by
  unfold should_inc_mcycle
  refine Framed.bind (read_plan fp rs .mcountinhibit) ?_
  intro inhibit rs
  refine Framed.bind (read_plan fp rs .mcyclecfg) ?_
  intro config rs
  exact pure_plan fp rs _

private theorem time_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (mtimeFull : (.mtime, .own 1) ∈ fp) (mipFull : (.mip, .own 1) ∈ fp) :
    Framed fp rs (do
      PreSail.writeReg .mtime (_root_.Sail.BitVec.addInt (← PreSail.readReg .mtime) 1)
      clint_dispatch false) := by
  refine Framed.bind (read_plan fp rs .mtime) ?_
  intro time rs
  refine Framed.bind (write_plan fp rs .mtime (_root_.Sail.BitVec.addInt time 1)
    mtimeFull (by simp [clockRegisters])) ?_
  intro _ rs
  exact clint_plan fp mipFull rs

/-- Source value-agnostic tick contract, with every actual generated read and
write. No mode, reset configuration, timer value or counter bound is assumed. -/
theorem clock_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (mcycleFull : (.mcycle, .own 1) ∈ fp) (mtimeFull : (.mtime, .own 1) ∈ fp)
    (mipFull : (.mip, .own 1) ∈ fp) : Framed fp rs (tick_clock ()) := by
  unfold tick_clock
  refine Framed.bind (read_plan fp rs .cur_privilege) ?_
  intro priv rs
  refine Framed.bind (should_inc_plan fp rs priv) ?_
  intro enabled rs
  cases enabled
  · exact time_plan fp rs mtimeFull mipFull
  · refine Framed.bind (read_plan fp rs .mcycle) ?_
    intro cycle rs
    refine Framed.bind (write_plan fp rs .mcycle (_root_.Sail.BitVec.addInt cycle 1)
      mcycleFull (by simp [clockRegisters])) ?_
    intro _ rs
    exact time_plan fp rs mtimeFull mipFull

theorem optional_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (mcycleFull : (.mcycle, .own 1) ∈ fp) (mtimeFull : (.mtime, .own 1) ∈ fp)
    (mipFull : (.mip, .own 1) ∈ fp) (tick : Bool) :
    Framed fp rs (if tick then tick_clock () else pure ()) := by
  cases tick
  · exact pure_plan fp rs ()
  · exact clock_plan fp rs mcycleFull mtimeFull mipFull

theorem clockFootprint_unique : RegisterFootprint.Unique clockFootprint := by
  simp [RegisterFootprint.Unique, clockFootprint]

/-- The existential footprint is exactly the source's three existential
64-bit cell values; the witness's other register fields carry no resources. -/
theorem clockRes_iff {GF : BundledGFunctors} (capacity : Registers.Capacity GF) γ :
    iprop(clockRes capacity γ ⊣⊢ ∃ (cycle time pending : BitVec 64),
      Registers.regPointsto capacity γ .mcycle (.own 1) cycle ∗
      Registers.regPointsto capacity γ .mtime (.own 1) time ∗
      Registers.regPointsto capacity γ .mip (.own 1) pending) := by
  unfold clockRes
  isplit
  · iintro ⟨%rs, Hregs⟩
    iexists rs .mcycle, rs .mtime, rs .mip
    simp only [clockFootprint, RegisterFootprint.cells]
    icases Hregs with ⟨Hcycle, Htime, Hpending, _⟩
    iframe Hcycle Htime Hpending
  · iintro ⟨%cycle, %time, %pending, Hcycle, Htime, Hpending⟩
    iexists Sail.Registers.write
      (Sail.Registers.write (Sail.Registers.write zeroRegisters .mcycle cycle) .mtime time) .mip pending
    simp [clockFootprint, RegisterFootprint.cells, Sail.Registers.write]
    iframe Hcycle Htime Hpending

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem wp_clock (fp : RegisterFootprint.Footprint) (unique : RegisterFootprint.Unique fp)
    (mcycleFull : (.mcycle, .own 1) ∈ fp) (mtimeFull : (.mtime, .own 1) ∈ fp)
    (mipFull : (.mip, .own 1) ∈ fp)
    image fixed whole gen era cpu rs (continuation : Unit → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      (∀ after, ⌜OffClock rs after⌝ -∗
        RegisterFootprint.cells capacity.era.registers (era.registers cpu) after fp -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (tick_clock () >>= continuation)) post) := by
  iintro Hcert Hregs Hfinish
  iapply RegisterPlan.fold capacity fp unique image fixed whole gen era cpu rs _ _ continuation post
    (clock_plan fp rs mcycleFull mtimeFull mipFull) $$ Hcert Hregs
  iintro %value %after %frame Hregs
  cases value
  iapply Hfinish $$ %after [] Hregs
  ipureintro
  exact frame

theorem wp_optional (fp : RegisterFootprint.Footprint) (unique : RegisterFootprint.Unique fp)
    (mcycleFull : (.mcycle, .own 1) ∈ fp) (mtimeFull : (.mtime, .own 1) ∈ fp)
    (mipFull : (.mip, .own 1) ∈ fp) (tick : Bool)
    image fixed whole gen era cpu rs (continuation : Unit → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      (∀ after, ⌜OffClock rs after⌝ -∗
        RegisterFootprint.cells capacity.era.registers (era.registers cpu) after fp -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu ((if tick then tick_clock () else pure ()) >>= continuation)) post) := by
  iintro Hcert Hregs Hfinish
  iapply RegisterPlan.fold capacity fp unique image fixed whole gen era cpu rs _ _ continuation post
    (optional_plan fp rs mcycleFull mtimeFull mipFull tick) $$ Hcert Hregs
  iintro %value %after %frame Hregs
  cases value
  iapply Hfinish $$ %after [] Hregs
  ipureintro
  exact frame

/-- The source existential three-cell clock resource is preserved by either
machine-selected tick choice, with the actual continuation still required. -/
theorem wp_clockRes (tick : Bool) image fixed whole gen era cpu
    (continuation : Unit → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      clockRes capacity.era.registers (era.registers cpu) -∗
      (clockRes capacity.era.registers (era.registers cpu) -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu ((if tick then tick_clock () else pure ()) >>= continuation)) post) := by
  iintro Hcert Hclock Hfinish
  iunfold clockRes at Hclock
  icases Hclock with ⟨%rs, Hclock⟩
  iapply wp_optional capacity clockFootprint clockFootprint_unique
    (by simp [clockFootprint]) (by simp [clockFootprint]) (by simp [clockFootprint])
    tick image fixed whole gen era cpu rs continuation post $$ Hcert Hclock
  iintro %after %_frame Hclock
  iapply Hfinish
  unfold clockRes
  iexists after
  iexact Hclock

theorem actual : Spec capacity := ⟨wp_clock capacity⟩

end MachCSL.Logic.SupervisorClock
