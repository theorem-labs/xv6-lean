import MachCSL.Logic.SupervisorRetirementSpec
import MachCSL.Logic.SupervisorRetirementFactorProofs
import MachCSL.Logic.RegisterPlanProofs
import MachCSL.Logic.SupervisorClockProofs

namespace MachCSL.Logic.SupervisorRetirement
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

private theorem returns_bind {fp : RegisterFootprint.Footprint}
    {rs middle after : RegisterFile} {program : SailM α} {next : α → SailM β}
    {value : α} {result : β} (first : RegisterPlan.Returns fp rs program value middle)
    (rest : RegisterPlan.Returns fp middle (next value) result after) :
    RegisterPlan.Returns fp rs (program >>= next) result after :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (.pure value) value rs := .pure ⟨rfl, rfl⟩

private theorem read_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (r : Register) (dq : DFrac) (member : (r, dq) ∈ fp) :
    RegisterPlan.Returns fp rs (PreSail.readReg r) (rs r) rs :=
  .read member (.pure ⟨rfl, rfl⟩)

private theorem write_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (r : Register) (value : RegisterType r) (member : (r, .own 1) ∈ fp) :
    RegisterPlan.Returns fp rs (PreSail.writeReg r value) ()
      (Sail.Registers.write rs r value) := .write member (.pure ⟨rfl, rfl⟩)

/-- Both generated config reads are retained, even when IR inhibits counting. -/
theorem should_inc_plan [Platform] (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (mc cfg : DFrac) (readMC : (.mcountinhibit, mc) ∈ fp)
    (readCfg : (.minstretcfg, cfg) ∈ fp) (priv : Privilege) :
    RegisterPlan.Returns fp rs (should_inc_minstret priv)
      (flag (rs .mcountinhibit) (rs .minstretcfg) priv) rs := by
  unfold should_inc_minstret
  exact returns_bind (read_plan fp rs _ mc readMC)
    (returns_bind (read_plan fp rs _ cfg readCfg) (pure_plan fp rs _))

theorem setup_plan [Platform] (fp : RegisterFootprint.Footprint) (members : SetupMembers fp)
    (rs : RegisterFile) :
    RegisterPlan.Returns fp rs setup () (setupAfter rs (rs .cur_privilege)) := by
  unfold setup
  refine returns_bind (read_plan fp rs _ members.privilege members.readPrivilege) ?_
  refine returns_bind (should_inc_plan fp rs members.inhibit members.config
    members.readInhibit members.readConfig _) ?_
  exact write_plan fp rs _ _ members.writeFlag

/-- Without privilege ownership the actual read is universally covered, not pinned
by the symbolic file. The returned witness records that independent read value. -/
theorem setup_any_privilege_plan [Platform] (fp : RegisterFootprint.Footprint)
    (rs : RegisterFile) (mc cfg : DFrac) (readMC : (.mcountinhibit, mc) ∈ fp)
    (readCfg : (.minstretcfg, cfg) ∈ fp) (writeFlag : (.minstret_increment, .own 1) ∈ fp) :
    RegisterPlan.Plan fp rs setup
      (fun result after => result = () ∧ ∃ priv, after = setupAfter rs priv) := by
  unfold setup
  apply RegisterPlan.Plan.readAny
  intro priv
  apply RegisterPlan.Plan.mono (returns_bind
    (should_inc_plan fp rs mc cfg readMC readCfg priv) (write_plan fp rs _ _ writeFlag))
  intro result after same
  exact ⟨same.1, priv, same.2⟩

theorem tick_pc_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (dq : DFrac) (readNext : (.nextPC, dq) ∈ fp) (writePC : (.PC, .own 1) ∈ fp) :
    RegisterPlan.Returns fp rs (tick_pc ()) () (tickPCAfter rs) := by
  unfold tick_pc
  refine returns_bind (read_plan fp rs _ dq readNext) ?_
  refine returns_bind (write_plan fp rs _ _ writePC) ?_
  refine returns_bind (read_plan fp _ _ (.own 1) writePC) ?_
  exact pure_plan fp _ _

@[simp] theorem tickPC_flag (rs : RegisterFile) :
    tickPCAfter rs .minstret_increment = rs .minstret_increment := by
  simp [tickPCAfter, Sail.Registers.write]

@[simp] theorem tickPC_counter (rs : RegisterFile) :
    tickPCAfter rs .minstret = rs .minstret := by
  simp [tickPCAfter, Sail.Registers.write]

/-- Every successful postlude event, including both hart reads and the final PC
callback read. The post-body flag is arbitrary and remains unchanged. -/
theorem complete_plan [Platform] (fp : RegisterFootprint.Footprint)
    (members : CompleteMembers fp) (rs : RegisterFile)
    (active : rs .hart_state = .HART_ACTIVE ()) (bits : BitVec 32) :
    RegisterPlan.Returns fp rs (postlude (.Step_Execute (.Retire_Success (), bits)))
      false (completeAfter rs) := by
  unfold postlude
  refine returns_bind (read_plan fp rs _ members.hart members.readHart) ?_
  rw [active]
  refine returns_bind (pure_plan fp rs ()) ?_
  refine returns_bind (read_plan fp rs _ members.hart members.readHart) ?_
  rw [active]
  refine returns_bind (tick_pc_plan fp rs members.next members.readNext members.writePC) ?_
  refine returns_bind (read_plan fp _ _ members.readFlag members.readFlagMember) ?_
  simp only [tickPC_flag, Bool.true_and]
  split
  · rename_i enabled
    refine returns_bind (read_plan fp _ _ (.own 1) members.writeCounter) ?_
    refine returns_bind (write_plan fp _ _ _ members.writeCounter) ?_
    simp only [get_config_rvfi, Bool.false_eq_true, ↓reduceIte]
    apply RegisterPlan.Plan.pure
    exact ⟨rfl, by simp [completeAfter, enabled]⟩
  · rename_i inhibited
    simp only [get_config_rvfi, Bool.false_eq_true, ↓reduceIte]
    apply RegisterPlan.Plan.pure
    exact ⟨rfl, by simp [completeAfter, inhibited]⟩

@[simp] theorem complete_pc (rs : RegisterFile) : completeAfter rs .PC = rs .nextPC := by
  unfold completeAfter
  split <;> simp [tickPCAfter, Sail.Registers.write]

@[simp] theorem complete_nextPC (rs : RegisterFile) : completeAfter rs .nextPC = rs .nextPC := by
  unfold completeAfter
  split <;> simp [tickPCAfter, Sail.Registers.write]

@[simp] theorem complete_flag (rs : RegisterFile) :
    completeAfter rs .minstret_increment = rs .minstret_increment := by
  unfold completeAfter
  split <;> simp [tickPCAfter, Sail.Registers.write]

theorem complete_counter (rs : RegisterFile) :
    completeAfter rs .minstret = if rs .minstret_increment then
      _root_.Sail.BitVec.addInt (rs .minstret) 1 else rs .minstret := by
  unfold completeAfter
  split <;> simp [tickPCAfter, Sail.Registers.write, *]

theorem complete_other (rs : RegisterFile) (r : Register) (notPC : r ≠ .PC)
    (notCounter : r ≠ .minstret) : completeAfter rs r = rs r := by
  unfold completeAfter
  split <;> simp [tickPCAfter, Sail.Registers.write, Ne.symm notPC, Ne.symm notCounter]

theorem setup_flag (rs : RegisterFile) (priv : Privilege) :
    setupAfter rs priv .minstret_increment = flag (rs .mcountinhibit) (rs .minstretcfg) priv := by
  simp [setupAfter, Sail.Registers.write]

theorem setup_other (rs : RegisterFile) (priv : Privilege) (r : Register)
    (different : r ≠ .minstret_increment) : setupAfter rs priv r = rs r := by
  simp [setupAfter, Sail.Registers.write, Ne.symm different]

theorem retirementFootprint_unique : RegisterFootprint.Unique retirementFootprint := by
  simp [RegisterFootprint.Unique, retirementFootprint]

theorem pcFootprint_unique : RegisterFootprint.Unique pcFootprint := by
  simp [RegisterFootprint.Unique, pcFootprint, retirementFootprint, SupervisorClock.clockFootprint]

/-- Exact source existential cell values; the other fields of the witness file
are unowned and carry no reset hypothesis. -/
theorem minstretRes_iff {GF : BundledGFunctors} (capacity : Registers.Capacity GF) name :
    iprop(minstretRes capacity name ⊣⊢ ∃ (counter : BitVec 64) (increment : Bool)
      (inhibit : BitVec 32) (config : BitVec 64),
      Registers.regPointsto capacity name .minstret (.own 1) counter ∗
      Registers.regPointsto capacity name .minstret_increment (.own 1) increment ∗
      Registers.regPointsto capacity name .mcountinhibit .discard inhibit ∗
      Registers.regPointsto capacity name .minstretcfg .discard config) := by
  unfold minstretRes
  isplit
  · iintro ⟨%rs, Hregs⟩
    iexists rs .minstret, rs .minstret_increment, rs .mcountinhibit, rs .minstretcfg
    simp only [retirementFootprint, RegisterFootprint.cells]
    icases Hregs with ⟨Hcounter, Hflag, Hinhibit, Hconfig, _⟩
    iframe Hcounter Hflag Hinhibit Hconfig
  · iintro ⟨%counter, %increment, %inhibit, %config, Hcounter, Hflag, Hinhibit, Hconfig⟩
    iexists Sail.Registers.write (Sail.Registers.write
      (Sail.Registers.write (Sail.Registers.write zeroRegisters .minstret counter)
        .minstret_increment increment) .mcountinhibit inhibit) .minstretcfg config
    simp [retirementFootprint, RegisterFootprint.cells, Sail.Registers.write]
    iframe Hcounter Hflag Hinhibit Hconfig

theorem pcFootprint_split {GF : BundledGFunctors} (capacity : Registers.Capacity GF) name rs :
    iprop(RegisterFootprint.cells capacity name rs pcFootprint ⊣⊢
      Registers.regPointsto capacity name .PC (.own 1) (rs .PC) ∗
      Registers.regPointsto capacity name .nextPC (.own 1) (rs .nextPC) ∗
      RegisterFootprint.cells capacity name rs retirementFootprint ∗
      RegisterFootprint.cells capacity name rs SupervisorClock.clockFootprint) := by
  simp only [pcFootprint, retirementFootprint, SupervisorClock.clockFootprint,
    List.cons_append, List.nil_append, RegisterFootprint.cells]
  isplit
  · iintro ⟨Hpc, Hnext, Hms, Hflag, Hmc, Hcfg, Hcy, Htime, Hip, _⟩
    iframe Hpc Hnext Hms Hflag Hmc Hcfg Hcy Htime Hip
  · iintro ⟨Hpc, Hnext, ⟨Hms, Hflag, Hmc, Hcfg, _⟩, Hcy, Htime, Hip, _⟩
    iframe Hpc Hnext Hms Hflag Hmc Hcfg Hcy Htime Hip

/-- The combined finite footprint plus exactly the original reservation token
reassembles the source boundary resource. -/
theorem pcIs_intro {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    era cpu (rs : RegisterFile) (pc : BitVec 64) (pcEq : rs .PC = pc)
    (nextEq : rs .nextPC = pc) :
    iprop(⊢ RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs pcFootprint -∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu -∗
      pcIs capacity era cpu pc) := by
  rw [(pcFootprint_split capacity.era.registers (era.registers cpu) rs).to_eq]
  rw [pcEq, nextEq]
  iintro ⟨Hpc, Hnext, Hretire, Hclock⟩ Hresv
  unfold pcIs
  iframe Hpc Hnext Hresv
  isplitl [Hretire]
  · unfold minstretRes
    iexists rs
    iexact Hretire
  · unfold SupervisorClock.clockRes
    iexists rs
    iexact Hclock

/-- One common symbolic file packages independent source values without adding
ownership for any other register. This is a split/join equivalence. -/
theorem pcIs_iff {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF) era cpu pc :
    iprop(pcIs capacity era cpu pc ⊣⊢ ∃ rs : RegisterFile,
      ⌜rs .PC = pc ∧ rs .nextPC = pc⌝ ∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs pcFootprint ∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu) := by
  isplit
  · unfold pcIs
    rw [(minstretRes_iff capacity.era.registers (era.registers cpu)).to_eq,
      (SupervisorClock.clockRes_iff capacity.era.registers (era.registers cpu)).to_eq]
    iintro ⟨Hpc, Hnext, Hretire, Hclock, Hresv⟩
    icases Hretire with ⟨%counter, %increment, %inhibit, %config, Hcounter, Hflag, Hinhibit, Hconfig⟩
    icases Hclock with ⟨%cycle, %time, %pending, Hcycle, Htime, Hpending⟩
    iexists Sail.Registers.write (Sail.Registers.write (Sail.Registers.write
      (Sail.Registers.write (Sail.Registers.write (Sail.Registers.write
        (Sail.Registers.write (Sail.Registers.write (Sail.Registers.write zeroRegisters .PC pc)
          .nextPC pc) .minstret counter) .minstret_increment increment) .mcountinhibit inhibit)
            .minstretcfg config) .mcycle cycle) .mtime time) .mip pending
    simp [pcFootprint, retirementFootprint, SupervisorClock.clockFootprint,
      RegisterFootprint.cells, Sail.Registers.write]
    iframe Hpc Hnext Hcounter Hflag Hinhibit Hconfig Hcycle Htime Hpending Hresv
  · iintro ⟨%rs, %eq, Hregs, Hresv⟩
    iapply pcIs_intro capacity era cpu rs pc eq.1 eq.2 $$ Hregs Hresv

theorem pcIs_parts {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF) era cpu pc :
    iprop(pcIs capacity era cpu pc ⊣⊢
      pcRegs capacity.era.registers (era.registers cpu) pc ∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu) := by
  unfold pcIs pcRegs
  isplit
  · iintro ⟨Hpc, Hnext, Hretire, Hclock, Hresv⟩
    iframe Hpc Hnext Hretire Hclock Hresv
  · iintro ⟨⟨Hpc, Hnext, Hretire, Hclock⟩, Hresv⟩
    iframe Hpc Hnext Hretire Hclock Hresv

/-- Completion followed by either actual clock choice. Exact non-clock values
are preserved even though each unowned clock read is independently universal. -/
theorem complete_clock_plan [Platform] (fp : RegisterFootprint.Footprint)
    (members : CompleteMembers fp) (rs : RegisterFile)
    (active : rs .hart_state = .HART_ACTIVE ()) (bits : BitVec 32)
    (mcycleFull : (.mcycle, .own 1) ∈ fp) (mtimeFull : (.mtime, .own 1) ∈ fp)
    (mipFull : (.mip, .own 1) ∈ fp) (tick : Bool) :
    RegisterPlan.Plan fp rs (do
      let _ ← postlude (.Step_Execute (.Retire_Success (), bits))
      if tick then tick_clock () else pure ())
      (fun _ after => SupervisorClock.OffClock (completeAfter rs) after) :=
  RegisterPlan.Plan.bind (complete_plan fp members rs active bits) fun _ after same => by
    rw [same.2]
    exact SupervisorClock.optional_plan fp (completeAfter rs) mcycleFull mtimeFull mipFull tick

theorem completed_clock_pc (rs after : RegisterFile)
    (frame : SupervisorClock.OffClock (completeAfter rs) after) :
    after .PC = rs .nextPC ∧ after .nextPC = rs .nextPC := by
  constructor
  · exact (frame .PC (by simp [SupervisorClock.clockRegisters])).trans (complete_pc rs)
  · exact (frame .nextPC (by simp [SupervisorClock.clockRegisters])).trans (complete_nextPC rs)

theorem completed_clock_counter (rs after : RegisterFile)
    (frame : SupervisorClock.OffClock (completeAfter rs) after) :
    after .minstret = (if rs .minstret_increment then
      _root_.Sail.BitVec.addInt (rs .minstret) 1 else rs .minstret) ∧
    after .minstret_increment = rs .minstret_increment := by
  constructor
  · exact (frame .minstret (by simp [SupervisorClock.clockRegisters])).trans (complete_counter rs)
  · exact (frame .minstret_increment (by simp [SupervisorClock.clockRegisters])).trans (complete_flag rs)

/-- Full source boundary reassembly after the successful tail and optional clock.
The reservation token is the original framed resource, not a new allocation. -/
theorem pcIs_completed {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    era cpu rs after (frame : SupervisorClock.OffClock (completeAfter rs) after) :
    iprop(⊢ RegisterFootprint.cells capacity.era.registers (era.registers cpu) after pcFootprint -∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu -∗
      pcIs capacity era cpu (rs .nextPC)) :=
  pcIs_intro capacity era cpu after (rs .nextPC)
    (completed_clock_pc rs after frame).1 (completed_clock_pc rs after frame).2

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

private theorem wp_returns {A : Type} (fp : RegisterFootprint.Footprint)
    (unique : RegisterFootprint.Unique fp) image fixed whole gen era cpu rs
    (program : SailM A) (value : A) (after : RegisterFile)
    (continuation : A → SailM Unit) post (plan : RegisterPlan.Returns fp rs program value after) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu) after fp -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation value)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  iintro Hcert Hregs Hfinish
  iapply RegisterPlan.fold capacity fp unique image fixed whole gen era cpu rs program _ continuation post
    plan $$ Hcert Hregs
  iintro %result %file %same Hregs
  rcases same with ⟨rfl, rfl⟩
  iapply Hfinish $$ Hregs

theorem wp_setup (fp : RegisterFootprint.Footprint) (unique : RegisterFootprint.Unique fp)
    (members : SetupMembers fp) image fixed whole gen era cpu rs
    (continuation : Unit → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu)
          (setupAfter rs (rs .cur_privilege)) fp -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (setup >>= continuation)) post) :=
  wp_returns capacity fp unique image fixed whole gen era cpu rs _ _ _ continuation post
    (setup_plan fp members rs)

theorem wp_tick_pc (fp : RegisterFootprint.Footprint) (unique : RegisterFootprint.Unique fp)
    (dq : DFrac) (readNext : (.nextPC, dq) ∈ fp) (writePC : (.PC, .own 1) ∈ fp)
    image fixed whole gen era cpu rs (continuation : Unit → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu) (tickPCAfter rs) fp -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (tick_pc () >>= continuation)) post) :=
  wp_returns capacity fp unique image fixed whole gen era cpu rs _ _ _ continuation post
    (tick_pc_plan fp rs dq readNext writePC)

theorem wp_complete (fp : RegisterFootprint.Footprint) (unique : RegisterFootprint.Unique fp)
    (members : CompleteMembers fp) image fixed whole gen era cpu rs
    (active : rs .hart_state = .HART_ACTIVE ()) bits (continuation : Bool → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu) (completeAfter rs) fp -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation false)) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (postlude (.Step_Execute (.Retire_Success (), bits)) >>= continuation)) post) :=
  wp_returns capacity fp unique image fixed whole gen era cpu rs _ _ _ continuation post
    (complete_plan fp members rs active bits)

theorem wp_complete_clock (fp : RegisterFootprint.Footprint) (unique : RegisterFootprint.Unique fp)
    (members : CompleteMembers fp) image fixed whole gen era cpu rs
    (active : rs .hart_state = .HART_ACTIVE ()) bits
    (mcycleFull : (.mcycle, .own 1) ∈ fp) (mtimeFull : (.mtime, .own 1) ∈ fp)
    (mipFull : (.mip, .own 1) ∈ fp) (tick : Bool)
    (continuation : Unit → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      (∀ after, ⌜SupervisorClock.OffClock (completeAfter rs) after⌝ -∗
        RegisterFootprint.cells capacity.era.registers (era.registers cpu) after fp -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu ((do
        let _ ← postlude (.Step_Execute (.Retire_Success (), bits))
        if tick then tick_clock () else pure ()) >>= continuation)) post) := by
  iintro Hcert Hregs Hfinish
  iapply RegisterPlan.fold capacity fp unique image fixed whole gen era cpu rs _ _ continuation post
    (complete_clock_plan fp members rs active bits mcycleFull mtimeFull mipFull tick) $$ Hcert Hregs
  iintro %value %after %frame Hregs
  cases value
  iapply Hfinish $$ %after [] Hregs
  ipureintro
  exact frame

/-- Value-agnostic clock WP for the whole source `pc_is`; its counter and
reservation resources are framed through every clock subevent. -/
theorem wp_clock_pcIs (tick : Bool) image fixed whole gen era cpu pc
    (continuation : Unit → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      pcIs capacity era cpu pc -∗
      (pcIs capacity era cpu pc -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu ((if tick then tick_clock () else pure ()) >>= continuation)) post) := by
  iintro Hcert HpcIs Hfinish
  iunfold pcIs at HpcIs
  icases HpcIs with ⟨Hpc, Hnext, Hretire, Hclock, Hresv⟩
  iapply SupervisorClock.wp_clockRes capacity tick image fixed whole gen era cpu continuation post
    $$ Hcert Hclock
  iintro Hclock
  iapply Hfinish
  unfold pcIs
  iframe Hpc Hnext Hretire Hclock Hresv

theorem actual : Spec capacity := ⟨wp_setup capacity, wp_tick_pc capacity, wp_complete capacity⟩

end MachCSL.Logic.SupervisorRetirement
