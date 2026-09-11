import Xv6.Kernel.MycpuFetchDefs
import Xv6.Kernel.MycpuFetchBytesProofs
import MachCSL.Logic.SupervisorBareFetchPlan

namespace Xv6.Kernel.MycpuFetch
open Iris MachCSL.Memory MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem returns_bind {fp rs} {program : SailM α} {next : α → SailM β} {value result}
    (first : RegisterPlan.Returns fp rs program value rs)
    (rest : RegisterPlan.Returns fp rs (next value) result rs) :
    RegisterPlan.Returns fp rs (program >>= next) result rs :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (pure value) value rs := .pure ⟨rfl, rfl⟩

private theorem read_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (r : Register) (dq : DFrac) (member : (r, dq) ∈ fp) :
    RegisterPlan.Returns fp rs (PreSail.readReg r) (rs r) rs := .read member (.pure ⟨rfl, rfl⟩)

private theorem lift_except {fp rs} {program : SailM α} {value}
    (first : RegisterPlan.Returns fp rs program value rs) (ε : Type) :
    RegisterPlan.Returns fp rs (monadLift program : SailME ε α).run (.ok value) rs := by
  exact returns_bind first (pure_plan fp rs _)

private theorem widen_plan {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

private theorem widen_boundary {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {n : Nat} {req : MemoryReadWP.ReadRequest n} {program : SailM α} {tail}
    (cut : SupervisorFetchRead.Boundary small rs req program tail)
    (members : ∀ cell, cell ∈ small → cell ∈ large) :
    SupervisorFetchRead.Boundary large rs req program tail := by
  induction cut with
  | event => exact .event
  | «prefix» first _ ih => exact .prefix (widen_plan first members) ih

theorem FixedRead.bind {fp rs address n word} {program : SailM α} {value}
    (before : FixedRead fp rs address n word program value) (next : α → SailM β)
    (result : β) (finish : next value = pure result) :
    FixedRead fp rs address n word (program >>= next) result := by
  obtain ⟨tail, cut, success, error⟩ := before
  refine ⟨fun response => tail response >>= next, cut.bind next, ?_, ?_⟩
  · intro tag
    dsimp only
    rw [success]
    exact finish
  · dsimp only
    rw [error]
    change (Sail.ArchSem.FreeM.impure (.error Sail.Error.Exit)
      (fun x : Empty => (Empty.elim x : SailM α) >>= next) : SailM β) =
      Sail.ArchSem.FreeM.impure (.error Sail.Error.Exit) Empty.elim
    congr 1
    funext impossible
    exact Empty.elim impossible

theorem FixedRead.prefix {fp rs address n word} {segment : SailM β} {value}
    {next : β → SailM α} {result}
    (first : RegisterPlan.Returns fp rs segment value rs)
    (rest : FixedRead fp rs address n word (next value) result) :
    FixedRead fp rs address n word (segment >>= next) result := by
  obtain ⟨tail, cut, success, error⟩ := rest
  exact ⟨tail, .prefix first cut, success, error⟩

private theorem fixed_lift {fp rs address n word} {program : SailM α} {value}
    (first : FixedRead fp rs address n word program value) (ε : Type) :
    FixedRead fp rs address n word (monadLift program : SailME ε α).run (.ok value) :=
  first.bind _ _ rfl

theorem address_aligned : ∀ i : Fin 14,
    is_aligned_paddr (.Physaddr (MycpuDecode.address i)) (MycpuFetchBytes.width i) = true := by decide

theorem address_bit0 : ∀ i : Fin 14, Sail.BitVec.access (MycpuDecode.address i) 0 = 0#1 := by decide

theorem address_range (i : Fin 14) : SupervisorPhysical.RamRange (MycpuDecode.address i)
    (MycpuFetchBytes.width i) := by
  have finite : ∀ i : Fin 14, SupervisorPhysical.RamRange (MycpuDecode.address i) (MycpuFetchBytes.width i) := by
    unfold SupervisorPhysical.RamRange
    decide
  exact finite i

/-- Every two-byte footprint contains a complete compressed instruction. -/
theorem short_compressed : ∀ i : Fin 14, MycpuFetchBytes.width i = 2 →
    isRVC (BitVec.ofNat 16 (MycpuFetchBytes.encoding i)) = true := by decide

theorem fetched_classification (i : Fin 14) :
    (if isRVC ((MycpuFetchBytes.word i).setWidth 16) then
      FetchResult.F_RVC ((MycpuFetchBytes.word i).setWidth 16)
    else .F_Base ((MycpuFetchBytes.word i).setWidth 32)) = result i := by
  have marks : ∀ i : Fin 14, isRVC ((MycpuFetchBytes.word i).setWidth 16) = MycpuDecode.compressed i := by decide
  rw [marks]
  unfold result
  split
  · rw [MycpuFetchBytes.low_halfword]
  · next h => rw [MycpuFetchBytes.base_word i (Bool.eq_false_iff.mpr h)]

/-- One real misa read, including when alignment bit1 makes its value irrelevant. -/
theorem zca_plan (shares : Shares) (rs : RegisterFile) (enabled : _get_Misa_C (rs .misa) = 1#1) :
    RegisterPlan.Returns (footprint shares) rs (currentlyEnabled .Ext_Zca) true rs := by
  have c : RegisterPlan.Returns (footprint shares) rs (currentlyEnabled .Ext_C) true rs := by
    unfold currentlyEnabled
    refine returns_bind (read_plan (fp := footprint shares) rs .misa shares.misa (by simp [footprint])) ?_
    rw [enabled]
    simp only [hartSupports, beq_self_eq_true, Bool.and_self]
    exact pure_plan (footprint shares) rs _
  unfold currentlyEnabled
  refine returns_bind c ?_
  simp only [hartSupports, Bool.true_or, Bool.and_self]
  exact pure_plan (footprint shares) rs _

private theorem bytes_cut (shares : Shares) (rs : RegisterFile) (i : Fin 14) (region : PMA_Region)
    (config : Config rs i region) :
    FixedRead (footprint shares) rs (MycpuDecode.address i) (MycpuFetchBytes.width i)
      (MycpuFetchBytes.word i) (fetch_bytes (MycpuDecode.address i) (MycpuDecode.address i) (MycpuFetchBytes.width i))
      (.FetchBytes_Success (MycpuFetchBytes.word i)) := by
  obtain ⟨tail, cut, success, error⟩ := SupervisorBareFetch.fetch_boundary shares.bare rs config.bare
    (MycpuDecode.address i) (MycpuDecode.address i) (MycpuFetchBytes.width i) (MycpuFetchBytes.supported_width i)
    config.pmp (address_range i) config.htif region config.matched config.executable (address_aligned i)
  refine ⟨tail, widen_boundary cut ?_, success _, error⟩
  intro cell member
  exact List.mem_append_right _ member

private theorem low_extract (word : BitVec 32) :
    Sail.BitVec.extractLsb word 15 0 = word.setWidth 16 := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']

/-- The actual full fetch retains its arbitrary-response residual; only the
owned concrete word is proved to finish after this one memory event. -/
theorem fetch_cut [Platform] (shares : Shares) (rs : RegisterFile) (i : Fin 14) (region : PMA_Region)
    (config : Config rs i region) :
    FixedRead (footprint shares) rs (MycpuDecode.address i) (MycpuFetchBytes.width i)
      (MycpuFetchBytes.word i) (fetch ()) (result i) := by
  unfold fetch _root_.Sail.SailME.run PreSail.PreSailME.run
  refine FixedRead.bind (value := Except.ok (result i)) ?_ _ _ (by rfl)
  refine FixedRead.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  refine FixedRead.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  rw [config.pc]
  refine FixedRead.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  refine FixedRead.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  refine FixedRead.prefix (lift_except (zca_plan shares rs config.compressed) FetchResult) ?_
  rw [config.pc]
  simp only [ExceptT.bindCont, LeanPaperStock.Functions.not, address_bit0, bne_self_eq_false, Bool.not_true, Bool.and_false,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  refine FixedRead.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  have ziccif : RegisterPlan.Returns (footprint shares) rs (currentlyEnabled .Ext_Ziccif) true rs := by
    rw [MycpuFetchBytes.ziccif_enabled]
    exact pure_plan _ _ _
  refine FixedRead.prefix (lift_except ziccif FetchResult) ?_
  rw [config.pc]
  simp only [ExceptT.bindCont, Bool.and_true]
  have base := bytes_cut shares rs i region config
  by_cases aligned : is_aligned_vaddr (.Virtaddr (MycpuDecode.address i)) 4 = true
  · simp only [aligned, ↓reduceIte]
    refine FixedRead.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
    refine FixedRead.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
    rw [config.pc]
    have width : MycpuFetchBytes.width i = 4 := by simp [MycpuFetchBytes.width, aligned]
    simp only [MycpuFetchBytes.word] at base ⊢
    rw [width] at base ⊢
    simp only [ExceptT.bindCont]
    refine FixedRead.bind (fixed_lift base FetchResult) _ _ ?_
    have classify := fetched_classification i
    simp only [MycpuFetchBytes.word] at classify
    rw [width] at classify
    simp only [Nat.reduceMul, BitVec.setWidth_eq] at classify
    rw [← classify]
    simp only [ExceptT.bindCont, Nat.reduceMul, BitVec.setWidth_eq, low_extract]
    split <;> with_unfolding_all rfl
  · simp only [aligned]
    refine FixedRead.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
    refine FixedRead.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
    rw [config.pc]
    have width : MycpuFetchBytes.width i = 2 := by simp [MycpuFetchBytes.width, aligned]
    simp only [MycpuFetchBytes.word] at base ⊢
    rw [width] at base ⊢
    simp only [ExceptT.bindCont]
    refine FixedRead.bind (fixed_lift base FetchResult) _ _ ?_
    have compressed := short_compressed i width
    have classify := fetched_classification i
    simp only [MycpuFetchBytes.word] at classify
    rw [width] at classify
    simp only [Nat.reduceMul, BitVec.setWidth_eq, compressed, ↓reduceIte] at classify
    simp only [ExceptT.bindCont, Nat.reduceMul, BitVec.setWidth_eq, compressed, ↓reduceIte]
    with_unfolding_all exact congrArg (fun value => (pure (Except.ok value) : SailM (Except FetchResult FetchResult))) classify

end Xv6.Kernel.MycpuFetch
