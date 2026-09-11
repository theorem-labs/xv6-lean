import Xv6.Kernel.KptFetchPureProofs

namespace Xv6.Kernel.KptFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem Plan.bind {fp rs chunks} {program : SailM α} {value}
    (before : Plan fp rs chunks program value) (next : α → SailM β)
    (result : β) (finish : next value = Pure.pure result) :
    Plan fp rs chunks (program >>= next) result := by
  induction before with
  | pure value => rw [BootPmp.sail_pure_bind,finish]; exact .pure _
  | «prefix» first rest ih =>
    rw [BootPmp.sail_bind_assoc]
    exact .prefix first (ih finish)
  | chunk part width aligned rest ih =>
    rw [BootPmp.sail_bind_assoc]
    exact .chunk part width aligned (ih finish)

theorem Plan.seq {fp rs left right} {program : SailM α} {value}
    (before : Plan fp rs left program value) (next : α → SailM β) {result : β}
    (rest : Plan fp rs right (next value) result) :
    Plan fp rs (left ++ right) (program >>= next) result := by
  induction before with
  | pure value => exact rest
  | «prefix» first tail ih =>
    rw [BootPmp.sail_bind_assoc]
    exact .prefix first (ih rest)
  | chunk part width aligned tail ih =>
    rw [BootPmp.sail_bind_assoc]
    exact .chunk part width aligned (ih rest)

theorem returns_bind {fp rs} {program : SailM α} {next : α → SailM β} {value result}
    (first : RegisterPlan.Returns fp rs program value rs)
    (rest : RegisterPlan.Returns fp rs (next value) result rs) :
    RegisterPlan.Returns fp rs (program >>= next) result rs :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl,rfl⟩ => rest

theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (pure value) value rs := .pure ⟨rfl,rfl⟩

theorem read_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (r : Register) (dq : DFrac) (member : (r,dq) ∈ fp) :
    RegisterPlan.Returns fp rs (_root_.Sail.readReg r) (rs r) rs := .read member (.pure ⟨rfl,rfl⟩)

theorem lift_except {fp rs} {program : SailM α} {value}
    (first : RegisterPlan.Returns fp rs program value rs) (ε : Type) :
    RegisterPlan.Returns fp rs (monadLift program : SailME ε α).run (.ok value) rs := by
  exact returns_bind first (pure_plan fp rs _)

theorem plan_lift {fp rs chunks} {program : SailM α} {value}
    (before : Plan fp rs chunks program value) (ε : Type) :
    Plan fp rs chunks (monadLift program : SailME ε α).run (.ok value) :=
  before.bind _ _ rfl

theorem zca_plan (shares : Shares) (rs : RegisterFile) (enabled : _get_Misa_C (rs .misa) = 1#1) :
    RegisterPlan.Returns (footprint shares) rs (currentlyEnabled .Ext_Zca) true rs := by
  have c : RegisterPlan.Returns (footprint shares) rs (currentlyEnabled .Ext_C) true rs := by
    unfold currentlyEnabled
    refine returns_bind (read_plan (fp := footprint shares) rs .misa shares.misa (by simp [footprint])) ?_
    rw [enabled]
    simp only [hartSupports,beq_self_eq_true,Bool.and_self]
    exact pure_plan _ _ _
  unfold currentlyEnabled
  refine returns_bind c ?_
  simp only [hartSupports,Bool.true_or,Bool.and_self]
  exact pure_plan _ _ _

theorem part_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (part : Chunk)
    (width : KptFetchHalf.Supported part.width)
    (aligned : is_aligned_vaddr (.Virtaddr part.address) part.width = true) :
    Plan fp rs [part] (KptFetchHalf.program part.start part.address part.width) (.FetchBytes_Success part.word) := by
  have p := Plan.chunk (fp := fp) (rs := rs) part (next := pure) width aligned (Plan.pure (FetchBytes_Result.FetchBytes_Success part.word))
  simpa only [EventPlan.sail_bind_pure_eq] using p

theorem fetch_plan shares rs (compressed : _get_Misa_C (rs .misa) = 1#1)
    (aligned : is_aligned_vaddr (.Virtaddr (rs .PC)) 2 = true) (word : BitVec 32) :
    Plan (footprint shares) rs (parts (rs .PC) word) program (classified word) := by
  unfold program fetch _root_.Sail.SailME.run PreSail.PreSailME.run
  refine Plan.bind (value := Except.ok (classified word)) ?_ _ _ (by rfl)
  refine Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  refine Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  refine Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  refine Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  refine Plan.prefix (lift_except (zca_plan shares rs compressed) FetchResult) ?_
  simp only [ExceptT.bindCont,LeanPaperStock.Functions.not,bit0 _ aligned,bne_self_eq_false,
    Bool.not_true,Bool.and_false,Bool.false_or,Bool.false_eq_true,↓reduceIte]
  refine Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  have ziccif : RegisterPlan.Returns (footprint shares) rs (currentlyEnabled .Ext_Ziccif) true rs := by
    unfold currentlyEnabled hartSupports
    exact pure_plan _ _ _
  refine Plan.prefix (lift_except ziccif FetchResult) ?_
  simp only [ExceptT.bindCont,Bool.and_true]
  by_cases four : is_aligned_vaddr (.Virtaddr (rs .PC)) 4 = true
  · simp only [four,↓reduceIte,parts]
    refine Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
    refine Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
    apply Plan.bind (plan_lift (part_plan (footprint shares) rs ⟨rs .PC,rs .PC,4,word⟩ (Or.inr rfl) four) FetchResult)
    simp only [ExceptT.bindCont,Nat.reduceMul,BitVec.setWidth_eq,low_cast,classified]
    split <;> rfl
  · have fourFalse : is_aligned_vaddr (.Virtaddr (rs .PC)) 4 = false := Bool.eq_false_iff.mpr four
    simp only [fourFalse,Bool.false_eq_true,↓reduceIte,parts]
    refine Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
    refine Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
    by_cases rvc : isRVC (KernelTextDatum.lowHalf word) = true
    · simp only [rvc,↓reduceIte]
      apply Plan.bind (plan_lift (part_plan (footprint shares) rs
        ⟨rs .PC,rs .PC,2,KernelTextDatum.lowHalf word⟩ (Or.inl rfl) aligned) FetchResult)
      simp only [ExceptT.bindCont,Nat.reduceMul,BitVec.setWidth_eq,rvc,↓reduceIte,classified]
      rfl
    · have rvcFalse : isRVC (KernelTextDatum.lowHalf word) = false := Bool.eq_false_iff.mpr rvc
      simp only [rvcFalse,Bool.false_eq_true,↓reduceIte]
      apply Plan.seq (right := [⟨rs .PC,addressAdd (rs .PC) 2,2,KernelTextDatum.highHalf word⟩])
        (plan_lift (part_plan (footprint shares) rs
          ⟨rs .PC,rs .PC,2,KernelTextDatum.lowHalf word⟩ (Or.inl rfl) aligned) FetchResult)
      simp only [ExceptT.bindCont,Nat.reduceMul,BitVec.setWidth_eq,rvcFalse,Bool.false_eq_true,↓reduceIte]
      refine Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
      refine Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
      apply Plan.bind (plan_lift (part_plan (footprint shares) rs
        ⟨rs .PC,addressAdd (rs .PC) 2,2,KernelTextDatum.highHalf word⟩ (Or.inl rfl) (next_two _ aligned)) FetchResult)
      simp only [ExceptT.bindCont,Nat.reduceMul,BitVec.setWidth_eq,classified,rvcFalse,Bool.false_eq_true,↓reduceIte]
      change Sail.ArchSem.FreeM.pure (Except.ok (FetchResult.F_Base (BitVec.append (KernelTextDatum.highHalf word) (KernelTextDatum.lowHalf word)))) =
        Sail.ArchSem.FreeM.pure (Except.ok (FetchResult.F_Base word))
      rw [halves]

end Xv6.Kernel.KptFetch
