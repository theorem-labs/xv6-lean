import Xv6.Kernel.BareJalFetchSpec
import Xv6.Kernel.KptFetchPlanProofs
import MachCSL.Logic.SupervisorBareFetchProofs

namespace Xv6.Kernel.BareJalFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
open KptFetch (returns_bind pure_plan read_plan lift_except plan_lift part_plan bit0 next_two low_cast halves)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem factor : program = KptFetch.factor SupervisorBareFetch.program := rfl

theorem unique shares : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique,footprint,SupervisorBareFetch.footprint,
    SupervisorBare.footprint,SupervisorFetchRead.footprint]

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

theorem fetch_plan shares rs (compressed : _get_Misa_C (rs .misa) = 1#1)
    (aligned : is_aligned_vaddr (.Virtaddr (rs .PC)) 2 = true) (word : BitVec 32) :
    Plan (footprint shares) rs (KptFetch.parts (rs .PC) word) program (KptFetch.classified word) := by
  unfold program KptFetch.program fetch _root_.Sail.SailME.run PreSail.PreSailME.run
  refine KptFetch.Plan.bind (value := Except.ok (KptFetch.classified word)) ?_ _ _ (by rfl)
  refine KptFetch.Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  refine KptFetch.Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  refine KptFetch.Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  refine KptFetch.Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  refine KptFetch.Plan.prefix (lift_except (zca_plan shares rs compressed) FetchResult) ?_
  simp only [ExceptT.bindCont,LeanPaperStock.Functions.not,bit0 _ aligned,bne_self_eq_false,
    Bool.not_true,Bool.and_false,Bool.false_or,Bool.false_eq_true,↓reduceIte]
  refine KptFetch.Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
  have ziccif : RegisterPlan.Returns (footprint shares) rs (currentlyEnabled .Ext_Ziccif) true rs := by
    unfold currentlyEnabled hartSupports
    exact pure_plan _ _ _
  refine KptFetch.Plan.prefix (lift_except ziccif FetchResult) ?_
  simp only [ExceptT.bindCont,Bool.and_true]
  by_cases four : is_aligned_vaddr (.Virtaddr (rs .PC)) 4 = true
  · simp only [four,↓reduceIte,KptFetch.parts]
    refine KptFetch.Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
    refine KptFetch.Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
    apply KptFetch.Plan.bind (plan_lift (part_plan (footprint shares) rs ⟨rs .PC,rs .PC,4,word⟩ (Or.inr rfl) four) FetchResult)
    simp only [ExceptT.bindCont,Nat.reduceMul,BitVec.setWidth_eq,low_cast,KptFetch.classified]
    split <;> rfl
  · have fourFalse : is_aligned_vaddr (.Virtaddr (rs .PC)) 4 = false := Bool.eq_false_iff.mpr four
    simp only [fourFalse,Bool.false_eq_true,↓reduceIte,KptFetch.parts]
    refine KptFetch.Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
    refine KptFetch.Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
    by_cases rvc : isRVC (KernelTextDatum.lowHalf word) = true
    · simp only [rvc,↓reduceIte]
      apply KptFetch.Plan.bind (plan_lift (part_plan (footprint shares) rs
        ⟨rs .PC,rs .PC,2,KernelTextDatum.lowHalf word⟩ (Or.inl rfl) aligned) FetchResult)
      simp only [ExceptT.bindCont,Nat.reduceMul,BitVec.setWidth_eq,rvc,↓reduceIte,KptFetch.classified]
      rfl
    · have rvcFalse : isRVC (KernelTextDatum.lowHalf word) = false := Bool.eq_false_iff.mpr rvc
      simp only [rvcFalse,Bool.false_eq_true,↓reduceIte]
      apply KptFetch.Plan.seq (right := [⟨rs .PC,addressAdd (rs .PC) 2,2,KernelTextDatum.highHalf word⟩])
        (plan_lift (part_plan (footprint shares) rs
          ⟨rs .PC,rs .PC,2,KernelTextDatum.lowHalf word⟩ (Or.inl rfl) aligned) FetchResult)
      simp only [ExceptT.bindCont,Nat.reduceMul,BitVec.setWidth_eq,rvcFalse,Bool.false_eq_true,↓reduceIte]
      refine KptFetch.Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
      refine KptFetch.Plan.prefix (lift_except (read_plan (fp := footprint shares) rs .PC shares.pc (by simp [footprint])) FetchResult) ?_
      apply KptFetch.Plan.bind (plan_lift (part_plan (footprint shares) rs
        ⟨rs .PC,addressAdd (rs .PC) 2,2,KernelTextDatum.highHalf word⟩ (Or.inl rfl) (next_two _ aligned)) FetchResult)
      simp only [ExceptT.bindCont,Nat.reduceMul,BitVec.setWidth_eq,KptFetch.classified,rvcFalse,Bool.false_eq_true,↓reduceIte]
      change Sail.ArchSem.FreeM.pure (Except.ok (FetchResult.F_Base (BitVec.append (KernelTextDatum.highHalf word) (KernelTextDatum.lowHalf word)))) =
        Sail.ArchSem.FreeM.pure (Except.ok (FetchResult.F_Base word))
      rw [halves]

theorem physical shares rs (config : Config rs) start address n
    (width : SupervisorFetchRead.Supported n)
    (aligned : is_aligned_vaddr (.Virtaddr address) n = true)
    (text : KernelTextDatum.AddrIsText address) :
    SupervisorFetchRead.OneRead (footprint shares) rs address n
      (SupervisorBareFetch.program start address n) (fun word => .FetchBytes_Success word) := by
  have range := KptFetchHalf.text_range address n width text
  obtain ⟨tail,cut,success,error⟩ := SupervisorBareFetch.fetch_boundary shares.bare rs config.bare
    start address n width config.tor range config.htif MycpuBare.ramRegion
    (by rw [config.pma]; exact MycpuBare.pma_ram address n (by rcases width with rfl | rfl <;> decide) range)
    (by rfl) aligned
  exact ⟨tail,KptFetchHalf.widen_boundary cut (fun _ h => List.mem_append_right _ h),success,error⟩

theorem nativePureSpec : PureSpec := ⟨factor,unique,(fun shares rs word c a => fetch_plan shares rs c a word),physical⟩

end Xv6.Kernel.BareJalFetch
