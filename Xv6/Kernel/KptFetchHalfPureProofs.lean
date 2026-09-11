import Xv6.Kernel.KptFetchHalfSpec
import Xv6.Kernel.KptAddressLink
import Xv6.Kernel.KernelTextDatumLink
import MachCSL.Logic.SupervisorBareFetchPlan

namespace Xv6.Kernel.KptFetchHalf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

open _root_.Sail.ConcurrencyInterfaceV1.Free

set_option maxRecDepth 10000

theorem factor start address n :
    program start address n = KptAddress.program address (.InstructionFetch ()) >>= afterTranslation n := by
  unfold program fetch_bytes KptAddress.program Sv39Address.program _root_.Sail.SailME.run
    _root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.PreSailME.run
  simp only [ext_fetch_check_pc]
  with_unfolding_all dsimp only [Function.comp_def, Bind.bind, Pure.pure, Functor.map, MonadLiftT.monadLift, MonadLift.monadLift,
    ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.lift, ExceptT.pure, ExceptT.mk,
    liftM, ExceptT, SailME, PreSailME, _root_.Sail.SailME.throw,
    _root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.PreSailME.throw, Sail.ArchSem.FreeM.bind]
  generalize translateAddr (.Virtaddr address) (.InstructionFetch ()) = trans
  induction trans with
  | impure event k ih => exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)
  | pure response =>
    cases response with
    | Err pair => rcases pair with ⟨error,ext⟩; rfl
    | Ok pair =>
      rcases pair with ⟨pa,pbmt,ext⟩
      with_unfolding_all dsimp only [Bind.bind, Pure.pure, Function.comp_def, Sail.ArchSem.FreeM.bind, ExceptT.bindCont, afterTranslation]
      generalize mem_read (.InstructionFetch ()) pbmt pa n false false false = rd
      induction rd with
      | impure event k ih => exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)
      | pure response =>
        cases response with
        | Ok word => rfl
        | Err pair =>
          rcases pair with ⟨errorAddress,error⟩
          with_unfolding_all dsimp only [Bind.bind, Pure.pure, Function.comp_def, Sail.ArchSem.FreeM.bind, ExceptT.bindCont]
          unfold _root_.Sail.assert PreSail.assert
          split
          · rfl
          · change (Sail.ArchSem.FreeM.impure (.error (.Assertion "postlude/fetch.sail:44.30-44.31")) _ : SailM (FetchBytes_Result n)) =
              (Sail.ArchSem.FreeM.impure (.error (.Assertion "postlude/fetch.sail:44.30-44.31")) _ : SailM (FetchBytes_Result n))
            congr 1
            funext impossible
            exact Empty.elim impossible

theorem aligned_iff address n :
    is_aligned_vaddr (.Virtaddr address) n = true ↔ address.toNat % n = 0 := by
  change ((Int.tmod (address.toNat : Int) n) == 0) = true ↔ address.toNat % n = 0
  change ((((address.toNat % n : Nat) : Int) == 0) = true) ↔ address.toNat % n = 0
  rw [beq_iff_eq]
  exact Int.ofNat_inj

theorem page address n (width : Supported n) (aligned : is_aligned_vaddr (.Virtaddr address) n = true) :
    KernelTextDatum.SamePage address n := by
  have h := (aligned_iff address n).mp aligned
  rcases width with rfl | rfl
  · exact KernelTextDatum.page_two address h
  · exact KernelTextDatum.page_four address h

theorem physical_nat address ppn :
    (KernelTextDatum.physical ppn address).toNat = ppn.toNat * 4096 + address.toNat % 4096 := by
  have size := ppn.isLt
  change ((BitVec.append ppn (address.extractLsb' 0 12)).setWidth 64).toNat = _
  rw [BitVec.toNat_setWidth]
  with_unfolding_all change (ppn.toNat <<< 12 ||| (address.extractLsb' 0 12).toNat) % 2^64 = _
  rw [← Nat.shiftLeft_add_eq_or_of_lt (address.extractLsb' 0 12).isLt]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.shiftLeft_eq]
  omega

theorem physical_alignment address ppn n (width : Supported n)
    (aligned : is_aligned_vaddr (.Virtaddr address) n = true) :
    is_aligned_paddr (.Physaddr (KernelTextDatum.physical ppn address)) n = true := by
  change is_aligned_vaddr (.Virtaddr (KernelTextDatum.physical ppn address)) n = true
  apply (aligned_iff _ n).mpr
  rw [physical_nat]
  have h := (aligned_iff address n).mp aligned
  rcases width with rfl | rfl <;> omega

theorem translation_success rs root step (config : Config rs) (facts : Step.Facts rs root step) :
    KptAddress.result step.address step.ppn (.InstructionFetch ()) step.outcome =
      .Ok (.Physaddr (KernelTextDatum.physical step.ppn step.address), .PBMT_PMA, ()) := by
  have enabled : KptAD.enabled (KptAddress.prepare rs step.data) = true := by
    simp [KptAD.enabled, SupervisorPteAD.enabled, config.adue]
  have h := facts.2.2.2
  simp only [enabled] at h
  cases step with
  | mk address ppn data tree p2 p1 a d branch view =>
    cases branch with
    | hit ca cd update | miss ca cd v2 v1 v0 update =>
      cases update <;> first | rfl | simp_all [KptTranslate.Branch.update, KptAD.BranchFacts]

theorem text_range address n (width : Supported n) (text : KernelTextDatum.AddrIsText address) :
    SupervisorPhysical.RamRange address n := by
  unfold SupervisorPhysical.RamRange ramLow ramHigh
  unfold KernelTextDatum.AddrIsText KernelTextDatum.textEnd at text
  rcases width with rfl | rfl <;> omega

theorem widen_plan {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

theorem widen_boundary {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {n : Nat} {req : MemoryReadWP.ReadRequest n} {program : SailM α} {tail}
    (cut : SupervisorFetchRead.Boundary small rs req program tail)
    (members : ∀ cell, cell ∈ small → cell ∈ large) :
    SupervisorFetchRead.Boundary large rs req program tail := by
  induction cut with
  | event => exact .event
  | «prefix» first _ ih => exact .prefix (widen_plan first members) ih

theorem physical_read shares rs data (config : Config rs)
    (tor : SupervisorPmp.TorRam (KptAddress.prepare rs data))
    address n (width : Supported n) (text : KernelTextDatum.AddrIsText address)
    (aligned : is_aligned_paddr (.Physaddr address) n = true) :
    SupervisorFetchRead.OneRead (KptAddress.footprint shares) (KptAddress.prepare rs data) address n
      (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr address) n false false false)
      (fun word => .Ok word) := by
  let shares' : SupervisorBareFetch.Shares :=
    ⟨KptAddress.outerShares shares, ⟨shares.pma,.own 1,.own 1,shares.htif⟩⟩
  have range := text_range address n width text
  obtain ⟨tail,cut,success,error⟩ := SupervisorBareFetch.outer_boundary shares' (KptAddress.prepare rs data)
    (by simpa using config.ambient.privilege) address n width tor range
    (by simpa using config.ambient.htif) MycpuBare.ramRegion
    (by rw [KptAddress.prepare_pma,config.ambient.pma]; exact MycpuBare.pma_ram address n (by rcases width with rfl | rfl <;> decide) range)
    (by rfl) aligned
  refine ⟨tail,widen_boundary cut ?_,success,error⟩
  intro cell member
  simp only [SupervisorBareFetch.footprint,SupervisorBare.footprint,SupervisorFetchRead.footprint,
    shares',KptAddress.outerShares,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
    simp [KptAddress.footprint,KptAddress.outerShares,KptAddress.innerShares,Sv39Address.footprint,
      SupervisorBare.footprint,KptTranslate.footprint,KptMiss.footprint,KptAD.footprint,SupervisorPteAD.footprint,
      SupervisorPteRead.footprint,SupervisorRead.footprint]

theorem nativePureSpec : PureSpec := ⟨factor,page,physical_alignment,translation_success,physical_read⟩

end Xv6.Kernel.KptFetchHalf
