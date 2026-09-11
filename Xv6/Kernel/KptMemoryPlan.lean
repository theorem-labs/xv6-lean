import Xv6.Kernel.KptMemoryPure
import Xv6.Kernel.Sv39AddressPure
import MachCSL.Logic.SupervisorBareWriteGeometry
import MachCSL.Logic.SupervisorMemOuterPlan
import MachCSL.Logic.SupervisorReadProofs

namespace Xv6.Kernel.KptMemory
open Iris MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
open Sv39Address (Boundary)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private theorem bind_returns {fp : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {next : α → SailM β} {value : α} {result : β}
    (first : RegisterPlan.Returns fp rs program value rs)
    (rest : RegisterPlan.Returns fp rs (next value) result rs) :
    RegisterPlan.Returns fp rs (program >>= next) result rs :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl,rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (pure value) value rs := .pure ⟨rfl,rfl⟩

private theorem lift_except {fp : RegisterFootprint.Footprint} {program : SailM α}
    {rs : RegisterFile} {value : α} (plan : RegisterPlan.Returns fp rs program value rs) (ε : Type) :
    RegisterPlan.Returns fp rs (monadLift program : SailME ε α).run (.ok value) rs := by
  change RegisterPlan.Returns fp rs (program >>= fun a => pure (Except.ok a)) (.ok value) rs
  exact bind_returns plan (pure_plan fp rs _)

private theorem prefix_except {fp rs} {body : SailM α} {segment : SailME ε γ} {value : γ}
    {next : γ → SailME ε β} {tail}
    (before : RegisterPlan.Returns fp rs segment.run (.ok value) rs)
    (after : Boundary fp rs body (next value).run tail) :
    Boundary fp rs body (segment >>= next).run tail := .prefix before after

private theorem boundary_body_eq {fp rs} {body : SailM α} {program : SailM β} {tail : α → SailM β}
    (eq : program = body >>= tail) : Boundary fp rs body program tail := by
  rw [eq]; exact .body _

private theorem boundary_bind {fp rs} {body : SailM α} {program : SailM β} {tail : α → SailM β}
    (cut : Boundary fp rs body program tail) (next : β → SailM γ) :
    Boundary fp rs body (program >>= next) (fun value => tail value >>= next) := by
  induction cut with
  | body => rw [BootPmp.sail_bind_assoc]; exact .body _
  | «prefix» first rest ih => rw [BootPmp.sail_bind_assoc]; exact .prefix first ih

private theorem boundary_bind_eq {fp rs} {body : SailM α} {program : SailM β} {tail : α → SailM β}
    (cut : Boundary fp rs body program tail) (next : β → SailM γ) (out : α → SailM γ)
    (eq : ∀ value, tail value >>= next = out value) :
    Boundary fp rs body (program >>= next) out := by
  have same : (fun value => tail value >>= next) = out := funext eq
  rw [← same]; exact boundary_bind cut next

theorem mode shares rs data root (ambient : Ambient rs)
    (rooted : KptResidue.SatpRooted root data.satp) :
    RegisterPlan.Returns (KptAddress.footprint shares) (KptAddress.prepare rs data)
      (translationMode .Supervisor) .Sv39 (KptAddress.prepare rs data) := by
  apply widen_plan (Sv39Address.mode (KptAddress.outerShares shares) _ root
    (KptAddress.outer rs data root ambient.address rooted))
  intro cell member; exact List.mem_append_left _ member

theorem effective shares rs data (ambient : Ambient rs) kind :
    RegisterPlan.Returns (KptAddress.footprint shares) (KptAddress.prepare rs data)
      (SupervisorMemOuter.effective (access kind)) .Supervisor (KptAddress.prepare rs data) := by
  apply widen_plan (SupervisorMemOuter.effective_plan ⟨shares.status,shares.privilege⟩ _ _
    (by simpa using ambient.address.privilege) (Or.inr (by simpa using ambient.mprv)))
  intro cell member
  simp only [SupervisorMemOuter.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    simp [KptAddress.footprint, KptAddress.outerShares, Sv39Address.footprint, SupervisorBare.footprint]

theorem read_boundary [Platform] shares rs data root (ambient : Ambient rs)
    (rooted : KptResidue.SatpRooted root data.satp) va (aligned : TsoContextWord.Aligned va) :
    Boundary (KptAddress.footprint shares) (KptAddress.prepare rs data)
      (KptAddress.program va (.Load .Data)) (addressProgram .load va 0#64) (readAfterAddress va) := by
  have ha : is_aligned_vaddr (.Virtaddr va) 8 = true := SupervisorRead.alignment va aligned
  have page := SupervisorBareWrite.split_page_eight va aligned
  have hm := mode shares rs data root ambient rooted
  have he := effective shares rs data ambient .load
  unfold addressProgram vmem_read_addr _root_.Sail.SailME.run PreSail.PreSailME.run
  simp only [ha, LeanPaperStock.Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bits_of_virtaddr, page]
  apply boundary_bind_eq (tail := fun response =>
    readAfterAddress va response >>= fun value => pure (match value with
      | .Ok word => Except.ok (.Ok word : Result .load)
      | .Err failure => Except.error (.Err failure : Result .load)))
  · apply prefix_except (value := ((8, 0) : Int × Int)) (pure_plan _ _ _)
    apply prefix_except (value := Privilege.Supervisor) (lift_except he _)
    apply prefix_except (value := SATPMode.Sv39) (lift_except hm _)
    apply prefix_except (value := false) (pure_plan _ _ _)
    apply prefix_except (value := (0#64)) (pure_plan _ _ _)
    apply boundary_body_eq
    unfold Result
    unfold translate_and_read_value
    simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    unfold KptAddress.program Sv39Address.program
    dsimp only [Bind.bind, Pure.pure, Functor.map, MonadLiftT.monadLift, MonadLift.monadLift,
      ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.lift, ExceptT.pure, ExceptT.mk, liftM, ExceptT, SailME, PreSailME, _root_.Sail.SailME.throw, PreSail.PreSailME.throw, Sail.ArchSem.FreeM.bind]
    generalize translateAddr (.Virtaddr va) (.Load .Data) = trans
    induction trans with
    | impure event k ih =>
      apply congrArg (Sail.ArchSem.FreeM.impure event)
      funext value
      exact ih value
    | pure response =>
      cases response with
      | Err pair =>
        rcases pair with ⟨error,ext⟩
        dsimp only [Bind.bind, Pure.pure, Functor.map, MonadLiftT.monadLift, MonadLift.monadLift,
          ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.lift, ExceptT.pure, ExceptT.mk, liftM, ExceptT, SailME, PreSailME, _root_.Sail.SailME.throw, PreSail.PreSailME.throw,
          Sail.ArchSem.FreeM.bind, readAfterAddress]
        generalize memory_exception (.Virtaddr va) error = failed
        induction failed with
        | pure result => rfl
        | impure event k ih => exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)
      | Ok pair =>
        rcases pair with ⟨pa,pbmt,ext⟩
        dsimp only [Bind.bind, Pure.pure, Functor.map, MonadLiftT.monadLift, MonadLift.monadLift,
          ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.lift, ExceptT.pure, ExceptT.mk, liftM, ExceptT, SailME, PreSailME, _root_.Sail.SailME.throw, PreSail.PreSailME.throw,
          Sail.ArchSem.FreeM.bind, readAfterAddress]
        unfold ExceptT.bindCont
        generalize hread : mem_read (.Load .Data) pbmt pa
          (if false = true then (8 : Int) else ↑(8 : Nat)).toNat false false false = read
        have right : mem_read (.Load .Data) pbmt pa 8 false false false = read := hread
        rw [right]
        clear hread right
        induction read with
        | impure event k ih => exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)
        | pure response =>
          cases response with
          | Ok word =>
            change pure (Except.ok (.Ok (Sail.BitVec.updateSubrange (0#64) 63 0 (word.setWidth 64)))) =
              (pure (Except.ok (.Ok word)) : SailM (Except (Result .load) (Result .load)))
            have cast : word.setWidth 64 = word := BitVec.setWidth_eq word
            have full : Sail.BitVec.updateSubrange (0#64) 63 0 (word.setWidth 64) = word :=
              (SupervisorRead.full_word (0#64) (word.setWidth 64)).trans cast
            exact congrArg (fun value : BitVec 64 =>
              (pure (Except.ok (.Ok value : Result .load)) : SailM (Except (Result .load) (Result .load)))) full
          | Err pair =>
            rcases pair with ⟨excPa,error⟩
            dsimp only [Sail.ArchSem.FreeM.bind, readAfterMemory]
            generalize memory_exception (offset_virtaddr_by (.Virtaddr va) pa excPa) error = failed
            induction failed with
            | pure value => rfl
            | impure event k ih => exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)
  · intro response
    generalize readAfterAddress va response = resultProgram
    induction resultProgram with
    | impure event k ih => exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)
    | pure value => cases value <;> rfl


theorem write_boundary [Platform] shares rs data root (ambient : Ambient rs)
    (rooted : KptResidue.SatpRooted root data.satp) va new (aligned : TsoContextWord.Aligned va) :
    Boundary (KptAddress.footprint shares) (KptAddress.prepare rs data)
      (KptAddress.program va (.Store .Data)) (addressProgram .store va new) (writeAfterAddress va new) := by
  have ha : is_aligned_vaddr (.Virtaddr va) 8 = true := SupervisorRead.alignment va aligned
  have page := SupervisorBareWrite.split_page_eight va aligned
  have hm := mode shares rs data root ambient rooted
  have he := effective shares rs data ambient .store
  unfold addressProgram vmem_write_addr _root_.Sail.SailME.run PreSail.PreSailME.run
  simp only [ha, LeanPaperStock.Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bits_of_virtaddr, page]
  apply boundary_bind_eq (tail := fun response =>
    writeAfterAddress va new response >>= fun value => pure (match value with
      | .Ok success => Except.ok (.Ok success : Result .store)
      | .Err failure => Except.error (.Err failure : Result .store)))
  · apply prefix_except (value := ((8, 0) : Int × Int)) (pure_plan _ _ _)
    apply prefix_except (value := Privilege.Supervisor) (lift_except he _)
    apply prefix_except (value := SATPMode.Sv39) (lift_except hm _)
    apply prefix_except (value := false) (pure_plan _ _ _)
    apply prefix_except (value := true) (pure_plan _ _ _)
    apply boundary_body_eq
    unfold Result KptAddress.program Sv39Address.program
    dsimp only [Bind.bind, Pure.pure, Functor.map, MonadLiftT.monadLift, MonadLift.monadLift,
      ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.lift, ExceptT.pure, ExceptT.mk, liftM,
      ExceptT, SailME, PreSailME, _root_.Sail.SailME.throw, PreSail.PreSailME.throw, Sail.ArchSem.FreeM.bind]
    generalize translateAddr (.Virtaddr va) (.Store .Data) = trans
    induction trans with
    | impure event k ih => exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)
    | pure response =>
      cases response with
      | Err pair =>
        rcases pair with ⟨error,ext⟩
        dsimp only [Bind.bind, Pure.pure, Sail.ArchSem.FreeM.bind, Function.comp_def, ExceptT.bindCont,
          _root_.Sail.assert, PreSail.assert, is_store_conditional, Bool.and, sys_misaligned_order_decreasing, writeAfterAddress]
        generalize memory_exception (.Virtaddr va) error = failed
        induction failed with
        | pure value => rfl
        | impure event k ih => exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)
      | Ok pair =>
        rcases pair with ⟨pa,pbmt,ext⟩
        dsimp only [Bind.bind, Pure.pure, Sail.ArchSem.FreeM.bind, Function.comp_def, ExceptT.bindCont,
          _root_.Sail.assert, PreSail.assert, is_store_conditional, Bool.and, sys_misaligned_order_decreasing, writeAfterAddress]
        generalize hea : mem_write_ea pa (if false = true then (8 : Int) else ↑(8 : Nat)).toNat
          (.Store .Data) pbmt false false false = ea
        have right : mem_write_ea pa 8 (.Store .Data) pbmt false false false = ea := hea
        rw [right]
        clear hea right
        induction ea with
        | impure event k ih => exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)
        | pure response =>
          cases response with
          | Err pair =>
            rcases pair with ⟨excPa,error⟩
            dsimp only [Bind.bind, Pure.pure, Sail.ArchSem.FreeM.bind, Function.comp_def, ExceptT.bindCont,
          _root_.Sail.assert, PreSail.assert, is_store_conditional, Bool.and, sys_misaligned_order_decreasing, writeAfterEA]
            generalize memory_exception (offset_virtaddr_by (.Virtaddr va) pa excPa) error = failed
            induction failed with
            | pure value => rfl
            | impure event k ih => exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)
          | Ok done =>
            cases done
            dsimp only [Bind.bind, Pure.pure, Sail.ArchSem.FreeM.bind, Function.comp_def, ExceptT.bindCont,
          _root_.Sail.assert, PreSail.assert, is_store_conditional, Bool.and, sys_misaligned_order_decreasing, writeAfterEA]
            generalize hwrite : mem_write_value pa
              (if false = true then (8 : Int) else ↑(8 : Nat)).toNat
              ((Sail.BitVec.extractLsb new ((8 * (if false = true then (8 : Int) else ↑(8 : Nat))) - 1).toNat 0).setWidth
                (8 * (if false = true then (8 : Int) else ↑(8 : Nat)).toNat))
              (.Store .Data) pbmt false false false = written
            have sliced : (Sail.BitVec.extractLsb new 63 0).setWidth 64 = new := by
              rw [SupervisorWrite.full_word, BitVec.setWidth_eq]
            have right : mem_write_value pa 8 new (.Store .Data) pbmt false false false = written := by
              have equal : mem_write_value pa 8 ((Sail.BitVec.extractLsb new 63 0).setWidth 64)
                  (.Store .Data) pbmt false false false = written := hwrite
              rw [sliced] at equal
              exact equal
            rw [right]
            clear hwrite right
            induction written with
            | impure event k ih => exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)
            | pure response =>
              cases response with
              | Ok success => rfl
              | Err pair =>
                rcases pair with ⟨excPa,error⟩
                dsimp only [Bind.bind, Pure.pure, Sail.ArchSem.FreeM.bind, Function.comp_def, ExceptT.bindCont,
          _root_.Sail.assert, PreSail.assert, is_store_conditional, Bool.and, sys_misaligned_order_decreasing, writeAfterMemory]
                generalize memory_exception (offset_virtaddr_by (.Virtaddr va) pa excPa) error = failed
                induction failed with
                | pure value => rfl
                | impure event k ih => exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)
  · intro response
    generalize writeAfterAddress va new response = resultProgram
    induction resultProgram with
    | impure event k ih => exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)
    | pure value => cases value <;> rfl

theorem address [Platform] shares rs data root (ambient : Ambient rs)
    (rooted : KptResidue.SatpRooted root data.satp) va new kind (aligned : TsoContextWord.Aligned va) :
    Boundary (KptAddress.footprint shares) (KptAddress.prepare rs data)
      (KptAddress.program va (access kind)) (addressProgram kind va new) (afterAddress kind va new) := by
  cases kind with
  | load => exact read_boundary shares rs data root ambient rooted va aligned
  | store => exact write_boundary shares rs data root ambient rooted va new aligned

theorem nativePureSpec [Platform] : PureSpec :=
  ⟨transform, address, completed, read_address_error, read_memory_error, write_address_error,
    write_ea_error, write_memory_error, write_false⟩

end Xv6.Kernel.KptMemory
