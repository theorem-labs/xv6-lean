import Xv6.Kernel.PtTreeSpec
import MachCSL.Machine.PteCanonicalLink

namespace Xv6.Kernel.PtTree
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

/-- The residual Boolean after the actual five eager validation reads.
The equation below checks this transcription against generated code. -/
def invalidValue (pte_flags : BitVec 8) (pte_ext : BitVec 10)
    (environment1 isa1 isa2 environment2 isa3 : BitVec 64) : Bool :=
  (((_get_PTE_Flags_V pte_flags) == 0#1) || ((((_get_PTE_Flags_R pte_flags) == 0#1) && (((_get_PTE_Flags_W
                pte_flags) == 1#1) && (((_get_PTE_Flags_X pte_flags) == 0#1) && ((_get_MEnvcfg_SSE
                  environment1) == 0#1)))) || ((((_get_PTE_Flags_R pte_flags) == 0#1) && (((_get_PTE_Flags_W
                  pte_flags) == 1#1) && ((_get_PTE_Flags_X pte_flags) == 1#1))) || (((Bool.not
                (page_based_mem_type_forwards_matches (_get_PTE_Ext_PBMT pte_ext))) && (_get_Misa_S isa1 == 1#1)) || (pte_reserved_bits_must_be_zero && (((pte_is_non_leaf pte_flags) && (((_get_PTE_Flags_A
                        pte_flags) == 1#1) || (((_get_PTE_Flags_D pte_flags) == 1#1) || (((_get_PTE_Flags_U
                            pte_flags) == 1#1) || (pte_ext != (zeros (n := 10))))))) || ((((_get_PTE_Ext_N
                        pte_ext) != (zeros (n := 1))) && (Bool.not (_get_Misa_S isa2 == 1#1))) || ((((_get_PTE_Ext_PBMT
                          pte_ext) != (zeros (n := 2))) && (((_get_MEnvcfg_PBMTE
                            environment2) == 0#1) || (Bool.not
                          (page_based_mem_type_forwards_matches (_get_PTE_Ext_PBMT pte_ext))))) || ((((_get_PTE_Ext_RSW_60t59b
                            pte_ext) != (zeros (n := 2))) && (Bool.not
                          (_get_Misa_S isa3 == 1#1))) || ((_get_PTE_Ext_reserved
                          pte_ext) != (zeros (n := 5))))))))))))

theorem validation_eq (w : Word) : validation w = (do
    let environment1 ← _root_.Sail.readReg .menvcfg
    let isa1 ← _root_.Sail.readReg .misa
    let isa2 ← _root_.Sail.readReg .misa
    let environment2 ← _root_.Sail.readReg .menvcfg
    let isa3 ← _root_.Sail.readReg .misa
    pure (invalidValue (PteCanonical.flags w) (ext_bits_of_PTE w)
      environment1 isa1 isa2 environment2 isa3)) := by
  unfold validation pte_is_invalid
  simp only [currentlyEnabled]
  apply congrArg (fun k : BitVec 64 → SailM Bool => _root_.Sail.readReg .menvcfg >>= k)
  funext environment1
  apply congrArg (fun k : BitVec 64 → SailM Bool => _root_.Sail.readReg .misa >>= k)
  funext isa1
  apply congrArg (fun k : BitVec 64 → SailM Bool => _root_.Sail.readReg .misa >>= k)
  funext isa2
  apply congrArg (fun k : BitVec 64 → SailM Bool => _root_.Sail.readReg .menvcfg >>= k)
  funext environment2
  apply congrArg (fun k : BitVec 64 → SailM Bool => _root_.Sail.readReg .misa >>= k)
  funext isa3
  simp [invalidValue, hartSupports, LeanPaperStock.Functions.not, LeanPaperStock.Functions.xlen]

theorem registerRun_result_unique {α : Type} (fuel fuel' : Nat) (program : SailM α)
    (rs : RegisterFile) (x y : α × RegisterFile)
    (hx : registerRun fuel program rs = some x)
    (hy : registerRun fuel' program rs = some y) : x = y := by
  induction fuel generalizing fuel' program rs with
  | zero => simp [registerRun] at hx
  | succ fuel ih =>
    cases fuel' with
    | zero => simp [registerRun] at hy
    | succ fuel' =>
      cases program with
      | pure value => exact Option.some.inj (hx.symm.trans hy)
      | impure event k =>
        cases event <;> simp only [registerRun] at hx hy
        all_goals first | contradiction | exact ih _ _ _ hx hy

theorem validation_run (w : Word) (rs : RegisterFile) :
    registerRun 6 (validation w) rs = some
      (invalidValue (PteCanonical.flags w) (ext_bits_of_PTE w)
        (rs .menvcfg) (rs .misa) (rs .misa) (rs .menvcfg) (rs .misa), rs) := by
  rw [validation_eq]
  rfl

theorem outcome_value (w : Word) (answer : Bool) (h : Outcome w answer) (rs : RegisterFile) :
    invalidValue (PteCanonical.flags w) (ext_bits_of_PTE w)
      (rs .menvcfg) (rs .misa) (rs .misa) (rs .menvcfg) (rs .misa) = answer := by
  obtain ⟨fuel, good⟩ := h rs
  exact congrArg Prod.fst (registerRun_result_unique 6 fuel _ rs _ _ (validation_run w rs) good)

theorem outcome_unique (w : Word) (a b : Bool) (ha : Outcome w a) (hb : Outcome w b) : a = b := by
  let rs : RegisterFile := fun r => by cases r <;> exact default
  exact (outcome_value w a ha rs).symm.trans (outcome_value w b hb rs)

theorem valid_invalid (w : Word) (hv : Valid w) (hi : Invalid w) : False := by
  have bad := outcome_unique w false true hv hi
  cases bad

end Xv6.Kernel.PtTree
