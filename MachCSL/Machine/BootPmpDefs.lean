import MachCSL.Machine.BootUniversalDefs

/-! Exact generated PMP reset, retaining every preboot field except A and L. -/
namespace MachCSL.Machine.BootPmp
open LeanPaperStock.Functions

def clearEntry (entry : BitVec 8) : BitVec 8 :=
  _update_Pmpcfg_ent_L (_update_Pmpcfg_ent_A entry (pmpAddrMatchType_encdec_forwards .OFF)) 0#1

def resetPrefix : Nat → Vector (BitVec 8) 64 → Vector (BitVec 8) 64
  | 0, entries => entries
  | n + 1, entries =>
    let current := resetPrefix n entries
    current.set! n (clearEntry current[(n : Int)]!)

/-- All 64 entries are disabled and unlocked; no condition on address vectors
or unrelated configuration bits is part of this predicate. -/
def Off (rs : RegisterFile) : Prop := ∀ i : Fin 64,
  _get_Pmpcfg_ent_L ((rs .pmpcfg_n)[i.val]) = 0#1 ∧
  _get_Pmpcfg_ent_A ((rs .pmpcfg_n)[i.val]) = 0#2

def resetRange : IntRange := ⟨0, 63, 1, by decide⟩
def resetBody (i : Int) (_ : i ∈ resetRange) (_ : Unit) : SailM (ForInStep Unit) := do
  let current ← _root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.readReg Register.pmpcfg_n
  let readAgain ← _root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.readReg Register.pmpcfg_n
  _root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.writeReg Register.pmpcfg_n
    (current.set! i.toNat (clearEntry readAgain[i]!))
  pure (.yield ())
def resetLoop (i : Nat) : SailM Unit :=
  IntRange.forIn'.loop resetRange resetBody () (i : Int) (by simp [resetRange])

end MachCSL.Machine.BootPmp
