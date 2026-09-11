import LeanPaperStock.VmemPte
import MachCSL.Logic.TsoDefs
import MachCSL.Memory.ReadBytes

/-! Exact A/D variant and leaf-conditioned byte family from PtAdBits/PtTree. -/
namespace MachCSL.Machine.PteCanonical
open LeanPaperStock.Functions MachCSL.Memory

def flags (word : BitVec 64) : BitVec 8 :=
  Mk_PTE_Flags (_root_.Sail.BitVec.extractLsb word 7 0)

def setAD (word : BitVec 64) (a d : BitVec 1) : BitVec 64 :=
  _root_.Sail.BitVec.updateSubrange word 7 0
    (_update_PTE_Flags_D (_update_PTE_Flags_A (flags word) a) d)

def canon (word : BitVec 64) : BitVec 64 := setAD word 0#1 0#1
def nonleaf (word : BitVec 64) : Bool := pte_is_non_leaf (flags word)
def Leaf (word : BitVec 64) : Prop := nonleaf word = false

def adByte0 (word : BitVec 64) : Logic.Tso.ByteSet :=
  {nthByte (setAD word 0#1 0#1) 0, nthByte (setAD word 0#1 1#1) 0,
   nthByte (setAD word 1#1 0#1) 0, nthByte (setAD word 1#1 1#1) 0}

def slotSet (word : BitVec 64) (j : Nat) : Logic.Tso.ByteSet :=
  if j = 0 then
    if nonleaf word then {nthByte word 0} else adByte0 word
  else {nthByte word j}

def WritebackOK (old new : BitVec 64) : Prop :=
  Leaf old ∧ ∀ j, j < 8 → nthByte new j ∈ slotSet old j

end MachCSL.Machine.PteCanonical
