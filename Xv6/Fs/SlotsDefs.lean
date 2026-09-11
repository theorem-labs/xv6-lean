import Xv6.Fs.DurableInodeDefs

namespace Xv6.Fs

/-- Source slot numbering: file slots0–267; indirect-root slot268. -/
def slot (image : Blocks) (dn : Dinode) (i : Nat) : Int :=
  if i = 268 then dn.addrZ 12 else blockAddress image dn i

def SlotInjective (image : Blocks) (dn : Dinode) : Prop :=
  ∀ i j : Nat, i ≤ 268 → j ≤ 268 → slot image dn i ≠ 0 →
    slot image dn i = slot image dn j → i = j

/-- Source concatenation shares the indirect decoder once. -/
def slotList (image : Blocks) (dn : Dinode) : List Int :=
  dn.addrZ 12 :: ((List.range 12).map dn.addrZ ++ indirectEntries image dn)

def runIndex (i : Nat) : Nat := if i = 268 then 0 else i + 1

def inodeEntries (image : Blocks) (dn : Dinode) : List Int :=
  (slotList image dn).filter (fun a => !(a == 0))

end Xv6.Fs
