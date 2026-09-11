import Xv6.Fs.RecoveryDefs

namespace Xv6.Fs.Recovery.Examples

/-- One full log header whose only destination is block 47. -/
def header : List (BitVec 8) :=
  word32Bytes 1 ++ word32Bytes 47 ++ List.replicate 1016 0

def coverage : BlockSet := Std.ExtTreeSet.ofList [(47 : Int)]

/-- At start 2, slot 0 contains 42. The dirty example has raw home byte 7;
the equal example already has 42 there. All physical blocks remain full. -/
def physical (changed : Bool) : Blocks := fun b =>
  if b = 2 then header else
  if b = 47 ∧ changed = true then List.replicate 1024 7 else List.replicate 1024 42

end Xv6.Fs.Recovery.Examples
