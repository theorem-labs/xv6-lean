import Xv6.Fs.DurableStateDefs

/-! Exact signed home-set and finite committed-view definitions from LogDefs.v. -/
namespace Xv6.Fs.SnapshotHome
open DurableState

def logBlocks : Nat := 30
def logHeader (start : Int) : Int := start
def logSlot (start : Int) (i : Nat) : Int := start + 1 + (i : Int)
def logRegion (start : Int) : BlockSet :=
  (Std.ExtTreeSet.ofList ((List.range logBlocks).map (logSlot start))).insert (logHeader start)
def homeSet (coverage : BlockSet) (start : Int) : BlockSet := coverage \ logRegion start

/-- A missing committed block reads the empty list, not a full zero block. -/
def view (disk : BlockMap) : Blocks := fun b => disk[b]?.getD []

/-- Set enumeration is immaterial: each occurrence carries that key's same value. -/
def restrict (image : Blocks) (covered : BlockSet) : BlockMap :=
  covered.toList.foldr (fun b m => m.insert b (image b)) ∅

def homeMap (image : Blocks) (coverage : BlockSet) (start : Int) : BlockMap :=
  restrict image (homeSet coverage start)

end Xv6.Fs.SnapshotHome
