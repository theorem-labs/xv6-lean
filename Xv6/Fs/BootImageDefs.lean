import Xv6.Fs.ValidityDefs
import Xv6.Fs.DurableLinksDefs

/-! Exact pure initial-image contract from FsCfgBoot.v:584–652 and
FsBoot.v:86 at xv6iris arxiv-v1. This is an initial image premise; later
reboots require the separately defined durable snapshot contract. -/
namespace Xv6.Fs

/-- A covered block is positive and its last byte lies in the disk mint. -/
def CovIn (cov : BlockSet) (ndisk : Nat) : Prop :=
  ∀ b : Int, b ∈ cov → 0 < b ∧ 1024 * (b + 1) ≤ (ndisk : Int)

/-- All fifteen source premises, in source order. -/
structure BootImageWF (disk : Disk) (ndisk : Nat) (sb : Superblock)
    (nib : Nat) (cov : BlockSet) : Prop where
  image : fsimgValid (blocks disk) sb = true
  region : regionValid (blocks disk) sb nib = true
  advertised : sb.ninodes ≤ 16 * (nib : Int)
  wordBound : 16 * (nib : Int) ≤ 2 ^ 32
  positive : 0 < nib
  rounded : (nib : Int) = sb.ninodes / 16 + 1
  coverage : CovIn cov ndisk
  metadata : ∀ b : Int, 1 ≤ b ∧ b < dataStart sb → b ∈ cov
  data : ∀ b : Int, dataStart sb ≤ b ∧ b < sb.size → b ∈ cov
  parsed : parseSuperblock (blocks disk) = some sb
  ushortBound : 16 * (nib : Int) ≤ 2 ^ 16
  diskBound : (ndisk : Int) ≤ 1024 * sb.size
  links : linksEqual (blocks disk) sb = true
  bare : regionBare (blocks disk) sb nib = true
  rootSelf : rootNoSelf (blocks disk) sb = true

/-- Finite coverage of positive block numbers below a natural endpoint. -/
def blockCoverage (count : Nat) : BlockSet :=
  Std.ExtTreeSet.ofList ((List.range (count - 1)).map fun i : Nat => (i : Int) + 1)

end Xv6.Fs
