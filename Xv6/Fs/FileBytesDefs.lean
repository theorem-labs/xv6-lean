import Xv6.Fs.TreeDiskDefs

namespace Xv6.Fs

def takeBlocks (data : FileData) (start : Nat) : Nat → List (BitVec 8)
  | 0 => []
  | n + 1 => data start ++ takeBlocks data (start + 1) n


end Xv6.Fs
