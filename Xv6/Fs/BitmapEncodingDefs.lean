import Xv6.Fs.BitmapDefs

/-! BitmapEnc.v's integer encoder and byte image. Signed byte positions and
all eight bits of every encoded byte are retained. -/
namespace Xv6.Fs.BitmapEncoding

/-- Least-significant-bit-first source bits_to_Z, with its exact Int carrier. -/
def bitsToInt : List Bool → Int
  | [] => 0
  | true :: rest => 2 * bitsToInt rest + 1
  | false :: rest => 2 * bitsToInt rest

def byteBits (used : BlockSet) (j : Int) : List Bool :=
  (List.range 8).map fun k : Nat => decide (8 * j + (k : Int) ∈ used)

def bitmapByte (used : BlockSet) (j : Int) : BitVec 8 :=
  BitVec.ofInt 8 (bitsToInt (byteBits used j))

def bitmapBytes (n : Nat) (used : BlockSet) : List (BitVec 8) :=
  (List.range n).map fun j : Nat => bitmapByte used (j : Int)

end Xv6.Fs.BitmapEncoding
