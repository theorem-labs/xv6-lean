import Xv6.Elf.ImageRepresentation

/-! Ordered sparse imports of the paper's `list_to_map` byte tables.
Authorship note: researched and written by OpenAI Codex on Jason Gross's behalf.
-/
namespace Xv6.Kernel

/-- A consecutive subsequence of the original ordered byte entries. The length
is explicit: zero high bytes are entries, while addresses outside remain absent. -/
structure ByteRun where
  base : Int
  length : Nat
  payload : Nat
  deriving Repr, DecidableEq

def ByteRun.byte (run : ByteRun) (i : Nat) : UInt8 :=
  ((run.payload >>> (8 * i)) % 256).toUInt8

def ByteRun.lookup (run : ByteRun) : Elf.MemoryImage := fun address =>
  if 0 ≤ address - run.base ∧ address - run.base < (run.length : Int) then
    some (run.byte (address - run.base).toNat)
  else none

def ByteRun.entries (run : ByteRun) : List (Int × UInt8) :=
  (List.range run.length).map fun (i : Nat) => (run.base + (i : Int), run.byte i)

/-- Lookup meaning of stdpp `list_to_map`: earlier entries win, including duplicates. -/
def listMap {α : Type} : List (Int × α) → Int → Option α
  | [], _ => none
  | (key, value) :: rest, address => if key = address then some value else listMap rest address

/-- Source run order is significant; no sorting or last-writer conversion occurs. -/
def runMap (runs : List ByteRun) : Elf.MemoryImage :=
  runs.foldr (fun run rest => Elf.union run.lookup rest) (fun _ => none)

structure Instruction where
  address : Int
  width : Nat
  encoding : Int
  deriving Repr, DecidableEq

structure Segment where
  address : Int
  fileSize : Int
  memorySize : Int
  flags : Int
  deriving Repr, DecidableEq

/-- Section metadata is imported from KernelData.v's allocated-section comment,
which the pinned dumper derives from ELF headers. Permissions are section flags,
not the single RWX program header's permissions. -/
structure Section where
  name : String
  address : Int
  endAddress : Int
  flags : Nat
  hasFileContents : Bool
  deriving Repr, DecidableEq

structure Symbol where
  sourceName : String
  elfName : String
  address : Int
  deriving Repr, DecidableEq

end Xv6.Kernel
