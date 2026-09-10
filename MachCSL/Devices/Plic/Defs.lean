import Std

/-!
PLIC component of `iris/DevModel.v:752–945,1136–1138`, xv6iris `arxiv-v1`
(`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). The source's `N` and `nat`
indices are represented by unrestricted `Nat` functions, not finite arrays.
Offsets remain signed integers. Source unsigned 32-bit words become `BitVec 32`.
The source mapping and correspondence boundary are recorded in `STATUS.md`.
-/
namespace MachCSL.Devices.Plic

abbrev Word := BitVec 32

structure State where
  prio : Nat → Word
  pending : Nat → Bool
  claimed : Nat → Bool
  enable : Nat → Nat → Word
  thresh : Nat → Word

/-- Board geometry, including both M and S contexts of every hart. -/
def base : Int := 0xc000000
def size : Int := 0x400000
def nCpu : Nat := 8
def uartIrqId : Nat := 10
def virtioIrqId : Nat := 1
def nSrc : Nat := 96
def nWords : Nat := 3
def nCtx : Nat := 2 * nCpu
def mCtx (hart : Nat) : Nat := 2 * hart
def sCtx (hart : Nat) : Nat := 2 * hart + 1

def srcWord (source : Nat) : Nat := source / 32
def srcBit (source : Nat) : Nat := source % 32

def nupd (f : Nat → α) (i : Nat) (value : α) : Nat → α :=
  fun j => if j = i then value else f j

def hupd (f : Nat → α) (context : Nat) (value : α) : Nat → α :=
  fun other => if other = context then value else f other

def wupd (f : Nat → Nat → Word) (context word : Nat) (value : Word) : Nat → Nat → Word :=
  fun otherContext otherWord =>
    if otherContext = context ∧ otherWord = word then value else f otherContext otherWord

def enabled (p : State) (context source : Nat) : Bool :=
  (p.enable context (srcWord source)).getLsbD (srcBit source)

/-- The strict threshold comparison governs both notification and claim. -/
def cand (p : State) (context source : Nat) : Bool :=
  p.pending source && enabled p context source &&
    decide ((p.thresh context).toNat < (p.prio source).toNat)

/-- Higher priority wins; a tie goes to the lower source ID. -/
def better (p : State) (i j : Nat) : Bool :=
  decide ((p.prio j).toNat < (p.prio i).toNat) ||
    (decide ((p.prio i).toNat = (p.prio j).toNat) && decide (i < j))

/-- Source zero is excluded; the scan visits IDs 1 through 95 in order. -/
def srcs : List Nat := List.range' 1 (nSrc - 1)

/-- The source fold body, named to support compositional selection proofs. -/
def select (p : State) (context : Nat) (winner : Option Nat) (source : Nat) : Option Nat :=
  if cand p context source then
    match winner with
    | none => some source
    | some old => if better p source old then some source else some old
  else winner

def best (p : State) (context : Nat) : Option Nat :=
  srcs.foldl (select p context) none

/-- Claim returns zero unchanged if no source is visible. -/
def claim (p : State) (context : Nat) : Word × State :=
  match best p context with
  | none => (0, p)
  | some source =>
      (BitVec.ofNat 32 source,
       { p with pending := nupd p.pending source false,
                claimed := nupd p.claimed source true })

/-- Invalid completion IDs, including zero, leave the state unchanged. -/
def complete (p : State) (source : Nat) : State :=
  if 1 ≤ source ∧ source < nSrc then
    { p with claimed := nupd p.claimed source false }
  else p

def eip (p : State) (context : Nat) : Bool := srcs.any (cand p context)

/-- All 32 raw pending bits are retained, including bit zero of word zero.
The source imposes no well-formedness condition on an arbitrary input state. -/
def pendingWord (p : State) (word : Nat) : Word :=
  BitVec.ofNat 32 ((List.range 32).foldr
    (fun bit acc => if p.pending (32 * word + bit) then (1 <<< bit) ||| acc else acc) 0)

def prioSrc (off : Int) : Option Nat :=
  if 0 ≤ off ∧ off < 4 * (nSrc : Int) ∧ off % 4 = 0 then
    some (off / 4).toNat
  else none

def pendingWidx (off : Int) : Option Nat :=
  if 0x1000 ≤ off ∧ off < 0x1000 + 4 * (nWords : Int) ∧ off % 4 = 0 then
    some ((off - 0x1000) / 4).toNat
  else none

def enableCtx (off : Int) : Option (Nat × Nat) :=
  if 0x2000 ≤ off ∧ off < 0x2000 + 0x80 * (nCtx : Int) ∧ off % 4 = 0 ∧
      ((off - 0x2000) % 0x80) / 4 < (nWords : Int) then
    some (((off - 0x2000) / 0x80).toNat, (((off - 0x2000) % 0x80) / 4).toNat)
  else none

def threshCtx (off : Int) : Option Nat :=
  if 0x200000 ≤ off ∧ (off - 0x200000) % 0x1000 = 0 ∧
      (off - 0x200000) / 0x1000 < (nCtx : Int) then
    some ((off - 0x200000) / 0x1000).toNat
  else none

def claimCtx (off : Int) : Option Nat :=
  if 0x200004 ≤ off ∧ (off - 0x200004) % 0x1000 = 0 ∧
      (off - 0x200004) / 0x1000 < (nCtx : Int) then
    some ((off - 0x200004) / 0x1000).toNat
  else none

/-- Partial MMIO read, preserving the source decoder precedence. -/
def read (p : State) (off : Int) : Option (Word × State) :=
  match prioSrc off with
  | some source => some ((if source = 0 then 0 else p.prio source), p)
  | none => match pendingWidx off with
    | some word => some (pendingWord p word, p)
    | none => match enableCtx off with
      | some (context, word) => some (p.enable context word, p)
      | none => match threshCtx off with
        | some context => some (p.thresh context, p)
        | none => match claimCtx off with
          | some context => some (claim p context)
          | none => none

/-- Partial MMIO write. Source zero and the pending bitmap swallow writes. -/
def write (p : State) (off : Int) (value : Word) : Option State :=
  match prioSrc off with
  | some source => some (if source = 0 then p else { p with prio := nupd p.prio source value })
  | none => match pendingWidx off with
    | some _ => some p
    | none => match enableCtx off with
      | some (context, word) => some { p with enable := wupd p.enable context word value }
      | none => match threshCtx off with
        | some context => some { p with thresh := hupd p.thresh context value }
        | none => match claimCtx off with
          | some _ => some (complete p value.toNat)
          | none => none

/-- The source gateway only tests pending/claimed. It has no source-bound guard;
board wiring supplies the source ID when constructing autonomous transitions. -/
def latch (p : State) (source : Nat) : Option State :=
  if !p.pending source && !p.claimed source then
    some { p with pending := nupd p.pending source true }
  else none

def initial : State :=
  ⟨fun _ => 0, fun _ => false, fun _ => false, fun _ _ => 0, fun _ => 0⟩

end MachCSL.Devices.Plic
