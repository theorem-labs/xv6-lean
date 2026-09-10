import Std

/-!
Core of `iris/TsoMemPa.v` at xv6iris `arxiv-v1`
(`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). This is the production
TSO model's byte-map message representation, parameterized by address width.
The Sail carrier is 64 bits; physical-address validity is a separate 56-bit
constraint. The finite-domain partial functions below represent finite byte
maps extensionally. The Sail map/byte-operation correspondence is not yet proved.
-/
namespace MachCSL.Memory

abbrev Byte := BitVec 8
abbrev Agent := Nat
abbrev Address (width : Nat) := BitVec width
abbrev PhysicalAddress := Address 64
abbrev ByteMap (width : Nat) := Address width → Option Byte

/-- Left-biased union, as used by stdpp's finite maps. -/
def overlay (new old : ByteMap width) : ByteMap width :=
  fun a => (new a).or (old a)

def empty : ByteMap width := fun _ => none

def singleton (a : Address width) (v : Byte) : ByteMap width :=
  fun b => if b = a then some v else none

/-- Source `pwmsg`; one append may write several bytes. -/
structure Message (width : Nat) where
  bytes : ByteMap width
  author : Agent

abbrev WriteLog (width : Nat) := List (Message width)

/-- Source `msg_byte`. -/
def msgByte (m : Message width) (a : Address width) : Option Byte := m.bytes a

/-- Timestamp zero names the era's initial image. -/
def logByte (img : ByteMap width) (log : WriteLog width)
    (t : Nat) (a : Address width) : Option Byte :=
  match t with
  | 0 => img a
  | i + 1 => (log[i]?).bind (fun m => msgByte m a)

/-- Source `visibleb`: own writes are visible even above the reader's view. -/
def visible (h : Agent) (view : Nat) (log : WriteLog width) (t : Nat) : Bool :=
  decide (t ≤ view) || match t with
  | 0 => true
  | i + 1 => match log[i]? with
    | some m => decide (m.author = h)
    | none => false

/-- Source `read_down`, scanning in descending timestamp order. -/
def readDown (img : ByteMap width) (log : WriteLog width)
    (h : Agent) (view : Nat) (a : Address width) : Nat → Option Byte
  | 0 => if visible h view log 0 then logByte img log 0 a else none
  | t + 1 =>
    match if visible h view log (t + 1) then logByte img log (t + 1) a else none with
    | some v => some v
    | none => readDown img log h view a t

/-- Source `tso_read`. -/
def read (img : ByteMap width) (log : WriteLog width)
    (h : Agent) (view : Nat) (a : Address width) : Option Byte :=
  readDown img log h view a log.length

def addressAdd (a : Address width) (j : Nat) : Address width :=
  a + BitVec.ofNat width j

def nthByte (v : BitVec bits) (j : Nat) : Byte :=
  BitVec.ofNat 8 (v.toNat / 2 ^ (8 * j))

/-- Source `tso_read_bytes`: a multi-byte access uses one common view. -/
def ReadsBytes (img : ByteMap width) (log : WriteLog width)
    (h : Agent) (view : Nat) (a : Address width) (n : Nat) (v : BitVec bits) : Prop :=
  ∀ j, j < n → read img log h view (addressAdd a j) = some (nthByte v j)

/-- Source `own_pub`, the timestamp of the author's last published message. -/
def ownPub (h : Agent) (log : WriteLog width) : Nat :=
  ((log.zipIdx).map (fun (m, i) => if m.author = h then i + 1 else 0)).foldr Nat.max 0

/-- Source `fence_post`; the language layer decides whether a fence drains. -/
def fencePost (h : Agent) (log : WriteLog width) (drain : Bool) (view : Nat) : Nat :=
  if drain then max view (ownPub h log) else view

/-- Source `flat`: memory obtained by publishing every message in log order. -/
def flat (img : ByteMap width) (log : WriteLog width) : ByteMap width :=
  log.foldl (fun acc m => overlay m.bytes acc) img

/-- Source `all_own`. -/
def AllOwn (h : Agent) (log : WriteLog width) : Prop :=
  ∀ m ∈ log, m.author = h

/-- Source `latest`: an address's latest write, regardless of its visibility. -/
def Latest (img : ByteMap width) (log : WriteLog width)
    (a : Address width) (t : Nat) (v : Byte) : Prop :=
  logByte img log t a = some v ∧ ∀ t', t < t' → logByte img log t' a = none

end MachCSL.Memory
