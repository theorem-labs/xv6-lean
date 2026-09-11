import Xv6.Fs.Dinode
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeSet

/-! Exact raw directory bytes, canonical names and first-match map reading from
DirentEnc.v, DirView.v and FsTree.v at xv6iris arxiv-v1. -/
namespace Xv6.Fs

abbrev FileData := Nat → List (BitVec 8)
abbrev FName := List (BitVec 8)
abbrev NameSet := Std.ExtTreeSet FName
abbrev NameMap := Std.ExtTreeMap FName Int

structure Dirent where
  inum : BitVec 16
  name : List (BitVec 8)
  deriving DecidableEq, Repr, Inhabited

def Dirent.WellFormed (d : Dirent) : Prop := d.name.length = 14
def direntBytes (d : Dirent) : List (BitVec 8) := halfBytes d.inum ++ d.name
def dirblockBytes (ds : List Dirent) : List (BitVec 8) := ds.flatMap direntBytes

def cutNul : List (BitVec 8) → FName
  | [] => []
  | b :: bs => if b == 0 then [] else b :: cutNul bs

def bname (n : Nat) (f : Nat → BitVec 8) : FName :=
  cutNul ((List.range n).map f)

def dotName : FName := [46]
def dotdotName : FName := [46, 46]

def fileByte (data : FileData) (offset : Nat) : BitVec 8 :=
  byteAt (data (offset / 1024)) (offset % 1024)

def dirInum (data : FileData) (k : Nat) : BitVec 16 :=
  BitVec.ofNat 16 (MachCSL.Memory.assembleBytes [fileByte data (16 * k), fileByte data (16 * k + 1)])
def dirName (data : FileData) (k j : Nat) : BitVec 8 := fileByte data (16 * k + 2 + j)
def dirBname (data : FileData) (k : Nat) : FName := bname 14 (dirName data k)
def dirFreeb (data : FileData) (k : Nat) : Bool := dirInum data k == 0
def DirLive (data : FileData) (k : Nat) : Prop := dirInum data k ≠ 0
def dirLiveb (data : FileData) (k : Nat) : Bool := !(dirFreeb data k)
def dirMatchb (data : FileData) (k : Nat) (name : FName) : Bool :=
  dirLiveb data k && (dirBname data k == name)
def DirMatch (data : FileData) (k : Nat) (name : FName) : Prop :=
  DirLive data k ∧ dirBname data k = name

/-- Ascending first-match scan, including its exact short-circuit order. -/
def dFirst (predicate : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n + 1 => match dFirst predicate n with
    | some k => some k
    | none => if predicate n then some n else none

def dirFirst (data : FileData) (n : Nat) (name : FName) : Option Nat :=
  dFirst (fun k => dirMatchb data k name) n

def dirWins (data : FileData) (k : Nat) : Bool :=
  dirLiveb data k && (dirFirst data k (dirBname data k)).isNone

def dirEntry (data : FileData) (k : Nat) : Option (FName × Int) :=
  if dirWins data k then some (dirBname data k, (dirInum data k).toNat) else none

/-- Source list_to_map: the earlier list entry wins at a repeated key. -/
def nameMap (entries : List (FName × Int)) : NameMap :=
  entries.foldr (fun entry acc => acc.insert entry.1 entry.2) ∅

/-- Source first-match filter and original ordered list-to-map conversion. -/
def dirView (data : FileData) (n : Nat) : NameMap :=
  nameMap ((List.range n).filterMap (dirEntry data))

def DirNamesUnique (data : FileData) (n : Nat) : Prop :=
  ∀ j k : Nat, j < n → k < n → DirLive data j → DirLive data k →
    dirBname data j = dirBname data k → j = k

def dirNrec (size : Int) : Nat := (size / 16).toNat
def DirInumsOK (data : FileData) (nrec nib : Nat) : Prop :=
  ∀ k : Nat, k < nrec → DirLive data k → ((dirInum data k).toNat : Int) < 16 * (nib : Int)

/-- Exact source implication guards retained, including zero-link directories. -/
def DirDotsIx (self : Int) (dn : Dinode) (data : FileData) : Prop :=
  dn.type.toNat = 1 → dn.nlink ≠ 0 →
    2 ≤ dirNrec dn.size.toNat ∧ DirLive data 0 ∧
    ((dirInum data 0).toNat : Int) = self ∧ dirBname data 0 = dotName ∧
    DirLive data 1 ∧ dirBname data 1 = dotdotName

end Xv6.Fs
