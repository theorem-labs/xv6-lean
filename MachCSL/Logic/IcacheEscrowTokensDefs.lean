import MachCSL.Logic.TsoViewsDefs
import Iris.Algebra.Excl
import Iris.Instances.Lib.GhostMap
import Iris.Std.HeapInstances

/-! Exact token layer of EscrowDefs. The escrow body/invariant is separate. -/
namespace MachCSL.Logic.IcacheEscrowTokens
open Iris Iris.Std Iris.Algebra Iris.BI

/-- Source icorpse: the pre-deposit row retains its full transaction/share index. -/
inductive Corpse where
  | pre (transaction : Nat) (share : Qp)
  | deposited
  deriving DecidableEq

abbrev TokenMap (V : Type) := _root_.Std.ExtTreeMap Int V
abbrev RegistryValue := GName × GName
abbrev RegistryRA := HeapView Int (Agree (DiscreteO RegistryValue)) TokenMap
abbrev RegistryRF := constOF RegistryRA
abbrev TicketRA := Excl Unit
abbrev TicketRF := constOF TicketRA
abbrev CorpseRA := HeapView Int (Agree (DiscreteO Corpse)) TokenMap
abbrev CorpseRF := constOF CorpseRA

def registryFunctor : GFunctor := ⟨RegistryRF, inferInstance⟩
def ticketFunctor : GFunctor := ⟨TicketRF, inferInstance⟩
def corpseFunctor : GFunctor := ⟨CorpseRF, inferInstance⟩

structure Capacity (GF : BundledGFunctors) where
  registry : GhostMapG GF Int RegistryValue TokenMap
  ticket : ElemG GF TicketRF
  corpse : GhostMapG GF Int Corpse TokenMap
  mono : ElemG GF MonoNatRF

@[reducible] def Capacity.monoNat {GF : BundledGFunctors} (capacity : Capacity GF)
    (name : GName) : MonoNatG GF := ⟨capacity.mono, name⟩

def ticketElem : TicketRA := .excl ()

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def committedA (ge : GName) : IProp GF :=
  letI := capacity.monoNat ge
  MonoNat.lb_own ge (.ofNat 1)

def redeem_ticketA (gr : GName) : IProp GF := iOwn (E := capacity.ticket) gr ticketElem

def reg_auth (name : GName) (rows : TokenMap RegistryValue) : IProp GF :=
  letI := capacity.registry
  ghost_map_auth (H := TokenMap) name (.own 1) rows

def reg_elem (name : GName) (dq : DFrac) (z : Int) (pair : RegistryValue) : IProp GF :=
  letI := capacity.registry
  ghost_map_elem name dq z pair

def reg_half (name : GName) (z : Int) (ge gr : GName) : IProp GF :=
  reg_elem capacity name (.own (1 : Qp).half) z (ge, gr)
def reg_full (name : GName) (z : Int) (ge gr : GName) : IProp GF :=
  reg_elem capacity name (.own 1) z (ge, gr)

def crp_auth (name : GName) (rows : TokenMap Corpse) : IProp GF :=
  letI := capacity.corpse
  ghost_map_auth (H := TokenMap) name (.own 1) rows

def crp_elemQ (name : GName) (dq : DFrac) (z : Int) (value : Corpse) : IProp GF :=
  letI := capacity.corpse
  ghost_map_elem name dq z value

def crp_elem (name : GName) (z : Int) (value : Corpse) : IProp GF :=
  crp_elemQ capacity name (.own 1) z value

def region_pending (name : GName) (z : Int) : IProp GF :=
  iprop(∃ ge gr, reg_half capacity name z ge gr ∗ committedA capacity ge)

end MachCSL.Logic.IcacheEscrowTokens
