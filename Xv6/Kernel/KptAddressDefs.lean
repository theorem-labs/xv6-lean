import Xv6.Kernel.Sv39AddressDefs
import Xv6.Kernel.KptHardwareDefs

/-! Source per-hart residue wrapper for actual supervisor `translateAddr`.
The four hidden owned values are opened, used, and reassembled; no second
SATP/PMP ownership or unrelated register-file equality is required. -/
namespace Xv6.Kernel.KptAddress
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := KptShared.Capacity
abbrev Result := Sv39Address.Result
abbrev program := Sv39Address.program

/-- Only the five cells outside the source residue are supplied separately. -/
structure Shares where
  status : DFrac
  privilege : DFrac
  pma : DFrac
  htif : DFrac
  environment : DFrac

def outerShares (shares : Shares) : Sv39Address.Shares :=
  ⟨shares.status, shares.privilege, .own 1⟩
def innerShares (shares : Shares) : KptTranslate.Shares :=
  ⟨⟨shares.pma, .own 1, .own 1, shares.htif⟩, shares.environment⟩
def auxiliaryFootprint (shares : Shares) : RegisterFootprint.Footprint :=
  [(.mstatus, shares.status), (.cur_privilege, shares.privilege),
    (.pma_regions, shares.pma), (.htif_tohost_base, shares.htif), (.menvcfg, shares.environment)]
def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  Sv39Address.footprint (outerShares shares) ++ KptTranslate.footprint (innerShares shares)

/-- The source residue's four actual owned values. -/
structure Data where
  satp : BitVec 64
  tlb : KptResidue.Tlb
  cfg : RegisterType .pmpcfg_n
  addr : RegisterType .pmpaddr_n

/-- Proof-side assembly of a partial register description, not a machine
transition. Actual instructions read the corresponding nine owned cells. -/
def prepare (rs : RegisterFile) (data : Data) : RegisterFile :=
  MachCSL.Sail.Registers.write
    (MachCSL.Sail.Registers.write
      (MachCSL.Sail.Registers.write
        (MachCSL.Sail.Registers.write rs .satp data.satp) .tlb data.tlb)
      .pmpcfg_n data.cfg) .pmpaddr_n data.addr

/-- Source ambient facts on the five separately owned cells. TOR is obtained
from the source residue, not asserted about the caller's unused PMP fields. -/
structure Ambient (rs : RegisterFile) : Prop where
  privilege : rs .cur_privilege = .Supervisor
  sxl : _get_Mstatus_SXL (rs .mstatus) = 2#2
  pma : rs .pma_regions = pmaBoot
  htif : rs .htif_tohost_base = none

/-- These path facts are derived internally from the native map/snapshot
resources and returned to the continuation, never supplied to the WP. -/
structure Path (rs : RegisterFile) (data : Data) (root : PtTree.PPN) (address : BitVec 64)
    (ppn : PtTree.PPN) (permission : KptLeaf.Permission) (tree : PtTree.Tree)
    (p2 p1 : PtTree.Word) (referenceA referenceD : Bool) : Prop where
  rooted : KptResidue.SatpRooted root data.satp
  tor : MachCSL.Machine.SupervisorPmp.TorRam (prepare rs data)
  base : PtTree.base tree = root
  mapped : PtTree.Maps tree (Sv39Address.vpn address) p2 p1
    (KptLeaf.word ppn permission referenceA referenceD)
  coherent : TlbCoherence.Coherent 0#16 tree data.tlb

inductive Outcome where
  | noncanonical
  | translated (tree : PtTree.Tree) (p2 p1 : PtTree.Word)
      (referenceA referenceD : Bool) (branch : KptTranslate.Branch)

def afterData (rs : RegisterFile) (data : Data) (address : BitVec 64)
    (ppn : PtTree.PPN) (permission : KptLeaf.Permission) : Outcome → Data
  | .noncanonical => data
  | .translated _ p2 p1 _ _ branch =>
      { data with tlb := (KptTranslate.after (prepare rs data) 0#16 (Sv39Address.vpn address)
          p2 p1 ppn permission branch) .tlb }

def result (address : BitVec 64) (ppn : PtTree.PPN)
    (access : MemoryAccessType mem_payload) : Outcome → Result
  | .noncanonical => .Err (Sv39Address.pageFault access, ())
  | .translated _ _ _ _ _ branch =>
      Sv39Address.resumed address access (KptTranslate.result ppn branch)

def afterReservation (address : BitVec 64) (rr : Option Reservation) : Outcome → Option Reservation
  | .noncanonical => rr
  | .translated _ _ p1 _ _ branch =>
      KptAD.afterReservation (PtTree.addr0 p1 (Sv39Address.vpn address)) rr branch.update

def OutcomeFacts (rs : RegisterFile) (data : Data) (root : PtTree.PPN)
    (address : BitVec 64) (ppn : PtTree.PPN) (permission : KptLeaf.Permission)
    (access : MemoryAccessType mem_payload) : Outcome → Prop
  | .noncanonical => ¬ Sv39Address.Canonical address
  | .translated tree p2 p1 a d branch => Sv39Address.Canonical address ∧
      Path rs data root address ppn permission tree p2 p1 a d ∧
      KptTranslate.BranchFacts (prepare rs data) 0#16 (Sv39Address.vpn address) p2 p1
        ppn permission a d access branch

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def auxiliaryCells (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (auxiliaryFootprint shares)
def cells (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (footprint shares)
def dataCells (era : Era.Record) (cpu : CPU) (data : Data) : IProp GF :=
  iprop(KptResidue.satpCell capacity era cpu data.satp ∗
    KptResidue.tlbCell capacity era cpu data.tlb ∗
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .pmpcfg_n (.own 1) data.cfg ∗
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .pmpaddr_n (.own 1) data.addr)

def receipts (era : Era.Record) (cpu : CPU) (address : BitVec 64) : Outcome → IProp GF
  | .noncanonical => iprop(emp)
  | .translated _ _ p1 _ _ branch =>
      KptTranslate.receipts capacity era cpu (PtTree.addr0 p1 (Sv39Address.vpn address)) branch

variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- An exposed source residue at four named values. Its close rule returns
the original existential predicate. Only the TLB field changes after a call. -/
noncomputable def opened (era : Era.Record) (cpu : CPU) (rs : RegisterFile)
    (N : Namespace) (root : PtTree.PPN) (data : Data) : IProp GF :=
  iprop(dataCells capacity era cpu data ∗ ⌜KptResidue.SatpRooted root data.satp⌝ ∗
    KptResidue.tlbSnapOK capacity era data.tlb ∗
    ⌜MachCSL.Machine.SupervisorPmp.TorRam (prepare rs data)⌝ ∗
    KptShared.shared capacity era N root ∗ KptShared.credentials capacity era cpu)

noncomputable def resources (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (data : Data) (address : BitVec 64)
    (ppn : PtTree.PPN) (permission : KptLeaf.Permission) (rr : Option Reservation)
    (outcome : Outcome) : IProp GF :=
  iprop(auxiliaryCells capacity era cpu rs shares ∗
    opened capacity era cpu rs N root (afterData rs data address ppn permission outcome) ∗
    KptShared.mapAt capacity era (Sv39Address.vpn address) ppn permission ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (afterReservation address rr outcome) ∗ receipts capacity era cpu address outcome)

noncomputable def continueWith [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (data : Data) (address : BitVec 64)
    (ppn : PtTree.PPN) (permission : KptLeaf.Permission) (access : MemoryAccessType mem_payload)
    (rr : Option Reservation) (continuation : Result → SailM Unit) (post : Empty → IProp GF)
    (outcome : Outcome) : IProp GF :=
  iprop(⌜OutcomeFacts rs data root address ppn permission access outcome⌝ -∗
    resources capacity era cpu rs shares N root data address ppn permission rr outcome -∗
    MemoryReadWP.threadWP capacity.machine image fixed whole
      (.hart gen cpu (continuation (result address ppn access outcome))) post)

/-- The initial hidden values/path are universally offered to the caller's
continuation. No caller premise supplies those witnesses or a successful body
WP. Each memory-result fact stays inside the corresponding event guards. -/
noncomputable def finish [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (address : BitVec 64)
    (ppn : PtTree.PPN) (permission : KptLeaf.Permission) (access : MemoryAccessType mem_payload)
    (rr : Option Reservation) (continuation : Result → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  let next := fun data => continueWith capacity image fixed whole gen era cpu rs shares N root data
    address ppn permission access rr continuation post
  iprop((∀ data, next data .noncanonical) ∧
    (∀ data tree p2 p1 referenceA referenceD,
      ⌜Sv39Address.Canonical address ∧ Path rs data root address ppn permission tree p2 p1 referenceA referenceD⌝ -∗
      ((∀ a d update, KptAD.guarded update
          (next data (.translated tree p2 p1 referenceA referenceD (.hit a d update)))) ∧
        ▷ ▷ ▷ (∀ a d view2 view1 view0 update, KptAD.guarded update
          (next data (.translated tree p2 p1 referenceA referenceD (.miss a d view2 view1 view0 update)))))))

end Xv6.Kernel.KptAddress
