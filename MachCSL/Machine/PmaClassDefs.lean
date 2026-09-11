import MachCSL.Machine.Platform
import LeanPaperStock.Pma

/-! Exact source address-class PMA obligation, RiscvFetchExec.v:88–160.
Widths use the generated Lean model's Nat domain; the source's positive
width premise makes its Int domain equivalent on every admitted access. -/
namespace MachCSL.Machine.PmaClass
open LeanPaperStock.Functions

inductive Class where
  | ram | io

def access (class_ : Class) (address : BitVec 64) (width : Nat) : Prop :=
  1 ≤ width ∧ width ≤ 4096 ∧
    match class_ with
    | .ram => ramLow ≤ address.toNat ∧ address.toNat + width ≤ ramHigh
    | .io => 0x2000000 ≤ address.toNat ∧ address.toNat + width ≤ 0x12000000

/-- All source attributes, including every AMO through width sixteen,
misaligned plain accesses and reservation support. -/
def grants (class_ : Class) (region : PMA_Region) : Prop :=
  let attributes := override_PMA region.attributes .PBMT_PMA
  match class_ with
  | .ram => attributes.executable = true ∧ attributes.readable = true ∧ attributes.writable = true ∧
      (∀ op width, width ≤ 16 → pma_allows_atomic_op attributes.atomic_support op width = true) ∧
      attributes.supports_pte_read = true ∧ attributes.supports_pte_write = true ∧
      attributes.misaligned_exceptions.load_store = none ∧ attributes.reservability ≠ .RsrvNone
  | .io => attributes.readable = true ∧ attributes.writable = true

def allowsClass (class_ : Class) (regions : List PMA_Region) : Prop :=
  ∀ address width, access class_ address width →
    ∃ region, matching_pma_region regions (.Physaddr address) width = some region ∧ grants class_ region

def allowsAll (regions : List PMA_Region) : Prop := ∀ class_, allowsClass class_ regions

def ramRegion : PMA_Region :=
  ⟨BitVec.ofNat 64 ramLow, BitVec.ofNat 64 (ramHigh - ramLow), pmaBootRam, true⟩
def ioRegion : PMA_Region := ⟨0x2000000#64, 0x10000000#64, pmaBootIo, false⟩

end MachCSL.Machine.PmaClass
