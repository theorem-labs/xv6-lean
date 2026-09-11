import MachCSL.Machine.BootPmpPlan

/-! Source supervisor TOR-entry configuration, separate from the reset OFF state. -/
namespace MachCSL.Machine.SupervisorPmp
open LeanPaperStock.Functions

def entry0 (rs : RegisterFile) : BitVec 8 := (rs .pmpcfg_n)[0]
def upper0 (rs : RegisterFile) : BitVec 64 := (rs .pmpaddr_n)[0]

/-- `SmodePte.pmp_config`: later entries and the entry's lock bit are arbitrary. -/
structure TorRam (rs : RegisterFile) : Prop where
  tor : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (entry0 rs)) = .TOR
  positive : 0 < (upper0 rs).toNat
  execute : _get_Pmpcfg_ent_X (entry0 rs) = 1#1
  write : _get_Pmpcfg_ent_W (entry0 rs) = 1#1
  read : _get_Pmpcfg_ent_R (entry0 rs) = 1#1
  covers : ramHigh ≤ (upper0 rs).toNat * 4

/-- The surrounding source hardware/supervisor facts. PMP itself does not read
these two registers; privilege is an explicit argument to the checked call. -/
structure SourceConfig (rs : RegisterFile) : Prop extends TorRam rs where
  security : rs .mseccfg = 0#64
  supervisor : rs .cur_privilege = .Supervisor

/-- The bounded access family used by fetch, PTE loads, and scalar stack accesses. -/
inductive Supported : MemoryAccessType mem_payload → Prop
  | fetch : Supported (.InstructionFetch ())
  | pte : Supported (.Load .PageTableEntry)
  | load : Supported (.Load .Data)
  | store : Supported (.Store .Data)

end MachCSL.Machine.SupervisorPmp
