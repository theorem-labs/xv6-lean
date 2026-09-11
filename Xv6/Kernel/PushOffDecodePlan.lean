import Xv6.Kernel.PushOffDecodeSpec
import Xv6.Kernel.KptJalDecodeProofs

namespace Xv6.Kernel.PushOffDecode
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

private theorem returns_bind {fp rs middle after} {program : SailM α} {next : α → SailM β} {value result}
    (first : RegisterPlan.Returns fp rs program value middle)
    (rest : RegisterPlan.Returns fp middle (next value) result after) :
    RegisterPlan.Returns fp rs (program >>= next) result after :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (pure value) value rs := .pure ⟨rfl, rfl⟩

private theorem read_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (r : Register) (dq : DFrac) (member : (r, dq) ∈ fp) :
    RegisterPlan.Returns fp rs (PreSail.readReg r) (rs r) rs := .read member (.pure ⟨rfl, rfl⟩)

/-- Reuse the proved generic JAL bitfield factor. Only the real two-cell
supervisor extension prefix is specialized here. -/
theorem jal_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (privShare envShare : DFrac)
    (privMember : (.cur_privilege, privShare) ∈ fp)
    (envMember : (.menvcfg, envShare) ∈ fp)
    (priv : rs .cur_privilege = .Supervisor)
    (env : rs .menvcfg = 0xa000000000000000#64)
    (imm : BitVec 21) (even : KptJal.Encodable imm) :
    RegisterPlan.Returns fp rs (ext_decode (KptJal.encoding imm)) (KptJal.instruction imm) rs := by
  rw [KptJal.decode_factor imm even]
  rw [show currentlyEnabled .Ext_Zihintpause = (pure true : SailM Bool) by
    unfold currentlyEnabled hartSupports; rfl]
  simp only [BootPmp.sail_pure_bind]
  have enabled : RegisterPlan.Returns fp rs (currentlyEnabled .Ext_Zicfilp) false rs := by
    unfold currentlyEnabled
    rw [show currentlyEnabled .Ext_Zicsr = (pure true : SailM Bool) by
      unfold currentlyEnabled
      rw [show hartSupports .Ext_Zicsr = true by unfold hartSupports; rfl]]
    simp only [BootPmp.sail_pure_bind]
    refine returns_bind (read_plan rs .cur_privilege privShare privMember) ?_
    rw [priv]
    have inner : RegisterPlan.Returns fp rs (get_xLPE .Supervisor) false rs := by
      unfold get_xLPE
      refine returns_bind (read_plan rs .menvcfg envShare envMember) ?_
      rw [env]
      exact .pure ⟨rfl, rfl⟩
    refine returns_bind inner ?_
    rw [show hartSupports .Ext_Zicfilp = true by unfold hartSupports; rfl]
    exact .pure ⟨rfl, rfl⟩
  exact returns_bind enabled (.pure ⟨rfl, rfl⟩)

end Xv6.Kernel.PushOffDecode
