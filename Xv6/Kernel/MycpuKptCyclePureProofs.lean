import Xv6.Kernel.MycpuKptCyclePlanProofs

namespace Xv6.Kernel.MycpuKptCycle
open _root_.Sail.ConcurrencyInterfaceV1.Free
open Iris MachCSL.Memory MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem entry_config control cpu values (h : Config control) : Config (entry control cpu values) :=
  ⟨h.privilege,h.active,h.landing,h.misa,h.environment,h.delegated,h.pma,h.htif⟩

theorem prepared_entry i control cpu values :
    Prepared i (entry control cpu values) = entry (Prepared i control) cpu values := by
  funext r
  cases r <;> rfl

theorem prepared_config i control (h : Config control) : Config (Prepared i control) :=
  ⟨h.privilege,h.active,h.landing,h.misa,h.environment,h.delegated,h.pma,h.htif⟩

theorem fetch_config control (h : Config control) : MycpuKptFetch.Config control :=
  MycpuKptFetch.source_config control h.privilege h.pma h.htif h.misa h.environment

theorem body_config i control (h : Config control) : MycpuKptBody.Config i (Prepared i control) := by
  have p := prepared_config i control h
  unfold MycpuKptBody.Config
  cases MycpuKptBody.route i with
  | registers inst =>
    cases inst with
    | scalar j => trivial
    | returns =>
      refine ⟨p.privilege, ?_, ?_⟩
      · rw [p.environment]; rfl
      · rw [p.misa]; rfl
  | memory kind slot =>
    refine ⟨p.privilege,p.pma,p.htif,?_,?_⟩
    · rw [p.environment]; rfl
    · rw [p.environment]; rfl

theorem body_config_stable i control cpu values (h : Config control) : Config (bodyControl i control cpu values) := by
  unfold bodyControl MycpuKptBody.afterControl
  cases MycpuKptBody.route i with
  | registers inst =>
    cases inst <;> exact ⟨h.privilege,h.active,h.landing,h.misa,h.environment,h.delegated,h.pma,h.htif⟩
  | memory kind slot => exact prepared_config i control h

theorem started_config control (h : Config control) : Config (started control) :=
  ⟨h.privilege,h.active,h.landing,h.misa,h.environment,h.delegated,h.pma,h.htif⟩

theorem completed_config i control cpu values after (h : Config control)
    (done : MycpuRegimeShell.Completed (bodyControl i control cpu values) after) : Config after := by
  have p := body_config_stable i control cpu values h
  have unchanged := MycpuCycleShell.completed_other _ _ done
  constructor
  · rw [unchanged .cur_privilege (by decide) (by decide) (by decide)]; exact p.privilege
  · rw [unchanged .hart_state (by decide) (by decide) (by decide)]; exact p.active
  · rw [unchanged .elp (by decide) (by decide) (by decide)]; exact p.landing
  · rw [unchanged .misa (by decide) (by decide) (by decide)]; exact p.misa
  · rw [unchanged .menvcfg (by decide) (by decide) (by decide)]; exact p.environment
  · rw [unchanged .mie (by decide) (by decide) (by decide), unchanged .mideleg (by decide) (by decide) (by decide)]
    exact p.delegated
  · rw [unchanged .pma_regions (by decide) (by decide) (by decide)]; exact p.pma
  · rw [unchanged .htif_tohost_base (by decide) (by decide) (by decide)]; exact p.htif

theorem next_pc i control cpu values : bodyControl i control cpu values .nextPC = nextPC i control cpu values := by
  rcases i with ⟨i, bound⟩
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem completed_pc i control cpu values after
    (done : MycpuRegimeShell.Completed (bodyControl i control cpu values) after) :
    after .PC = nextPC i control cpu values ∧ after .nextPC = nextPC i control cpu values := by
  simpa only [next_pc] using MycpuCycleShell.completed_pc _ _ done

theorem execute_tail [Platform] i : MycpuActive.executeTail i =
    (MycpuKptBody.body i >>= fun execution => pure (.Step_Execute (execution,MycpuActive.instbits i))) := by
  unfold MycpuActive.executeTail MycpuKptBody.body
  rw [BootPmp.sail_bind_assoc]
  congr 1
  funext result
  cases result <;> rfl

theorem decode_owned shares rs i (h : Config rs) :
    RegisterPlan.Returns (footprint shares) rs (MycpuKptFetch.decodeFetch (MycpuKptFetch.result i))
      (MycpuDecode.decoded i) rs := by
  rw [MycpuKptFetch.decode_identity]
  exact decode_plan shares rs i (decode_config rs i h)

theorem dispatch_owned shares rs (h : Config rs) (off : (_get_Mstatus_SIE (rs .mstatus) == 1#1) = false) :
    RegisterPlan.Returns (footprint shares) rs
      (PreSail.readReg .cur_privilege >>= dispatchInterrupt) none rs :=
  dispatch_plan shares rs h.privilege ⟨by rw [h.misa]; rfl,h.delegated,off⟩

theorem prepare_owned [Platform] shares control cpu values i (h : Config control) :
    MycpuActive.Prefix (footprint shares) (entry control cpu values)
      (MycpuActive.afterFetch 0 (MycpuKptFetch.result i)) (MycpuActive.executeTail i)
      (entry (Prepared i control) cpu values) := by
  rw [← prepared_entry]
  exact prepare_prefix shares _ i 0 (entry_config control cpu values h)

theorem dispatch_prefix [Platform] shares control cpu values (h : Config control)
    (off : (_get_Mstatus_SIE (control .mstatus) == 1#1) = false) :
    MycpuActive.Prefix (footprint shares) (entry control cpu values) (run_hart_active 0)
      (fetch () >>= MycpuActive.afterFetch 0) (entry control cpu values) := by
  rw [MycpuActive.factor, ← BootPmp.sail_bind_assoc]
  exact .prefix (dispatch_owned shares _ (entry_config control cpu values h) off) .done

theorem pureSpec [Platform] : PureSpec :=
  ⟨MycpuActive.factor,decode_owned,dispatch_owned,prepare_owned,execute_tail,prepared_entry,
    fetch_config,body_config,started_config,body_config_stable,completed_config,next_pc,completed_pc⟩

end Xv6.Kernel.MycpuKptCycle
