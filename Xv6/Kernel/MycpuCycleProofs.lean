import Xv6.Kernel.MycpuCycleSpec
import Xv6.Kernel.MycpuCycleEntryLink
import Xv6.Kernel.MycpuCycleShellLink

namespace Xv6.Kernel.MycpuCycle
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open TsoContextReadWP MycpuMemory

theorem started_address (slot : Slot) (rs : RegisterFile) : address slot (started rs) = address slot rs := by
  simp [address, started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write]

theorem started_data (slot : Slot) (rs : RegisterFile) : dataValue slot (started rs) = dataValue slot rs := by
  cases slot <;> simp [dataValue, started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write]

private theorem started_bare (rs : RegisterFile) (config : SupervisorBare.Config rs) :
    SupervisorBare.Config (started rs) := by
  rcases config with ⟨privilege, sxl, mode⟩
  constructor <;> simp_all [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write]

private theorem started_tor (rs : RegisterFile) (config : SupervisorPmp.TorRam rs) :
    SupervisorPmp.TorRam (started rs) := by
  rcases config with ⟨mode, positive, execute, write, read, covers⟩
  constructor <;> simp_all [SupervisorPmp.entry0, SupervisorPmp.upper0,
    started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write]

private theorem started_transform (rs : RegisterFile) (config : SupervisorAddress.Config rs .Bare) :
    SupervisorAddress.Config (started rs) .Bare := by
  rcases config with ⟨privilege, mprv, mxr, pmm, sxl, decoded⟩
  constructor <;> simp_all [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write]

theorem started_config (rs : RegisterFile) (i : Fin 14) region (config : Config rs i region) :
    MycpuActive.Config (started rs) i region := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, started_bare rs config.fetch.bare, started_tor rs config.fetch.pmp, ?_, ?_, config.fetch.executable⟩
    · simpa [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write] using config.fetch.pc
    · simpa [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write] using config.fetch.compressed
    · simpa [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write] using config.fetch.htif
    · simpa [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write] using config.fetch.matched
  · obtain ⟨extension, delegated, sie⟩ := config.interrupts
    constructor <;> simp_all [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write]
  · simpa [MycpuDecode.Config, started, MycpuCycleShell.started, SupervisorRetirement.setupAfter,
      MachCSL.Sail.Registers.write] using config.decode
  · simpa [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write] using config.landing

theorem started_write_config (slot : Slot) (rs : RegisterFile) region (config : WriteConfig slot rs region) :
    WriteConfig slot (started rs) region := by
  refine ⟨started_transform rs config.transform, ?_⟩
  refine ⟨started_bare rs config.memory.bare, ?_, started_tor rs config.memory.tor, ?_, ?_, ?_, config.memory.writable⟩
  · simpa [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write] using config.memory.mprv
  · simpa only [started_address] using config.memory.range
  · simpa [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write] using config.memory.disabled
  · rw [started_address]
    simpa [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write] using config.memory.matched

theorem started_read_config (slot : Slot) (rs : RegisterFile) region (config : ReadConfig slot rs region) :
    ReadConfig slot (started rs) region := by
  refine ⟨started_transform rs config.transform, ?_⟩
  refine ⟨started_bare rs config.memory.bare, ?_, started_tor rs config.memory.tor, ?_, ?_, ?_, config.memory.readable⟩
  · simpa [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write] using config.memory.mprv
  · simpa only [started_address] using config.memory.range
  · simpa [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write] using config.memory.disabled
  · rw [started_address]
    simpa [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write] using config.memory.matched

theorem started_return_config (rs : RegisterFile) (config : MycpuReturn.Config rs) :
    MycpuReturn.Config (started rs) := by
  rcases config with ⟨privilege, lpe, compressed⟩
  constructor <;> simp_all [started, MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write]

theorem scalar_active (i : Fin 9) (rs : RegisterFile) :
    scalarBeforeFinish i rs .hart_state = rs .hart_state := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [scalarBeforeFinish, MycpuCycleEntry.scalarAfter, MycpuScalar.after,
    MycpuCycleEntry.prepared, MycpuActive.prepared, started,
    MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write]

theorem store_active (slot : Slot) (rs : RegisterFile) :
    storeBeforeFinish slot rs .hart_state = rs .hart_state := by
  simp [storeBeforeFinish, MycpuActive.prepared, started,
    MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write]

theorem load_active (slot : Slot) (rs : RegisterFile) (word : BitVec 64) :
    loadBeforeFinish slot rs word .hart_state = rs .hart_state := by
  cases slot <;> simp [loadBeforeFinish, MycpuCycleEntry.loadAfter, MycpuMemory.after,
    MycpuCycleEntry.prepared, MycpuActive.prepared, started,
    MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write]

theorem return_active (rs : RegisterFile) : returnBeforeFinish rs .hart_state = rs .hart_state := by
  simp [returnBeforeFinish, MycpuCycleEntry.returnAfter, MycpuReturn.after,
    MycpuCycleEntry.prepared, MycpuActive.prepared, started,
    MycpuCycleShell.started, SupervisorRetirement.setupAfter, MachCSL.Sail.Registers.write]

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem wp_scalar (shares : Shares) (rs : RegisterFile) (i : Fin 9) region
    (config : Config rs (MycpuScalar.index i) region)
    image fixed whole gen era cpu ξ rr tick post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ (∀ fetchView after, ⌜Completed (scalarBeforeFinish i rs) after⌝ -∗
        ∀ nextTick, cells capacity era cpu after shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle tick)) post) := by
  iintro #Hcert Hregs Hrun Hspan Hresv Hfinish
  iapply MycpuCycleShell.wp_start capacity shares rs config.active tick image fixed whole gen era cpu post
    $$ Hcert Hregs
  iintro Hregs
  iapply MycpuCycleEntry.wp_scalar capacity shares (started rs) i region (started_config rs _ region config)
    image fixed whole gen era cpu ξ rr 0 (MycpuCycleShell.finish tick) post $$ Hcert Hregs Hrun Hspan Hresv
  iintro !> %fetchView Hregs Hrun Hspan Hresv Hfetch
  simp only [MycpuCycleEntry.result]
  iapply MycpuCycleShell.wp_finish_restart capacity shares (MycpuCycleEntry.scalarAfter i (started rs))
    ((scalar_active i rs).trans config.active) tick (MycpuActive.instbits (MycpuScalar.index i))
    image fixed whole gen era cpu rr post $$ Hcert Hregs Hresv
  iintro %after %completed !> %nextTick Hregs Hresv
  isimp only [scalarBeforeFinish] at Hfinish
  iapply Hfinish $$ %fetchView %after [] %nextTick Hregs Hrun Hspan Hresv Hfetch
  ipureintro
  exact completed

theorem wp_store (slot : Slot) (shares : Shares) (rs : RegisterFile) fetchRegion dataRegion
    (config : Config rs (storeIndex slot) fetchRegion) (memory : WriteConfig slot rs dataRegion)
    image fixed whole gen era cpu ξ (old : BitVec 64) rr tick post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      wordPointsto capacity era ξ (address slot rs) (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ ▷ (∀ fetchView dataView after, ⌜Completed (storeBeforeFinish slot rs) after⌝ -∗
        ∀ nextTick, cells capacity era cpu after shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
        wordPointsto capacity era ξ (address slot rs) (.own 1) (dataValue slot rs) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) dataView -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle tick)) post) := by
  iintro #Hcert Hregs Hrun Hspan Hword Hresv Hfinish
  iapply MycpuCycleShell.wp_start capacity shares rs config.active tick image fixed whole gen era cpu post
    $$ Hcert Hregs
  iintro Hregs
  have entry := MycpuCycleEntry.wp_store capacity slot shares (started rs) fetchRegion dataRegion
    (started_config rs _ fetchRegion config) (started_write_config slot rs dataRegion memory)
    image fixed whole gen era cpu ξ old rr 0 (MycpuCycleShell.finish tick) post
  rw [started_address, started_data] at entry
  iapply entry $$ Hcert Hregs Hrun Hspan Hword Hresv
  iintro !> !> %fetchView %dataView Hregs Hrun Hspan Hword Hresv Hfetch Hdata
  simp only [MycpuCycleEntry.result]
  iapply MycpuCycleShell.wp_finish_restart capacity shares
    (MycpuCycleEntry.prepared (storeIndex slot) (started rs))
    ((store_active slot rs).trans config.active) tick (MycpuActive.instbits (storeIndex slot))
    image fixed whole gen era cpu none post $$ Hcert Hregs Hresv
  iintro %after %completed !> %nextTick Hregs Hresv
  isimp only [storeBeforeFinish] at Hfinish
  iapply Hfinish $$ %fetchView %dataView %after [] %nextTick Hregs Hrun Hspan Hword Hresv Hfetch Hdata
  ipureintro
  exact completed

theorem wp_load (slot : Slot) (shares : Shares) (rs : RegisterFile) fetchRegion dataRegion
    (config : Config rs (loadIndex slot) fetchRegion) (memory : ReadConfig slot rs dataRegion)
    image fixed whole gen era cpu ξ dq (word : BitVec 64) rr tick post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      wordPointsto capacity era ξ (address slot rs) dq word -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ ▷ (∀ fetchView dataView after, ⌜Completed (loadBeforeFinish slot rs word) after⌝ -∗
        ∀ nextTick, cells capacity era cpu after shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
        wordPointsto capacity era ξ (address slot rs) dq word -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) dataView -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle tick)) post) := by
  iintro #Hcert Hregs Hrun Hspan Hword Hresv Hfinish
  iapply MycpuCycleShell.wp_start capacity shares rs config.active tick image fixed whole gen era cpu post
    $$ Hcert Hregs
  iintro Hregs
  have entry := MycpuCycleEntry.wp_load capacity slot shares (started rs) fetchRegion dataRegion
    (started_config rs _ fetchRegion config) (started_read_config slot rs dataRegion memory)
    image fixed whole gen era cpu ξ dq word rr 0 (MycpuCycleShell.finish tick) post
  rw [started_address] at entry
  iapply entry $$ Hcert Hregs Hrun Hspan Hword Hresv
  iintro !> !> %fetchView %dataView Hregs Hrun Hspan Hword Hresv Hfetch Hdata
  simp only [MycpuCycleEntry.result]
  iapply MycpuCycleShell.wp_finish_restart capacity shares (MycpuCycleEntry.loadAfter slot (started rs) word)
    ((load_active slot rs word).trans config.active) tick (MycpuActive.instbits (loadIndex slot))
    image fixed whole gen era cpu rr post $$ Hcert Hregs Hresv
  iintro %after %completed !> %nextTick Hregs Hresv
  isimp only [loadBeforeFinish] at Hfinish
  iapply Hfinish $$ %fetchView %dataView %after [] %nextTick Hregs Hrun Hspan Hword Hresv Hfetch Hdata
  ipureintro
  exact completed

theorem wp_return (shares : Shares) (rs : RegisterFile) region
    (config : Config rs ⟨13, Nat.lt_succ_self 13⟩ region) (ret : MycpuReturn.Config rs)
    image fixed whole gen era cpu ξ rr tick post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ (∀ fetchView after, ⌜Completed (returnBeforeFinish rs) after⌝ -∗
        ∀ nextTick, cells capacity era cpu after shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle tick)) post) := by
  iintro #Hcert Hregs Hrun Hspan Hresv Hfinish
  iapply MycpuCycleShell.wp_start capacity shares rs config.active tick image fixed whole gen era cpu post
    $$ Hcert Hregs
  iintro Hregs
  iapply MycpuCycleEntry.wp_return capacity shares (started rs) region (started_config rs _ region config)
    (started_return_config rs ret) image fixed whole gen era cpu ξ rr 0 (MycpuCycleShell.finish tick) post
    $$ Hcert Hregs Hrun Hspan Hresv
  iintro !> %fetchView Hregs Hrun Hspan Hresv Hfetch
  simp only [MycpuCycleEntry.result]
  iapply MycpuCycleShell.wp_finish_restart capacity shares (MycpuCycleEntry.returnAfter (started rs))
    ((return_active rs).trans config.active) tick (MycpuActive.instbits ⟨13, Nat.lt_succ_self 13⟩)
    image fixed whole gen era cpu rr post $$ Hcert Hregs Hresv
  iintro %after %completed !> %nextTick Hregs Hresv
  isimp only [returnBeforeFinish] at Hfinish
  iapply Hfinish $$ %fetchView %after [] %nextTick Hregs Hrun Hspan Hresv Hfetch
  ipureintro
  exact completed

theorem actual : Spec capacity := ⟨wp_scalar capacity, wp_store capacity, wp_load capacity, wp_return capacity⟩

end Xv6.Kernel.MycpuCycle
