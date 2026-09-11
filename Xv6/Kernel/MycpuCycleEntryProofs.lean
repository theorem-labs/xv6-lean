import Xv6.Kernel.MycpuCycleEntrySpec
import Xv6.Kernel.MycpuCycleEntryPlan
import Xv6.Kernel.MycpuCycleBodyLink

namespace Xv6.Kernel.MycpuCycleEntry
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open TsoContextReadWP MycpuMemory
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

private theorem wp_fetch_shared (shares : Shares) (rs : RegisterFile) (i : Fin 14) region
    (config : MycpuFetch.Config rs i region)
    image fixed whole gen era cpu ξ (continuation : FetchResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (MycpuFetch.result i))) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (fetch () >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun #Hspan Hfinish
  ihave Hcontext := MycpuBootResources.discarded_context
    (MycpuBootResources.storeCapacity capacity.era) (MycpuBootResources.storeNames era) ξ $$ Hspan
  ihave ⟨Hword, _⟩ := MycpuBootResources.fetch_access
    (MycpuBootResources.storeCapacity capacity.era) (MycpuBootResources.storeNames era) ξ .discard i $$ Hcontext
  isimp only [MycpuBootResources.fetchWindow, MycpuBootResources.storeCapacity,
    MycpuBootResources.storeNames] at Hword
  obtain ⟨tail, cut, success, _error⟩ := fetch_cut shares rs i region config
  have gate := SupervisorFetchRead.Boundary.fold capacity (MycpuCycleBody.footprint shares)
    (MycpuCycleBody.footprint_unique shares) rs (MycpuFetchBytes.width i)
    (SupervisorFetchRead.request (MycpuDecode.address i) (MycpuFetchBytes.width i))
    (fetch ()) tail cut (SupervisorPhysical.device_ram _ _ (MycpuFetch.address_range i)) (by rfl)
    image fixed whole gen era cpu ξ .discard (MycpuFetchBytes.word i) continuation post
  rw [show (SupervisorFetchRead.request (MycpuDecode.address i) (MycpuFetchBytes.width i)).pa =
    MycpuDecode.address i from rfl] at gate
  iapply gate $$ Hcert Hregs Hrun Hword
  iintro !> %view Hregs Hrun _ Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view Hregs Hrun Hspan Hreceipt

/-- Internal CPS composition only; the public family rules below prove its body obligation. -/
private theorem wp_entry (shares : Shares) (rs : RegisterFile) (i : Fin 14) region stepNo
    (config : Config rs i region)
    image fixed whole gen era cpu ξ (continuation : Step → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      ▷ (∀ view, cells capacity era cpu (prepared i rs) shares -∗
        running capacity era cpu ξ -∗ shared capacity era -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (MycpuActive.executeTail i >>= continuation)) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (run_hart_active stepNo >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hspan Hfinish
  rw [factor, BootPmp.sail_bind_assoc]
  iapply RegisterPlan.fold capacity (MycpuCycleBody.footprint shares)
    (MycpuCycleBody.footprint_unique shares) image fixed whole gen era cpu rs _ _ _ post
    (dispatch_plan shares rs config.fetch.bare.privilege config.interrupts) $$ Hcert Hregs
  iintro %pending %after %same Hregs
  rcases same with ⟨hp, ha⟩
  subst pending
  subst after
  rw [BootPmp.sail_bind_assoc]
  iapply wp_fetch_shared capacity shares rs i region config.fetch image fixed whole gen era cpu ξ
    (fun fetched => MycpuActive.afterFetch stepNo fetched >>= continuation) post $$ Hcert Hregs Hrun Hspan
  iintro !> %view Hregs Hrun Hspan Hreceipt
  iapply MycpuActive.Prefix.fold capacity (MycpuCycleBody.footprint shares)
    (MycpuCycleBody.footprint_unique shares) rs (prepared i rs)
    (MycpuActive.afterFetch stepNo (MycpuFetch.result i)) (MycpuActive.executeTail i)
    (prepare_prefix shares rs i region stepNo config) image fixed whole gen era cpu continuation post
    $$ Hcert Hregs
  iintro Hregs
  iapply Hfinish $$ %view Hregs Hrun Hspan Hreceipt

theorem wp_scalar (shares : Shares) (rs : RegisterFile) (i : Fin 9) region
    (config : Config rs (MycpuScalar.index i) region)
    image fixed whole gen era cpu ξ rr stepNo (continuation : Step → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ fetchView, cells capacity era cpu (scalarAfter i rs) shares -∗
        running capacity era cpu ξ -∗ shared capacity era -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (result (MycpuScalar.index i)))) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (run_hart_active stepNo >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hspan Hresv Hfinish
  iapply wp_entry capacity shares rs (MycpuScalar.index i) region stepNo config
    image fixed whole gen era cpu ξ continuation post $$ Hcert Hregs Hrun Hspan
  iintro !> %fetchView Hregs Hrun Hspan Hfetch
  rw [MycpuCycleBody.scalar_tail_eq, BootPmp.sail_bind_assoc]
  simp only [BootPmp.sail_pure_bind]
  iapply MycpuCycleBody.wp_scalar capacity shares i image fixed whole gen era cpu
    (prepared (MycpuScalar.index i) rs) _ post $$ Hcert Hregs
  iintro Hregs
  isimp only [scalarAfter, returnAfter, result] at Hfinish
  iapply Hfinish $$ %fetchView Hregs Hrun Hspan Hresv Hfetch

theorem wp_store (slot : Slot) (shares : Shares) (rs : RegisterFile) fetchRegion dataRegion
    (config : Config rs (storeIndex slot) fetchRegion) (memory : WriteConfig slot rs dataRegion)
    image fixed whole gen era cpu ξ (old : BitVec 64) rr stepNo (continuation : Step → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      wordPointsto capacity era ξ (address slot rs) (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ (∀ fetchView dataView, cells capacity era cpu (prepared (storeIndex slot) rs) shares -∗
        running capacity era cpu ξ -∗ shared capacity era -∗
        wordPointsto capacity era ξ (address slot rs) (.own 1) (dataValue slot rs) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) dataView -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (result (storeIndex slot)))) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (run_hart_active stepNo >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hspan Hword Hresv Hfinish
  iapply wp_entry capacity shares rs (storeIndex slot) fetchRegion stepNo config
    image fixed whole gen era cpu ξ continuation post $$ Hcert Hregs Hrun Hspan
  iintro !> %fetchView Hregs Hrun Hspan Hfetch
  rw [MycpuCycleBody.store_tail_eq, BootPmp.sail_bind_assoc]
  simp only [BootPmp.sail_pure_bind]
  have gate := MycpuCycleBody.wp_store capacity slot shares (prepared (storeIndex slot) rs) dataRegion
    (prepared_write_config slot _ rs dataRegion memory) image fixed whole gen era cpu ξ old rr
    (fun execution => continuation (.Step_Execute (execution, MycpuActive.instbits (storeIndex slot)))) post
  rw [prepared_address, prepared_data] at gate
  iapply gate $$ Hcert Hregs Hrun Hword Hresv
  iintro !> %dataView Hregs Hrun Hword Hresv Hdata
  isimp only [loadAfter, result] at Hfinish
  iapply Hfinish $$ %fetchView %dataView Hregs Hrun Hspan Hword Hresv Hfetch Hdata

theorem wp_load (slot : Slot) (shares : Shares) (rs : RegisterFile) fetchRegion dataRegion
    (config : Config rs (loadIndex slot) fetchRegion) (memory : ReadConfig slot rs dataRegion)
    image fixed whole gen era cpu ξ dq (word : BitVec 64) rr stepNo (continuation : Step → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      wordPointsto capacity era ξ (address slot rs) dq word -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ (∀ fetchView dataView, cells capacity era cpu (loadAfter slot rs word) shares -∗
        running capacity era cpu ξ -∗ shared capacity era -∗
        wordPointsto capacity era ξ (address slot rs) dq word -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) dataView -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (result (loadIndex slot)))) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (run_hart_active stepNo >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hspan Hword Hresv Hfinish
  iapply wp_entry capacity shares rs (loadIndex slot) fetchRegion stepNo config
    image fixed whole gen era cpu ξ continuation post $$ Hcert Hregs Hrun Hspan
  iintro !> %fetchView Hregs Hrun Hspan Hfetch
  rw [MycpuCycleBody.load_tail_eq, BootPmp.sail_bind_assoc]
  simp only [BootPmp.sail_pure_bind]
  have gate := MycpuCycleBody.wp_load capacity slot shares (prepared (loadIndex slot) rs) dataRegion
    (prepared_read_config slot _ rs dataRegion memory) image fixed whole gen era cpu ξ dq word rr
    (fun execution => continuation (.Step_Execute (execution, MycpuActive.instbits (loadIndex slot)))) post
  rw [prepared_address] at gate
  iapply gate $$ Hcert Hregs Hrun Hword Hresv
  iintro !> %dataView Hregs Hrun Hword Hresv Hdata
  isimp only [loadAfter, result] at Hfinish
  iapply Hfinish $$ %fetchView %dataView Hregs Hrun Hspan Hword Hresv Hfetch Hdata

theorem wp_return (shares : Shares) (rs : RegisterFile) region
    (config : Config rs ⟨13, Nat.lt_succ_self 13⟩ region) (ret : MycpuReturn.Config rs)
    image fixed whole gen era cpu ξ rr stepNo (continuation : Step → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ fetchView, cells capacity era cpu (returnAfter rs) shares -∗
        running capacity era cpu ξ -∗ shared capacity era -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (result ⟨13, Nat.lt_succ_self 13⟩))) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (run_hart_active stepNo >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hspan Hresv Hfinish
  iapply wp_entry capacity shares rs ⟨13, Nat.lt_succ_self 13⟩ region stepNo config
    image fixed whole gen era cpu ξ continuation post $$ Hcert Hregs Hrun Hspan
  iintro !> %fetchView Hregs Hrun Hspan Hfetch
  rw [MycpuCycleBody.return_tail_eq, BootPmp.sail_bind_assoc]
  simp only [BootPmp.sail_pure_bind]
  iapply MycpuCycleBody.wp_return capacity shares (prepared ⟨13, Nat.lt_succ_self 13⟩ rs)
    (prepared_return_config _ rs ret) image fixed whole gen era cpu _ post $$ Hcert Hregs
  iintro Hregs
  isimp only [scalarAfter, returnAfter, result] at Hfinish
  iapply Hfinish $$ %fetchView Hregs Hrun Hspan Hresv Hfetch

theorem actual : Spec capacity := ⟨wp_scalar capacity, wp_store capacity, wp_load capacity, wp_return capacity⟩

end Xv6.Kernel.MycpuCycleEntry
