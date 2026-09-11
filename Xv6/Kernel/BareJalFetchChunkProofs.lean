import Xv6.Kernel.BareJalFetchResources

namespace Xv6.Kernel.BareJalFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem wp_chunk shares rs (config : Config rs) start address n
    (width : SupervisorFetchRead.Supported n) (aligned : is_aligned_vaddr (.Virtaddr address) n = true)
    image fixed whole gen era cpu ξ (word : BitVec (8*n)) continuation post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity.machine era cpu ξ -∗
      KernelTextDatum.window capacity era .identity address n .discard word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoContextBytesReadWP.running capacity.machine era cpu ξ -∗
        KernelTextDatum.window capacity era .identity address n .discard word -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        RegisterWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.FetchBytes_Success word))) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (SupervisorBareFetch.program start address n >>= continuation)) post) := by
  iintro #Hcert Hcells Hrun #Hwindow Hfinish
  ihave %isText := text capacity era address n word (by rcases width with rfl | rfl <;> decide) $$ Hwindow
  ihave Hcontext := context capacity era ξ address n word $$ Hwindow
  have range := KptFetchHalf.text_range address n width isText
  ihave ⟨Hhead,Hbare⟩ := (partition capacity era cpu rs shares).mp $$ Hcells
  iapply SupervisorBareFetch.wp_fetch_bytes capacity.machine shares.bare rs config.bare start address n width
    aligned config.tor range config.htif MycpuBare.ramRegion
    (by rw [config.pma]; exact MycpuBare.pma_ram address n (by rcases width with rfl | rfl <;> decide) range)
    (by rfl) image fixed whole gen era cpu ξ .discard word continuation post $$ Hcert Hbare Hrun Hcontext
  iintro !> %view Hbare Hrun _ Hreceipt
  ihave Hcells := (partition capacity era cpu rs shares).mpr $$ [Hhead Hbare]
  · iframe
  iapply Hfinish $$ %view Hcells Hrun Hwindow Hreceipt

end Xv6.Kernel.BareJalFetch
