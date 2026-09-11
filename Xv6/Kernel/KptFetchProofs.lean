import Xv6.Kernel.KptFetchFoldProofs
import Xv6.Kernel.KptFetchWindowProofs

namespace Xv6.Kernel.KptFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem wp_fetch shares rs (config : Config rs) tier result image fixed whole gen era cpu
    (N : Namespace) root rr continuation post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ KptResidue.residue capacity era cpu N root -∗
      instrBytes capacity era tier (rs .PC) result -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root tier result rr continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  iintro #Hcert Hcells Hresidue #Hbytes Hresv Hfinish
  ihave ⟨%word,%facts,Hwindows⟩ := select_word capacity era tier (rs .PC) result $$ Hbytes
  rcases facts with ⟨equal,aligned⟩
  subst result
  iapply fold capacity shares rs config (fetch_plan shares rs config.compressed aligned word)
    tier image fixed whole gen era cpu N root rr continuation post $$ Hcert Hcells Hresidue Hwindows Hresv
  rw [parts_addresses]
  iunfold finish at Hfinish
  iapply guardChunks_mono $$ [] Hfinish
  iintro %trace Hdone Hresources
  iapply Hdone $$ [Hresources]
  iunfold resources
  iunfold runResources at Hresources
  icases Hresources with ⟨Hcells,Hresidue,Hresv,Hreceipts⟩
  iframe Hcells Hresidue Hresv Hreceipts Hbytes

theorem actual : Spec capacity := ⟨wp_fetch capacity⟩

end Xv6.Kernel.KptFetch
