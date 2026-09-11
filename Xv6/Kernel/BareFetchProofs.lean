import Xv6.Kernel.BareFetchSpec
import Xv6.Kernel.BareJalFetchFoldProofs

namespace Xv6.Kernel.BareFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

instance code_persistent era pc result : Persistent (code capacity era pc result) := by
  unfold code
  infer_instance

theorem wp_fetch shares rs (config : Config rs) result image fixed whole gen era cpu ξ continuation post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity.machine era cpu ξ -∗
      code capacity era (rs .PC) result -∗
      finish capacity image fixed whole gen era cpu ξ rs shares result continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  iintro #Hcert Hcells Hrun #Hcode Hfinish
  ihave Hbytes : KptFetch.instrBytes capacity era .identity (rs .PC) result $$ []
  · iunfold code at Hcode; iexact Hcode
  ihave ⟨%selected,%facts,Hwindows⟩ := KptFetch.select_word capacity era .identity (rs .PC) result $$ Hbytes
  rcases facts with ⟨equal,aligned⟩
  iapply BareJalFetch.fold capacity shares rs config
    (BareJalFetch.fetch_plan shares rs config.compressed aligned selected)
    image fixed whole gen era cpu ξ continuation post $$ Hcert Hcells Hrun Hwindows
  rw [KptFetch.parts_addresses,equal]
  iunfold finish at Hfinish
  iunfold guards at Hfinish
  iapply BareJalFetch.guardReads_mono $$ [] Hfinish
  iintro %views Hdone ⟨Hcells,Hrun,Hreceipts⟩
  iapply Hdone
  iunfold resources
  iframe Hcells Hrun Hcode Hreceipts

theorem actual : Spec capacity := ⟨wp_fetch capacity⟩
end Xv6.Kernel.BareFetch
