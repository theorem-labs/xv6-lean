import Xv6.Kernel.MycpuBareSourcePure
import Xv6.Kernel.MycpuOffResources
import Xv6.Kernel.KernelDatumWordLink
import Xv6.Kernel.KernelTextDatumLink
import Xv6.Kernel.KernelTextImageLink

namespace Xv6.Kernel.MycpuBareSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem identity_word era ξ address word :
    iprop(KernelDatum.word capacity.translation era .identity ξ address (.own 1) word ⊢
      TsoContextReadWP.wordPointsto capacity.machine era ξ address (.own 1) word ∗
      closeWord capacity era ξ address) := by
  iintro Hword
  ihave ⟨%ppn,Hclaims,Hword,Hclose⟩ :=
    (KernelDatumWord.nativeSpec capacity.translation).access era .identity ξ address (.own 1) word $$ Hword
  ihave Hhead := (KernelDatumWord.nativeSpec capacity.translation).head era .identity address ppn $$ Hclaims
  iunfold KernelDatum.claim at Hhead
  icases Hhead with ⟨_,%facts⟩
  have ident : KernelDatum.physical ppn address = address := facts.2.2
  isimp only [ident] at Hword Hclose
  unfold closeWord
  iframe

theorem text_resources era : iprop(KernelTextImage.text capacity.translation era .identity ⊢
    KernelTextImage.text capacity.translation era .identity ∗ MycpuBare.shared capacity.machine era) := by
  iintro #Htext
  ihave Hwindow := (KernelTextImage.nativeSpec capacity.translation).window era .identity
    MycpuDecode.base 34 MycpuBootResources.spanWord text $$ Htext
  ihave ⟨Hbytes,Hpristine,_⟩ := (KernelTextDatum.nativeWindowSpec capacity.translation).identity_access
    era (KernelTextImage.address MycpuDecode.base) 34 .discard MycpuBootResources.spanWord $$ Hwindow
  iframe Htext
  ieval (change _ ⊢ iprop(KernelTextDatum.physicalWindow capacity.translation era (KernelTextImage.address MycpuDecode.base) 34 .discard MycpuBootResources.spanWord ∗ KernelTextDatum.pristineWindow capacity.translation era (KernelTextImage.address MycpuDecode.base) 34))
  isplit
  · iexact Hbytes
  · iexact Hpristine

theorem packet era cpu control file :
    iprop(MycpuRegimeShell.resources capacity era cpu .bare control file MycpuRegimeShell.sourceShares ⊣⊢
      ∃ satp pmp, ⌜_get_Satp64_Mode (Mk_Satp64 satp) = 0#4⌝ ∗ ⌜SupervisorPmp.TorRam pmp⌝ ∗
        MycpuOff.resources (bareCapacity capacity) era cpu (patch control satp pmp) file shares) := by
  simp only [MycpuRegimeShell.resources, MycpuRegimeShell.translation, MycpuRegimeShell.bare,
    MycpuRegimeShell.controls, MycpuRegimeShell.controlFootprint, MycpuRegimeShell.sourceShares,
    SupervisorRetirement.pcFootprint, SupervisorRetirement.retirementFootprint, SupervisorClock.clockFootprint,
    MycpuOff.resources, MycpuOff.controls, MycpuOff.control_list, shares, patch,
    bareCapacity, MycpuOff.Capacity.supervisorBits, MycpuRegimeShell.Capacity.supervisorBits,
    MachCSL.Logic.SupervisorPmp.config, MachCSL.Logic.SupervisorPmp.footprint,
    List.cons_append, List.nil_append, RegisterFootprint.cells]
  constructor
  · iintro ⟨⟨Hpc,Hnext,Hret,Hinc,Hinhibit,Hrcfg,Hcycle,Htime,Hip,Hpriv,Hisa,Hie,Hideleg,Henv,Help,Hpma,Hhtif,Hhart,_⟩,
      Hms,Hoff,Hgprs,⟨%satp,Hsatp,%mode,%pmp,%tor,Hpmp⟩⟩
    icases Hpmp with ⟨Hcfg,Haddr,_⟩
    iexists satp,pmp
    iframe
    isplitr
    · ipureintro; exact mode
    ipureintro; exact tor
  · iintro ⟨%satp,%pmp,%mode,%tor,
      ⟨Hpc,Hisa,Hpriv,Hsatp,Hpma,Hcfg,Haddr,Hhtif,Hie,Hideleg,Henv,Help,Hnext,Hret,Hinc,Hinhibit,Hrcfg,Hcycle,Htime,Hip,Hhart,_⟩,
      Hms,Hoff,Hgprs⟩
    iframe Hpc Hnext Hret Hinc Hinhibit Hrcfg Hcycle Htime Hip Hpriv Hisa Hie Hideleg Henv Help Hpma Hhtif Hhart Hms Hoff Hgprs
    iexists satp
    iframe Hsatp
    isplitr
    · ipureintro; exact mode
    iexists pmp
    iframe
    ipureintro; exact tor

end Xv6.Kernel.MycpuBareSource
