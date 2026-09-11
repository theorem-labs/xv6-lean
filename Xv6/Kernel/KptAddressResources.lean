import Xv6.Kernel.KptAddressGeometry
import Xv6.Kernel.KptResidueLink
import Xv6.Kernel.KptTranslateLink

namespace Xv6.Kernel.KptAddress
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem open_residue era cpu rs (N : Namespace) root :
    iprop(KptResidue.residue capacity era cpu N root ⊢ ∃ data, opened capacity era cpu rs N root data) := by
  iintro Hresidue
  iunfold KptResidue.residue at Hresidue
  iunfold KptResidue.parts at Hresidue
  icases Hresidue with ⟨%satp,%tlb,Hsatp,%rooted,Htlb,Hsnapshot,Hpmp,Hshared,Hcredential⟩
  iunfold KptResidue.pmpConfig at Hpmp
  iunfold MachCSL.Logic.SupervisorPmp.config at Hpmp
  icases Hpmp with ⟨%old,%tor,Hcells⟩
  isimp only [MachCSL.Logic.SupervisorPmp.footprint, RegisterFootprint.cells] at Hcells
  icases Hcells with ⟨Hcfg,Haddr,_⟩
  iexists ⟨satp, tlb, old .pmpcfg_n, old .pmpaddr_n⟩
  iunfold opened
  iunfold dataCells
  iframe Hsatp Htlb Hcfg Haddr Hsnapshot Hshared Hcredential
  isplit
  · ipureintro; exact rooted
  · ipureintro; exact tor_of_vectors old rs _ rfl rfl tor

theorem close_residue era cpu rs (N : Namespace) root data :
    iprop(opened capacity era cpu rs N root data ⊢ KptResidue.residue capacity era cpu N root) := by
  iintro Hopened
  iunfold opened at Hopened
  icases Hopened with ⟨Hcells,%rooted,Hsnapshot,%tor,Hshared,Hcredential⟩
  iunfold dataCells at Hcells
  icases Hcells with ⟨Hsatp,Htlb,Hcfg,Haddr⟩
  iunfold KptResidue.residue
  iexists data.satp, data.tlb
  iunfold KptResidue.parts
  iframe Hsatp Htlb Hsnapshot Hshared Hcredential
  isplit
  · ipureintro; exact rooted
  · iunfold KptResidue.pmpConfig
    iunfold MachCSL.Logic.SupervisorPmp.config
    iexists prepare rs data
    isplit
    · ipureintro; exact tor
    · simp only [MachCSL.Logic.SupervisorPmp.footprint, RegisterFootprint.cells, prepare_cfg, prepare_addr]
      iframe Hcfg Haddr

theorem partition era cpu rs shares data :
    iprop(cells capacity era cpu (prepare rs data) shares ⊣⊢
      auxiliaryCells capacity era cpu rs shares ∗ dataCells capacity era cpu data) := by
  simp only [cells, auxiliaryCells, dataCells, footprint, auxiliaryFootprint,
    outerShares, innerShares, Sv39Address.footprint, SupervisorBare.footprint,
    KptTranslate.footprint, KptMiss.footprint, KptAD.footprint, SupervisorPteAD.footprint,
    SupervisorPteRead.footprint, SupervisorRead.footprint, List.cons_append, List.nil_append,
    RegisterFootprint.cells, prepare_status, prepare_privilege, prepare_satp,
    prepare_pma, prepare_cfg, prepare_addr, prepare_htif, prepare_environment, prepare_tlb,
    KptResidue.satpCell, KptResidue.tlbCell]
  constructor
  · iintro ⟨Hstatus,Hpriv,Hsatp,Hpma,Hcfg,Haddr,Hhtif,Henv,Htlb,_⟩
    iframe Hstatus Hpriv Hsatp Hpma Hcfg Haddr Hhtif Henv Htlb
  · iintro ⟨⟨Hstatus,Hpriv,Hpma,Hhtif,Henv,_⟩,Hsatp,Htlb,Hcfg,Haddr⟩
    iframe Hstatus Hpriv Hsatp Hpma Hcfg Haddr Hhtif Henv Htlb

theorem split_cells era cpu rs shares :
    iprop(cells capacity era cpu rs shares ⊣⊢
      Sv39Address.cells capacity.machine era cpu rs (outerShares shares) ∗
      KptTranslate.cells capacity era cpu rs (innerShares shares)) :=
  RegisterFootprint.cells_append capacity.machine.era.registers (era.registers cpu) rs _ _

theorem outer_cells_after era cpu rs shares data address ppn permission (tree : PtTree.Tree) p2 p1 (a d : Bool) branch :
    Sv39Address.cells capacity.machine era cpu
      (KptTranslate.after (prepare rs data) 0#16 (Sv39Address.vpn address) p2 p1 ppn permission branch)
      (outerShares shares) =
    Sv39Address.cells capacity.machine era cpu (prepare rs data) (outerShares shares) := by
  rw [after rs data address ppn permission tree p2 p1 a d branch]
  simp only [Sv39Address.cells, Sv39Address.footprint, SupervisorBare.footprint, outerShares,
    RegisterFootprint.cells, prepare_status, prepare_privilege, prepare_satp,
    afterData]

theorem return_translated era cpu rs shares N root data address ppn permission tree p2 p1 a d bound rr branch
    (rooted : KptResidue.SatpRooted root data.satp)
    (tor : MachCSL.Machine.SupervisorPmp.TorRam (prepare rs data)) :
    iprop(⊢ Sv39Address.cells capacity.machine era cpu (prepare rs data) (outerShares shares) -∗
      KptShared.mapAt capacity era (Sv39Address.vpn address) ppn permission -∗
      KptTranslate.resources capacity era cpu (prepare rs data) (innerShares shares) N root tree bound
        0#16 (Sv39Address.vpn address) p2 p1 ppn permission rr branch -∗
      resources capacity era cpu rs shares N root data address ppn permission rr
        (.translated tree p2 p1 a d branch)) := by
  iintro Houter Hmap Htranslated
  iunfold KptTranslate.resources at Htranslated
  icases Htranslated with ⟨Hinner,Hclients,Hresv,Hreceipts,%coherent⟩
  ihave Hcells := (split_cells capacity era cpu _ shares).mpr $$ [Houter Hinner]
  · rw [outer_cells_after capacity era cpu rs shares data address ppn permission tree p2 p1 a d branch]
    iframe Houter Hinner
  isimp only [after rs data address ppn permission tree p2 p1 a d branch] at Hcells
  ihave ⟨Haux,Hdata⟩ := (partition capacity era cpu rs shares _).mp $$ Hcells
  iunfold KptTranslate.clients at Hclients
  iunfold KptMiss.clients at Hclients
  iunfold KptTreeWalk.clients at Hclients
  icases Hclients with ⟨Hshared,Hsnapshot,Hbound,Hcredential⟩
  iunfold resources
  simp only [afterReservation, receipts]
  iframe Haux Hmap Hresv Hreceipts
  iunfold opened
  iframe Hdata Hshared
  isplit
  · ipureintro; exact rooted
  · isplitl [Hsnapshot]
    · simp only [afterData]
      iapply (KptResidue.nativeSpec capacity).snapshot_intro era tree _ coherent $$ Hsnapshot
    · isplit
      · ipureintro; exact tor_after rs data address ppn permission _ tor
      · iapply (KptResidue.nativeSpec capacity).credentials_intro era cpu bound $$ Hbound Hcredential

theorem resourceSpec : ResourceSpec capacity :=
  ⟨open_residue capacity, close_residue capacity, partition capacity⟩

end Xv6.Kernel.KptAddress
