import MachCSL.Logic.IcacheSlotCouplingSpec
import MachCSL.Logic.IcacheSlotCouplingPureProofs
import MachCSL.Logic.IcacheRefLedgerBootProofs
import MachCSL.Logic.IcacheCouplingBootProofs

namespace MachCSL.Logic.IcacheSlotCoupling
open Iris Iris.BI Xv6.Fs IcacheRefLedger
variable {GF : BundledGFunctors} (ledger : IcacheRefLedger.Capacity GF)
    (coupling : IcacheCoupling.Capacity GF)

instance ireg_rcol_timeless g z c r f n d : Timeless (ireg_rcol ledger g z c r f n d) := by
  unfold ireg_rcol; infer_instance
instance ireg_frzc_timeless names z f : Timeless (ireg_frzc coupling names z f) := by
  unfold ireg_frzc; infer_instance

theorem ireg_rcol_intro g z c r f n rc d (h : ireg_ref_ok r rc n c d) :
    link_auth ledger g z c r f rc ⊢ ireg_rcol ledger g z c r f n d := by
  iintro H; unfold ireg_rcol; iexists rc; iframe H; ipureintro; exact h

theorem ireg_rcol_stable g z c r f n d d' (same : d'.type = d.type) :
    ireg_rcol ledger g z c r f n d ⊢ ireg_rcol ledger g z c r f n d' := by
  unfold ireg_rcol
  iintro ⟨%rc, Ha, %h⟩
  iexists rc; iframe Ha; ipureintro
  exact ireg_ref_ok_stable same h

theorem ireg_rcol_freeze_agree g z c r f n d phase :
    iprop(ireg_rcol ledger g z c r f n d ∗ ifreeze ledger g phase z ⊢ ⌜f = freezeCell phase⌝) := by
  unfold ireg_rcol
  iintro ⟨⟨%rc, Ha, %_⟩, Hf⟩
  iapply link_freeze_agree ledger g z c r f rc phase $$ [$Ha $Hf]

theorem ireg_rcol_claim_agree g z c r f n d ty t q :
    iprop(ireg_rcol ledger g z c r f n d ∗ iclaim ledger g z ty t q ⊢ ⌜c = claimCell ty t q⌝) := by
  unfold ireg_rcol
  iintro ⟨⟨%rc, Ha, %_⟩, Hc⟩
  iapply link_claim_agree ledger g z c r f rc ty t q $$ [$Ha $Hc]

theorem ireg_rcol_mint g b z c r f n d (nz : d.type.toNat ≠ 0) (unclaimed : b = false → c = none) :
    iprop(ireg_rcol ledger g z c r f n d ⊢ |==>
      ((∃ r', ireg_rcol ledger g z c r' f (n + 1) d) ∗ runit ledger g b z)) := by
  unfold ireg_rcol
  iintro ⟨%rc, Ha, %h⟩
  imod link_mint_runit ledger g b z c r f rc $$ Ha with ⟨Ha, Hu⟩
  imodintro
  isplitr [Hu]
  · iexists rup b r, rcup b rc
    iframe Ha; ipureintro
    exact ireg_ref_ok_mint b h nz unclaimed
  · iexact Hu

theorem ireg_rcol_spend g b z c r f n d :
    iprop(ireg_rcol ledger g z c r f (n + 1) d ∗ runit ledger g b z ⊢ |==>
      ∃ r', ireg_rcol ledger g z c r' f n d) := by
  unfold ireg_rcol
  iintro ⟨⟨%rc, Ha, %h⟩, Hu⟩
  ihave %ge := link_runit_ge ledger g b z c r f rc $$ [$Ha $Hu]
  cases b with
  | false =>
    cases r with
    | zero => simp at ge
    | succ r =>
      have spend : iprop(link_auth ledger g z c (r + 1) f rc ∗ runit ledger g false z ⊢ |==> link_auth ledger g z c r f rc) :=
        link_spend_runit ledger g false z c r f rc
      imod spend $$ [$Ha $Hu] with Ha
      imodintro; iexists r, rc; iframe Ha; ipureintro
      exact ireg_ref_ok_spend false h
  | true =>
    cases rc with
    | zero => simp at ge
    | succ rc =>
      have spend : iprop(link_auth ledger g z c r f (rc + 1) ∗ runit ledger g true z ⊢ |==> link_auth ledger g z c r f rc) :=
        link_spend_runit ledger g true z c r f rc
      imod spend $$ [$Ha $Hu] with Ha
      imodintro; iexists r, rc; iframe Ha; ipureintro
      exact ireg_ref_ok_spend true h

theorem ireg_rcol_mint_ok g b z c r f n d :
    iprop(ireg_rcol ledger g z c r f n d ∗ runit ledger g b z ⊢
      ⌜d.type.toNat ≠ 0 ∧ (b = false → c = none)⌝) := by
  unfold ireg_rcol
  iintro ⟨⟨%rc, Ha, %h⟩, Hu⟩
  ihave %ge := link_runit_ge ledger g b z c r f rc $$ [$Ha $Hu]
  ipureintro
  constructor
  · apply ireg_ref_ok_alloc h
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at ge <;> omega
  · intro eq; subst b
    exact ireg_ref_ok_unclaimed h ge

theorem ireg_frzc_intro names z f b (h : ireg_frzm_ok b f) :
    IcacheCoupling.frzm_h coupling names z b ⊢ ireg_frzc coupling names z f := by
  iintro Hb; unfold ireg_frzc; iexists b; iframe Hb; ipureintro; exact h

theorem ireg_frzc_off_acc names z f (h : frz_preb f = false) :
    ireg_frzc coupling names z f ⊢ IcacheCoupling.frzm_h coupling names z false := by
  unfold ireg_frzc
  iintro ⟨%b, Hb, %ok⟩
  have eq : b = false := ok.trans h
  cases b with
  | false => iexact Hb
  | true => cases eq

theorem ireg_frzc_off_intro names z f (h : frz_preb f = false) :
    IcacheCoupling.frzm_h coupling names z false ⊢ ireg_frzc coupling names z f :=
  ireg_frzc_intro coupling names z f false (ireg_frzm_ok_false h)

theorem ireg_frzc_off_iff names z f (h : frz_preb f = false) :
    ireg_frzc coupling names z f ⊣⊢ IcacheCoupling.frzm_h coupling names z false :=
  ⟨ireg_frzc_off_acc coupling names z f h, ireg_frzc_off_intro coupling names z f h⟩

/-- Paired native count and reference update, using both supplied count halves.
The other count value is first established by actual camera agreement. -/
theorem count_mint g names b z c r f n m d (nz : d.type.toNat ≠ 0) (unclaimed : b = false → c = none) :
    iprop(ireg_rcol ledger g z c r f n d ∗ IcacheCoupling.icnt_half coupling names z n ∗
      IcacheCoupling.icnt_half coupling names z m ⊢ |==>
      ((∃ r', ireg_rcol ledger g z c r' f (n + 1) d) ∗ runit ledger g b z ∗
        IcacheCoupling.icnt_half coupling names z (n + 1) ∗ IcacheCoupling.icnt_half coupling names z (n + 1))) := by
  iintro ⟨Hr, Hn, Hm⟩
  ihave %same := IcacheCoupling.count_agree coupling names z n m $$ [$Hn $Hm]
  subst m
  imod IcacheCoupling.count_update coupling names z n (n + 1) $$ [$Hn $Hm] with ⟨Hn,Hm⟩
  imod ireg_rcol_mint ledger g b z c r f n d nz unclaimed $$ Hr with ⟨Hr,Hu⟩
  imodintro; iframe Hr Hu Hn Hm

theorem count_spend g names b z c r f n m d :
    iprop(ireg_rcol ledger g z c r f (n + 1) d ∗ runit ledger g b z ∗
      IcacheCoupling.icnt_half coupling names z (n + 1) ∗ IcacheCoupling.icnt_half coupling names z m ⊢ |==>
      ((∃ r', ireg_rcol ledger g z c r' f n d) ∗
        IcacheCoupling.icnt_half coupling names z n ∗ IcacheCoupling.icnt_half coupling names z n)) := by
  iintro ⟨Hr, Hu, Hn, Hm⟩
  ihave %same := IcacheCoupling.count_agree coupling names z (n + 1) m $$ [$Hn $Hm]
  subst m
  imod IcacheCoupling.count_update coupling names z (n + 1) n $$ [$Hn $Hm] with ⟨Hn,Hm⟩
  imod ireg_rcol_spend ledger g b z c r f n d $$ [$Hr $Hu] with Hr
  imodintro; iframe Hr Hn Hm

theorem boot_rows g names inums records :
    iprop(IcacheRefLedger.bootRows ledger g inums ∗ IcacheCoupling.bootCounts coupling names inums ∗
      IcacheCoupling.bootMirrors coupling names inums ⊢ bootRows ledger coupling g names inums records) := by
  unfold IcacheRefLedger.bootRows IcacheCoupling.bootCounts IcacheCoupling.bootMirrors bootRows
  rw [← BigSepS.bigSepS_sep.to_eq, ← BigSepS.bigSepS_sep.to_eq]
  apply BigSepS.bigSepS_mono_of_forall
  intro z
  iintro ⟨⟨Ha,Hf⟩, ⟨Hn,Hm⟩, ⟨Hb,Hb'⟩⟩
  ihave Hr := ireg_rcol_intro ledger g z none 0 (freezeCell .off) 0 0 (records z)
    (ireg_ref_ok_zero _ _ _) $$ Ha
  ihave Hmirror := ireg_frzc_off_intro coupling names z (freezeCell .off) rfl $$ Hb
  iframe Hr Hf Hn Hm Hmirror Hb'

theorem actual : Spec ledger coupling where
  mint := ireg_rcol_mint ledger
  spend := ireg_rcol_spend ledger
  mirrorOff := ireg_frzc_off_iff coupling
  boot := boot_rows ledger coupling

end MachCSL.Logic.IcacheSlotCoupling
