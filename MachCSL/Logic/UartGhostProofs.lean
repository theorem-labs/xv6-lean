import MachCSL.Logic.UartGhostSpec

namespace MachCSL.Logic.UartGhost
open Iris Iris.BI Iris.CMRA MachCSL.Memory
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance sent_persistent names bytes : Persistent (sent capacity names bytes) := by
  unfold sent; infer_instance
instance sent_timeless names bytes : Timeless (sent capacity names bytes) := by
  unfold sent; infer_instance
instance outLB_persistent names bytes : Persistent (outLB capacity names bytes) := by
  unfold outLB; infer_instance
instance outLB_timeless names bytes : Timeless (outLB capacity names bytes) := by
  unfold outLB; infer_instance
instance sentAuth_timeless names u : Timeless (sentAuth capacity names u) := by
  unfold sentAuth; infer_instance
instance outAuth_timeless names u : Timeless (outAuth capacity names u) := by
  unfold outAuth; infer_instance
instance txOwn_timeless names bytes : Timeless (txOwn capacity names bytes) := by
  unfold txOwn; infer_instance
instance txAuth_timeless names u : Timeless (txAuth capacity names u) := by
  unfold txAuth; infer_instance
instance dlabIs_timeless names dq value : Timeless (dlabIs capacity names dq value) := by
  unfold dlabIs; infer_instance
instance dlabAuth_timeless names u : Timeless (dlabAuth capacity names u) := by
  unfold dlabAuth; infer_instance
instance dlabOff_persistent names : Persistent (dlabOff capacity names) := by
  unfold dlabOff dlabIs; infer_instance
instance ghosts_timeless names u : Timeless (ghosts capacity names u) := by
  unfold ghosts; infer_instance

theorem sent_get names u : iprop(⊢ sentAuth capacity names u -∗
    sentAuth capacity names u ∗ sent capacity names (Devices.Uart.accepted u)) := by
  letI := capacity.traces
  unfold sentAuth sent
  iintro Ha
  ihave #Hl := MonoList.lb_own_get names.accepted (.own 1) (Devices.Uart.accepted u) $$ Ha
  iframe Ha Hl

theorem out_get names u : iprop(⊢ outAuth capacity names u -∗
    outAuth capacity names u ∗ outLB capacity names u.out) := by
  letI := capacity.traces
  unfold outAuth outLB
  iintro Ha
  ihave #Hl := MonoList.lb_own_get names.output (.own 1) u.out $$ Ha
  iframe Ha Hl

theorem sent_update names u u' (grows : Devices.Uart.accepted u <+: Devices.Uart.accepted u') :
    iprop(sentAuth capacity names u ⊢ |==> (sentAuth capacity names u' ∗ sent capacity names (Devices.Uart.accepted u'))) := by
  letI := capacity.traces
  unfold sentAuth sent
  iintro Ha
  imod MonoList.auth_own_update names.accepted (Devices.Uart.accepted u') grows $$ Ha with ⟨Ha, Hl⟩
  imodintro; iframe

theorem out_update names u u' (grows : u.out <+: u'.out) :
    iprop(outAuth capacity names u ⊢ |==> (outAuth capacity names u' ∗ outLB capacity names u'.out)) := by
  letI := capacity.traces
  unfold outAuth outLB
  iintro Ha
  imod MonoList.auth_own_update names.output u'.out grows $$ Ha with ⟨Ha, Hl⟩
  imodintro; iframe

theorem out_prefix names u bytes : iprop(⊢ outAuth capacity names u -∗ outLB capacity names bytes -∗
    ⌜bytes <+: u.out⌝) := by
  letI := capacity.traces
  unfold outAuth outLB
  iintro Ha Hb
  ihave %valid := MonoList.auth_lb_own_valid names.output (.own 1) u.out bytes $$ Ha Hb
  ipureintro; exact valid.2


theorem sent_stable names u u' (same : Devices.Uart.accepted u' = Devices.Uart.accepted u) :
    iprop(sentAuth capacity names u ⊢ sentAuth capacity names u') := by rw [sentAuth, sentAuth, same]
theorem out_stable names u u' (same : u'.out = u.out) :
    iprop(outAuth capacity names u ⊢ outAuth capacity names u') := by rw [outAuth, outAuth, same]
theorem tx_stable names u u' (same : Devices.Uart.accepted u' = Devices.Uart.accepted u) :
    iprop(txAuth capacity names u ⊢ txAuth capacity names u') := by rw [txAuth, txAuth, same]
theorem dlab_stable names u u' (same : Devices.Uart.dlab u' = Devices.Uart.dlab u) :
    iprop(dlabAuth capacity names u ⊢ dlabAuth capacity names u') := by rw [dlabAuth, dlabAuth, same]

theorem tx_agree names u bytes : iprop(⊢ txAuth capacity names u -∗ txOwn capacity names bytes -∗
    ⌜Devices.Uart.accepted u = bytes⌝) := by
  letI := capacity.transmitter
  unfold txAuth txOwn
  iintro Ha Hb
  iapply ghost_var_agree $$ Ha Hb

theorem tx_update names u bytes u' : iprop(⊢ txAuth capacity names u -∗ txOwn capacity names bytes ==∗
    txAuth capacity names u' ∗ txOwn capacity names (Devices.Uart.accepted u')) := by
  letI := capacity.transmitter
  unfold txAuth txOwn
  exact ghost_var_update_halves (Devices.Uart.accepted u') names.transmitter (Devices.Uart.accepted u) bytes

theorem dlab_agree names u dq value : iprop(⊢ dlabAuth capacity names u -∗ dlabIs capacity names dq value -∗
    ⌜Devices.Uart.dlab u = value⌝) := by
  unfold dlabAuth dlabIs
  iintro Ha Hb
  ihave %valid := iOwn_cmraValid_op (E := capacity.dlab) $$ [$Ha $Hb]
  ipureintro
  exact DiscreteO.eqv_inj (DFracAgree.op_valid.mp valid).2

theorem dlab_update names u value u' :
    iprop(⊢ dlabAuth capacity names u -∗ dlabIs capacity names (.own (1 : Qp).half) value ==∗
      dlabAuth capacity names u' ∗ dlabIs capacity names (.own (1 : Qp).half) (Devices.Uart.dlab u')) := by
  unfold dlabAuth dlabIs
  iintro Ha Hb
  ihave H := (iOwn_op (E := capacity.dlab)).mpr $$ [$Ha $Hb]
  imod iOwn_update (E := capacity.dlab) (DFracAgree.update₂ (by
    change DFrac.own ((1 : Qp).half + (1 : Qp).half) = DFrac.own 1
    rw [Qp.half_add_half])) $$ H with H
  imodintro
  iapply (iOwn_op (E := capacity.dlab)).mp $$ H

theorem dlab_freeze names : iprop(dlabIs capacity names (.own (1 : Qp).half) false ⊢ |==> dlabOff capacity names) := by
  unfold dlabOff dlabIs
  iintro H
  iapply iOwn_update (E := capacity.dlab) DFracAgree.persist $$ H

theorem ghosts_stable names u u' (acc : Devices.Uart.accepted u' = Devices.Uart.accepted u)
    (out : u'.out = u.out) (dlab : Devices.Uart.dlab u' = Devices.Uart.dlab u) :
    iprop(ghosts capacity names u ⊢ ghosts capacity names u') := by
  unfold ghosts sentAuth outAuth txAuth dlabAuth
  rw [acc, out, dlab]


theorem tx_ready_persists names (u : Devices.Uart.State) bytes :
    iprop(⊢ txOwn capacity names bytes -∗ outLB capacity names bytes -∗ dlabOff capacity names -∗
      txAuth capacity names u -∗ outAuth capacity names u -∗ dlabAuth capacity names u -∗
      ⌜u.tx = [] ∧ Devices.Uart.dlab u = false⌝) := by
  iintro Htx Hl Hd Ha Ho Hda
  ihave %acc := tx_agree capacity names u bytes $$ Ha Htx
  ihave %out := out_prefix capacity names u bytes $$ Ho Hl
  iunfold dlabOff at Hd
  ihave %dlab := dlab_agree capacity names u .discard false $$ Hda Hd
  ipureintro
  exact ⟨Devices.Uart.tx_empty_of_out u bytes acc out, dlab⟩

theorem tx_poll_thre names (u : Devices.Uart.State) bytes (ready : Devices.Uart.thre u = true) :
    iprop(⊢ txOwn capacity names bytes -∗ txAuth capacity names u -∗ outAuth capacity names u -∗
      txOwn capacity names bytes ∗ txAuth capacity names u ∗ outAuth capacity names u ∗
      outLB capacity names bytes ∗ ⌜u.tx = [] ∧ Devices.Uart.accepted u = bytes⌝) := by
  iintro Hown Htx Hout
  ihave %acc := tx_agree capacity names u bytes $$ Htx Hown
  have empty : u.tx = [] := List.isEmpty_iff.mp ready
  have out : u.out = bytes := by simpa [Devices.Uart.accepted, empty] using acc
  ihave ⟨Hout, Hlb⟩ := out_get capacity names u $$ Hout
  rw [out]
  iframe
  ipureintro
  exact ⟨empty, acc⟩

theorem allocate (u : Devices.Uart.State) : iprop(⊢ |==> ∃ names,
    ghosts capacity names u ∗ initialClients capacity names u) := by
  letI := capacity.traces
  letI := capacity.transmitter
  imod MonoList.own_alloc (Devices.Uart.accepted u) with ⟨%γa, Ha, Hsent⟩
  imod MonoList.own_alloc u.out with ⟨%γo, Ho, _⟩
  imod ghost_var_alloc (Devices.Uart.accepted u) with ⟨%γt, Ht⟩
  have splitTx := ghost_var_split (GF := GF) γt (Devices.Uart.accepted u) (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at splitTx
  ihave ⟨Hta, Htc⟩ := splitTx $$ Ht
  imod iOwn_alloc (E := capacity.dlab) (DFracAgree.mk (.own 1) (DiscreteO.mk (Devices.Uart.dlab u)))
    (DFracAgree.mk_valid.mpr DFrac.valid_own_one) with ⟨%γd, Hd⟩
  have halves : (DFrac.own 1) = DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half := by
    change DFrac.own 1 = DFrac.own ((1 : Qp).half + (1 : Qp).half)
    rw [Qp.half_add_half]
  have splitD := DFracAgree.mk_op (a := DiscreteO.mk (Devices.Uart.dlab u))
    (d₁ := DFrac.own (1 : Qp).half) (d₂ := DFrac.own (1 : Qp).half)
  rw [← halves] at splitD
  rw [splitD]
  ihave ⟨Hda, Hdc⟩ := (iOwn_op (E := capacity.dlab)).mp $$ Hd
  imodintro
  iexists (⟨γa, γo, γt, γd⟩ : Names)
  unfold ghosts initialClients sentAuth sent outAuth txAuth txOwn dlabAuth dlabIs
  iframe


theorem tx_step names (u next : Devices.Uart.State) (byte : Byte)
    (step : Devices.Uart.txPop u = some (byte, next)) :
    iprop(ghosts capacity names u ⊢ |==> ghosts capacity names next) := by
  unfold ghosts
  iintro ⟨Ha, Ho, Htx, Hd⟩
  ihave Ha := sent_stable capacity names u next (Devices.Uart.txPop_acc u byte next step) $$ Ha
  ihave Htx := tx_stable capacity names u next (Devices.Uart.txPop_acc u byte next step) $$ Htx
  ihave Hd := dlab_stable capacity names u next (Devices.Uart.txPop_dlab u byte next step) $$ Hd
  imod out_update capacity names u next (by
    rw [Devices.Uart.txPop_out u byte next step]
    exact ⟨[byte], rfl⟩) $$ Ho with ⟨Ho, _⟩
  imodintro
  iframe

theorem rx_step names (u next : Devices.Uart.State) (byte : Byte)
    (step : Devices.Uart.rxPush u byte = some next) :
    iprop(ghosts capacity names u ⊢ ghosts capacity names next) :=
  ghosts_stable capacity names u next (Devices.Uart.rxPush_acc u byte next step)
    (Devices.Uart.rxPush_out u byte next step) (Devices.Uart.rxPush_dlab u byte next step)


theorem uartGhostSpec : UartGhostSpec capacity :=
  ⟨allocate capacity, sent_get capacity, out_get capacity, sent_update capacity, out_update capacity,
    out_prefix capacity, tx_agree capacity, tx_update capacity, dlab_agree capacity, dlab_update capacity,
    dlab_freeze capacity, ghosts_stable capacity, tx_ready_persists capacity, tx_poll_thre capacity⟩

end MachCSL.Logic.UartGhost
