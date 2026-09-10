import MachCSL.Devices.Uart.Defs
import Lean.Elab.Tactic.Omega

namespace MachCSL.Devices.Uart

theorem read_lsr (u : State) : read u 5 = some (lsr u, u) := rfl

theorem read_total (u : State) (offset : Int) (ho : 0 ≤ offset ∧ offset < size) :
    ∃ b next, read u offset = some (b, next) := by
  unfold read
  repeat' first | split | (exfalso; unfold size at ho; omega)
  all_goals exact ⟨_, _, rfl⟩

theorem write_total (u : State) (offset : Int) (b : Byte)
    (ho : 0 ≤ offset ∧ offset < size) : ∃ next, write u offset b = some next := by
  unfold write
  repeat' first | split | (exfalso; unfold size at ho; omega)
  all_goals exact ⟨_, rfl⟩

theorem recv_out (u : State) (b : Byte) : (recv u b).out = u.out := rfl
theorem recv_tx (u : State) (b : Byte) : (recv u b).tx = u.tx := rfl
theorem recv_lcr (u : State) (b : Byte) : (recv u b).lcr = u.lcr := rfl

theorem dlab_of_lcr (u next : State) (h : next.lcr = u.lcr) : dlab next = dlab u := by
  simp only [dlab, h]

theorem tracked_of_fields (u next : State) (ho : next.out = u.out)
    (ht : next.tx = u.tx) (hl : next.lcr = u.lcr) :
    accepted next = accepted u ∧ next.out = u.out ∧ dlab next = dlab u := by
  exact ⟨by simp only [accepted, ho, ht], ho, dlab_of_lcr u next hl⟩

/-- Includes wire preservation, beyond the source's tracked-field statement. -/
theorem read_fields (u : State) (offset : Int) (b : Byte) (next : State)
    (h : read u offset = some (b, next)) :
    next.tx = u.tx ∧ next.out = u.out ∧ next.wire = u.wire ∧ next.lcr = u.lcr := by
  unfold read at h
  repeat' split at h
  all_goals simp_all
  all_goals rcases h with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩

theorem read_stable (u : State) (offset : Int) (b : Byte) (next : State)
    (h : read u offset = some (b, next)) :
    accepted next = accepted u ∧ next.out = u.out ∧ dlab next = dlab u := by
  have hs := read_fields u offset b next h
  exact tracked_of_fields u next hs.2.1 hs.1 hs.2.2.2

/-- MMIO stores preserve both completed-transmitter and external wire traces. -/
theorem write_traces (u : State) (offset : Int) (b : Byte) (next : State)
    (h : write u offset b = some next) : next.out = u.out ∧ next.wire = u.wire := by
  unfold write at h
  repeat' split at h
  all_goals simp_all
  all_goals subst next; exact ⟨rfl, rfl⟩

theorem write_out (u : State) (offset : Int) (b : Byte) (next : State)
    (h : write u offset b = some next) : next.out = u.out :=
  (write_traces u offset b next h).1

theorem txPop_fields (u : State) (b : Byte) (next : State)
    (h : txPop u = some (b, next)) :
    ∃ rest, u.tx = b :: rest ∧ next.tx = rest ∧ next.out = u.out ++ [b] ∧
      next.wire = (if loopback u then u.wire else u.wire ++ [b]) ∧
      next.lcr = u.lcr ∧ next.mcr = u.mcr := by
  cases ht : u.tx with
  | nil => simp [txPop, ht] at h
  | cons head rest =>
    cases hl : loopback u <;> simp [txPop, ht, hl] at h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals exact ⟨rest, rfl, rfl, rfl, by simp [recv], rfl, rfl⟩

theorem txPop_acc (u : State) (b : Byte) (next : State)
    (h : txPop u = some (b, next)) : accepted next = accepted u := by
  obtain ⟨rest, ht, hn, ho, _⟩ := txPop_fields u b next h
  simp only [accepted, ht, hn, ho, List.append_assoc, List.singleton_append]

theorem txPop_out (u : State) (b : Byte) (next : State)
    (h : txPop u = some (b, next)) : next.out = u.out ++ [b] := by
  obtain ⟨_, _, _, ho, _⟩ := txPop_fields u b next h
  exact ho

theorem txPop_wire (u : State) (b : Byte) (next : State)
    (h : txPop u = some (b, next)) :
    next.wire = if loopback u then u.wire else u.wire ++ [b] := by
  obtain ⟨_, _, _, _, hw, _⟩ := txPop_fields u b next h
  exact hw

theorem txPop_dlab (u : State) (b : Byte) (next : State)
    (h : txPop u = some (b, next)) : dlab next = dlab u := by
  obtain ⟨_, _, _, _, _, hl, _⟩ := txPop_fields u b next h
  exact dlab_of_lcr u next hl

theorem rxPush_fields (u : State) (b : Byte) (next : State)
    (h : rxPush u b = some next) :
    next.out = u.out ∧ next.tx = u.tx ∧ next.lcr = u.lcr ∧ next.wire = u.wire := by
  unfold rxPush at h
  split at h
  · cases Option.some.inj h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · contradiction

theorem rxPush_acc (u : State) (b : Byte) (next : State)
    (h : rxPush u b = some next) : accepted next = accepted u := by
  have hs := rxPush_fields u b next h
  simp only [accepted, hs.1, hs.2.1]

theorem rxPush_out (u : State) (b : Byte) (next : State)
    (h : rxPush u b = some next) : next.out = u.out := (rxPush_fields u b next h).1

theorem rxPush_dlab (u : State) (b : Byte) (next : State)
    (h : rxPush u b = some next) : dlab next = dlab u :=
  dlab_of_lcr u next (rxPush_fields u b next h).2.2.1

theorem rxPush_wire (u : State) (b : Byte) (next : State)
    (h : rxPush u b = some next) : next.wire = u.wire := (rxPush_fields u b next h).2.2.2

theorem write_thr_acc (u : State) (b : Byte) (next : State)
    (hd : dlab u = false) (hr : u.tx.length < fifoDepth)
    (h : write u 0 b = some next) : accepted next = accepted u ++ [b] := by
  simp only [write, hd, hr, if_true, Bool.false_eq_true, if_false] at h
  cases Option.some.inj h
  simp only [accepted, List.append_assoc]

theorem write_1_stable (u : State) (b : Byte) (next : State)
    (h : write u 1 b = some next) :
    accepted next = accepted u ∧ next.out = u.out ∧ dlab next = dlab u := by
  cases hd : dlab u <;> simp [write, hd] at h
  all_goals subst next; exact ⟨rfl, rfl, hd⟩

theorem write_0_dlab_stable (u : State) (b : Byte) (next : State)
    (hd : dlab u = true) (h : write u 0 b = some next) :
    accepted next = accepted u ∧ next.out = u.out ∧ dlab next = dlab u := by
  simp [write, hd] at h
  subst next
  exact tracked_of_fields _ _ rfl rfl rfl

theorem write_3_stable (u : State) (b : Byte) (next : State)
    (h : write u 3 b = some next) :
    accepted next = accepted u ∧ next.out = u.out ∧ dlab next = b.getLsbD 7 := by
  simp [write] at h
  subst next
  exact ⟨rfl, rfl, rfl⟩

theorem write_2_stable (u : State) (b : Byte) (next : State)
    (ht : u.tx = []) (h : write u 2 b = some next) :
    accepted next = accepted u ∧ next.out = u.out ∧ dlab next = dlab u := by
  simp [write] at h
  subst next
  simp [accepted, dlab, ht]

theorem write_lcr_0 (u : State) (b : Byte) (next : State)
    (h : write u 0 b = some next) : next.lcr = u.lcr := by
  simp only [write, if_true] at h
  repeat' split at h
  all_goals cases Option.some.inj h; rfl

theorem write_dlab_0 (u : State) (b : Byte) (next : State)
    (h : write u 0 b = some next) : dlab next = dlab u :=
  dlab_of_lcr u next (write_lcr_0 u b next h)

theorem tx_empty_of_out (u : State) (trace : List Byte)
    (ha : accepted u = trace) (hp : trace <+: u.out) : u.tx = [] := by
  obtain ⟨suffix, hs⟩ := hp
  have hl := congrArg List.length ha
  simp only [accepted, List.length_append] at hl
  have hm := congrArg List.length hs
  simp only [List.length_append] at hm
  apply List.eq_nil_of_length_eq_zero
  omega

/-- An ISR read acknowledges only a reported THRE interrupt. -/
theorem read_isr_ack (u : State) (h : isrThri u = true) :
    read u 2 = some (isr u, {u with thri := false}) := by simp [read, h]

theorem read_isr_no_ack (u : State) (h : isrThri u = false) :
    read u 2 = some (isr u, u) := by simp [read, h]

theorem acknowledged_tx_quiet (u : State) : txInterrupt {u with thri := false} = false := by
  simp [txInterrupt]

theorem rx_priority (u : State) (h : rxInterrupt u = true) : isrThri u = false := by
  simp [isrThri, h]

theorem irq_disabled (u : State) (h : u.ier = 0) : irq u = false := by
  simp [irq, rxInterrupt, txInterrupt, h]

/-- A full THR discards the data but still performs interrupt acknowledgement. -/
theorem write_thr_full (u : State) (b : Byte) (hd : dlab u = false)
    (hf : fifoDepth ≤ u.tx.length) : write u 0 b = some {u with thri := false} := by
  simp [write, hd, Nat.not_lt.mpr hf]

theorem read_rhr_empty (u : State) (hd : dlab u = false) (hr : u.rx = []) :
    read u 0 = some ((if fifoEnabled u then 0 else u.rbr), u) := by
  simp [read, hd, hr]

theorem read_rhr_pop (u : State) (b : Byte) (rest : List Byte)
    (hd : dlab u = false) (hr : u.rx = b :: rest) :
    read u 0 = some (b, {u with rx := rest}) := by simp [read, hd, hr]

theorem recv_rbr (u : State) (b : Byte) : (recv u b).rbr = b := rfl

theorem recv_overrun (u : State) (b : Byte) (hf : fifoDepth ≤ u.rx.length) :
    recv u b = {u with rbr := b} := by simp [recv, Nat.not_lt.mpr hf]

theorem rxPush_full (u : State) (b : Byte) (hf : fifoDepth ≤ u.rx.length) :
    rxPush u b = none := by simp [rxPush, Nat.not_lt.mpr hf]

theorem rxPush_room (u : State) (b : Byte) (hr : u.rx.length < fifoDepth) :
    rxPush u b = some {u with rx := u.rx ++ [b], rbr := b} := by simp [rxPush, recv, hr]

theorem recv_rx_bound (u : State) (b : Byte) (hr : u.rx.length ≤ fifoDepth) :
    (recv u b).rx.length ≤ fifoDepth := by
  simp only [recv]
  split <;> simp_all only [List.length_append, List.length_singleton]
  all_goals omega

theorem txPop_last_thri (u : State) (b : Byte) (next : State)
    (ht : u.tx = [b]) (h : txPop u = some (b, next)) : next.thri = true := by
  cases hl : loopback u <;> simp [txPop, ht, hl] at h
  all_goals subst next; rfl

/-- Byte-level board reset checks use ordinary kernel reduction. -/
theorem initial_status : lsr initial = 0x60 ∧ isr initial = 1 ∧
    irq initial = false ∧ initial.dll = 0x0c ∧ initial.mcr = 0x08 := by decide

/-- Enabling THRI while idle arms it, and one ISR read acknowledges it. -/
theorem idle_thri_acknowledgement :
    ∃ armed quiet,
      write initial 1 2 = some armed ∧ irq armed = true ∧
      read armed 2 = some (2, quiet) ∧ irq quiet = false ∧
      read quiet 2 = some (1, quiet) := by
  refine ⟨{initial with ier := 2, thri := true}, {initial with ier := 2}, ?_⟩
  decide

/-- Local loopback completes the transmitter but produces no external byte. -/
theorem loopback_example :
    txPop {initial with tx := [0x41], mcr := 0x10} =
      some (0x41, {initial with rx := [0x41], out := [0x41], mcr := 0x10, rbr := 0x41, thri := true}) := by decide

/-- FCR bit0 toggling clears both queues and retains the last RBR byte. -/
theorem fifo_toggle_example :
    write {initial with rx := [0x41], tx := [0x42], rbr := 0x41} 2 1 =
      some {initial with fcr := 1, rbr := 0x41, thri := true} := by decide

/-- FIFO clearing can strictly shrink accepted; no global write-monotonicity law. -/
theorem fifo_clear_drops_accepted :
    ∃ next, write {initial with tx := [0x41]} 2 4 = some next ∧
      accepted next = [] ∧ accepted {initial with tx := [0x41]} = [0x41] := by
  refine ⟨{initial with thri := true}, ?_⟩
  decide

end MachCSL.Devices.Uart
