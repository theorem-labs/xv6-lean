import MachCSL.Devices.Virtio.Dma
import MachCSL.Devices.Virtio.Proofs

/-!
Operational Virtio DMA laws. No driver queue or ownership invariant is assumed
by the definitions; those obligations remain for the machine/logic layers.

Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.
-/
namespace MachCSL.Devices.Virtio

@[simp] theorem view_bytes_length (mv : vmem) (a : Address) (n : Nat) :
    (view_bytes mv a n).length = n := by simp [view_bytes]

theorem mem_view_subseteq (m₁ m₂ : ByteMap) (mv : vmem)
    (hs : MachCSL.Memory.Submap m₁ m₂) (hv : mem_view m₂ mv) : mem_view m₁ mv :=
  fun a b h => hv a b (hs a b h)

/-- Any total view extends the empty partial memory; no default bytes are imposed. -/
theorem mem_view_empty (mv : vmem) : mem_view MachCSL.Memory.empty mv := by
  intro a b h
  cases h

private theorem mapM_view (xs : List α) (f : α → Option Byte) (g : α → Byte)
    (hv : ∀ x b, f x = some b → g x = b) (bs : List Byte) (hr : xs.mapM f = some bs) :
    xs.map g = bs := by
  induction xs generalizing bs with
  | nil => simpa using hr
  | cons x xs ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hr
    cases hx : f x with
    | none => simp [hx] at hr
    | some b =>
      cases ht : xs.mapM f with
      | none => simp [hx, ht] at hr
      | some rest =>
        simp [hx, ht] at hr
        subst bs
        simp [hv x b hx, ih rest ht]

theorem view_bytes_read (m : ByteMap) (mv : vmem) (a : Address) (n : Nat) (bs : List Byte)
    (hv : mem_view m mv) (hr : read_byte_list m a n = some bs) : view_bytes mv a n = bs :=
  mapM_view _ _ _ (fun _ b h => hv _ b h) bs hr

theorem view_word_read (m : ByteMap) (mv : vmem) (a : Address) (n : Nat) (w : BitVec (8*n))
    (hv : mem_view m mv) (hr : read_bytes m a n = some w) : view_word mv a n = w := by
  unfold read_bytes at hr
  cases hb : read_byte_list m a n with
  | none => simp [hb] at hr
  | some bs =>
    simp [hb] at hr
    subst w
    simp only [view_word, view_bytes_read m mv a n bs hv hb]

theorem cache_disjoint_spec (ss : Sectors) (cache : Cache) :
    cache_disjoint ss cache = true ↔ ∀ s, s ∈ ss → cache[s]? = none := by
  simp [cache_disjoint, List.all_eq_true, Std.ExtTreeSet.mem_toList, Option.isNone_iff_eq_none]

theorem cache_overlay_lookup (fresh old : Cache) (s : Int) :
    (cache_overlay fresh old)[s]? = (fresh[s]?).or (old[s]?) := by
  rw [cache_overlay, Std.ExtTreeMap.getElem?_mergeWith']
  cases fresh[s]? <;> cases old[s]? <;> rfl

/-- Capture overrides earlier volatile bytes, preserving the source's left-biased union. -/
theorem cache_overlay_new (fresh old : Cache) (s : Int) (bs : List Byte)
    (h : fresh[s]? = some bs) : (cache_overlay fresh old)[s]? = some bs := by
  simp [cache_overlay_lookup, h]

theorem vdist_bounds (a b : BitVec 16) : 0 ≤ vdist a b ∧ vdist a b < 65536 := by
  unfold vdist
  omega

theorem vdist_inj (a b c : BitVec 16) (h : vdist a b = vdist a c) : b = c := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  have hc := c.isLt
  simp only [vdist] at h
  change b.toNat < 65536 at hb
  change c.toNat < 65536 at hc
  omega

@[simp] theorem vreq_nsectors_wr (mv : vmem) (r : vio_req) :
    wr_nsectors (vreq_wr mv r) = vreq_nsectors r := by
  unfold vreq_wr vreq_nsectors
  split <;> simp [wr_nsectors]

theorem vreq_nsectors_in (r : vio_req) (h : (r.vr_type.toNat : Int) ≠ virtio_blk_t_out) :
    vreq_nsectors r = 0 := by simp [vreq_nsectors, h]

theorem vreq_key_inj (r : vio_req) (i j : Nat) (h : vreq_key r i = vreq_key r j) : i = j := by
  unfold vreq_key at h
  omega

theorem vreq_sectors_spec (r : vio_req) (s : Int) :
    s ∈ vreq_sectors r ↔ ∃ i, i < vreq_nsectors r ∧ s = vreq_key r i := by
  simp [vreq_sectors, Std.ExtTreeSet.mem_ofList, List.mem_map, eq_comm]

theorem vreq_touch_spec (r : vio_req) (s : Int) :
    s ∈ vreq_touch r ↔ ∃ i, i < vreq_span r ∧ s = vreq_key r i := by
  simp [vreq_touch, Std.ExtTreeSet.mem_ofList, List.mem_map, eq_comm]

theorem vreq_touch_out (r : vio_req) (h : (r.vr_type.toNat : Int) = virtio_blk_t_out) :
    vreq_touch r = vreq_sectors r := by simp [vreq_touch, vreq_sectors, vreq_span, vreq_nsectors, h]

theorem vreq_sectors_in (r : vio_req) (h : (r.vr_type.toNat : Int) ≠ virtio_blk_t_out) :
    vreq_sectors r = ∅ := by simp [vreq_sectors, vreq_nsectors_in r h]

theorem virtio_pop_cfg (v : State) (mv : vmem) : (virtio_pop v mv).v_cfg = v.v_cfg := rfl
theorem virtio_pop_cache (v : State) (mv : vmem) : (virtio_pop v mv).v_cache = v.v_cache := rfl
theorem virtio_pop_taken (v : State) (mv : vmem) : (virtio_pop v mv).v_taken = v.v_taken := rfl
theorem virtio_pop_isr (v : State) (mv : vmem) : (virtio_pop v mv).v_isr = v.v_isr := rfl
theorem virtio_pop_uidx (v : State) (mv : vmem) : (virtio_pop v mv).v_used_idx = v.v_used_idx := rfl
theorem virtio_pop_seen (v : State) (mv : vmem) : (virtio_pop v mv).v_seen = v.v_seen + one16 := rfl
theorem virtio_pop_inflight (v : State) (mv : vmem) :
    (virtio_pop v mv).v_inflight = v.v_inflight.insert (avail_ring_at v.v_cfg mv v.v_seen) := rfl

theorem virtio_pop_step_shape (v : State) (mv : vmem) (v' : State)
    (h : virtio_pop_step v mv = some v') : virtio_pop_ok v mv = true ∧ v' = virtio_pop v mv := by
  unfold virtio_pop_step at h
  split at h <;> simp_all

theorem virtio_pop_step_disk (v : State) (mv : vmem) (v' : State)
    (h : virtio_pop_step v mv = some v') : v'.v_disk = v.v_disk := by
  rw [(virtio_pop_step_shape v mv v' h).2]
  rfl

@[simp] theorem virtio_pop_step_not_live (v : State) (mv : vmem)
    (h : virtio_live v.v_cfg = false) : virtio_pop_step v mv = none := by
  simp [virtio_pop_step, virtio_pop_ok, h]

theorem virtio_serve_live (v : State) (mv : vmem) (i : BitVec 16)
    (h : virtio_serve_ok v mv i = true) : virtio_live v.v_cfg = true := by
  simp only [virtio_serve_ok, Bool.and_eq_true] at h
  exact h.1

theorem virtio_serve_in (v : State) (mv : vmem) (i : BitVec 16)
    (h : virtio_serve_ok v mv i = true) : i ∈ v.v_inflight := by
  simp only [virtio_serve_ok, Bool.and_eq_true] at h
  exact Std.ExtTreeSet.mem_iff_contains.mpr h.2

theorem virtio_complete_ok_in (v : State) (r : vio_req) (i : BitVec 16)
    (h₁ : (r.vr_type.toNat : Int) ≠ virtio_blk_t_out)
    (h₂ : (r.vr_type.toNat : Int) ≠ virtio_blk_t_flush)
    (hd : cache_disjoint (vreq_touch r) v.v_cache = true) : virtio_complete_ok v r i = true := by
  simp [virtio_complete_ok, h₁, h₂, hd]

theorem virtio_complete_ok_read (v : State) (r : vio_req) (i : BitVec 16)
    (h₁ : (r.vr_type.toNat : Int) ≠ virtio_blk_t_out)
    (h₂ : (r.vr_type.toNat : Int) ≠ virtio_blk_t_flush)
    (h : virtio_complete_ok v r i = true) :
    virtio_wce v.v_cfg = true ∨ cache_disjoint (vreq_touch r) v.v_cache = true := by
  simpa [virtio_complete_ok, h₁, h₂] using h

theorem virtio_complete_ok_out (v : State) (r : vio_req) (i : BitVec 16)
    (h₁ : (r.vr_type.toNat : Int) = virtio_blk_t_out)
    (h : virtio_complete_ok v r i = true) :
    v.v_taken = some i ∧ (virtio_wce v.v_cfg = true ∨ cache_disjoint (vreq_touch r) v.v_cache = true) := by
  simpa [virtio_complete_ok, h₁] using h

theorem virtio_complete_ok_flush (v : State) (r : vio_req) (i : BitVec 16)
    (h₁ : (r.vr_type.toNat : Int) ≠ virtio_blk_t_out)
    (h₂ : (r.vr_type.toNat : Int) = virtio_blk_t_flush)
    (h : virtio_complete_ok v r i = true) : v.v_cache = ∅ := by
  unfold virtio_complete_ok at h
  rw [if_neg h₁, if_pos h₂] at h
  exact Std.ExtTreeMap.isEmpty_iff.mp h

theorem virtio_req_step_shape (v : State) (mv : vmem) (i : BitVec 16) (v' : State) (w : ByteMap)
    (h : virtio_req_step v mv i = some (v', w)) :
    ∃ r, req_from v.v_cfg mv i = some r ∧ virtio_serve_ok v mv i = true ∧
      virtio_complete_ok v r i = true ∧ (v', w) = virtio_complete v mv r i := by
  unfold virtio_req_step at h
  split at h
  · contradiction
  · rename_i hs
    cases hr : req_from v.v_cfg mv i with
    | none => simp [hr] at h
    | some r =>
      simp only [hr] at h
      split at h
      · contradiction
      · rename_i hc
        exact ⟨r, rfl, by simpa using hs, by simpa using hc, (Option.some.inj h).symm⟩

/-- All completion side effects on device state, independent of request type or bus view. -/
theorem virtio_complete_state (v : State) (mv : vmem) (r : vio_req) (i : BitVec 16) :
    (virtio_complete v mv r i).1 = { v with
      v_isr := v.v_isr ||| 1
      v_inflight := v.v_inflight.erase i
      v_used_idx := v.v_used_idx + 1
      v_taken := if v.v_taken = some i then none else v.v_taken } := by
  by_cases ht : (r.vr_type.toNat : Int) = virtio_blk_t_in
  all_goals simp [virtio_complete, ht]

theorem virtio_req_step_cfg (v : State) (mv : vmem) (i : BitVec 16) (v' : State) (w : ByteMap)
    (h : virtio_req_step v mv i = some (v', w)) : v'.v_cfg = v.v_cfg := by
  obtain ⟨r, _, _, _, he⟩ := virtio_req_step_shape v mv i v' w h
  have hs := congrArg Prod.fst he
  rw [virtio_complete_state] at hs
  have hc := congrArg State.v_cfg hs
  exact hc

theorem virtio_req_step_disk_cache (v : State) (mv : vmem) (i : BitVec 16) (v' : State) (w : ByteMap)
    (h : virtio_req_step v mv i = some (v', w)) : v'.v_disk = v.v_disk ∧ v'.v_cache = v.v_cache := by
  obtain ⟨r, _, _, _, he⟩ := virtio_req_step_shape v mv i v' w h
  have hs := congrArg Prod.fst he
  rw [virtio_complete_state] at hs
  have hd := congrArg State.v_disk hs
  have hc := congrArg State.v_cache hs
  exact ⟨hd, hc⟩

@[simp] theorem virtio_req_step_not_live (v : State) (mv : vmem) (i : BitVec 16)
    (h : virtio_live v.v_cfg = false) : virtio_req_step v mv i = none := by
  simp [virtio_req_step, virtio_serve_ok, h]

theorem virtio_capture_step_shape (v : State) (mv : vmem) (i : BitVec 16) (v' : State)
    (h : virtio_capture_step v mv i = some v') :
    ∃ r, req_from v.v_cfg mv i = some r ∧ virtio_serve_ok v mv i = true ∧
      (r.vr_type.toNat : Int) = virtio_blk_t_out ∧ v.v_taken = none ∧
      v' = { v with v_cache := cache_overlay (vreq_cache mv r) v.v_cache, v_taken := some i } := by
  unfold virtio_capture_step at h
  split at h
  · contradiction
  · rename_i hs
    cases hr : req_from v.v_cfg mv i with
    | none => simp [hr] at h
    | some r =>
      simp only [hr] at h
      split at h
      · contradiction
      · rename_i ht
        split at h
        · rename_i htk
          exact ⟨r, rfl, by simpa using hs, by simpa using ht, htk, (Option.some.inj h).symm⟩
        · contradiction

/-- Capturing bytes moves neither durable storage nor interrupt state. -/
theorem virtio_capture_step_disk_isr (v : State) (mv : vmem) (i : BitVec 16) (v' : State)
    (h : virtio_capture_step v mv i = some v') : v'.v_disk = v.v_disk ∧ v'.v_isr = v.v_isr := by
  obtain ⟨_, _, _, _, _, rfl⟩ := virtio_capture_step_shape v mv i v' h
  exact ⟨rfl, rfl⟩

@[simp] theorem virtio_capture_step_not_live (v : State) (mv : vmem) (i : BitVec 16)
    (h : virtio_live v.v_cfg = false) : virtio_capture_step v mv i = none := by
  simp [virtio_capture_step, virtio_serve_ok, h]

theorem virtio_drain_step_shape (v : State) (s : Int) (v' : State)
    (h : virtio_drain_step v s = some v') :
    ∃ bs, v.v_cache[s]? = some bs ∧ v' = { v with
      v_disk := disk_write v.v_disk (virtio_sector_size * s) bs
      v_cache := v.v_cache.erase s } := by
  unfold virtio_drain_step at h
  cases hb : v.v_cache[s]? with
  | none => simp [hb] at h
  | some bs => exact ⟨bs, rfl, (Option.some.inj (by simpa [hb] using h)).symm⟩

theorem virtio_drain_step_isr (v : State) (s : Int) (v' : State)
    (h : virtio_drain_step v s = some v') : v'.v_isr = v.v_isr := by
  obtain ⟨_, _, rfl⟩ := virtio_drain_step_shape v s v' h
  rfl

theorem virtio_drain_step_enabled (v : State) (s : Int) (v' : State)
    (h : virtio_drain_step v s = some v') : ∃ bs, v.v_cache[s]? = some bs := by
  obtain ⟨bs, hb, _⟩ := virtio_drain_step_shape v s v' h
  exact ⟨bs, hb⟩

@[simp] theorem virtio_drain_step_none (v : State) (s : Int)
    (h : v.v_cache[s]? = none) : virtio_drain_step v s = none := by simp [virtio_drain_step, h]

@[simp] theorem virtio_drain_step_empty (v : State) (s : Int)
    (h : v.v_cache = ∅) : virtio_drain_step v s = none := by simp [virtio_drain_step, h]

/-- Malformed chains are distinguished from idle devices for the machine's wild rule. -/
theorem virtio_stalled_pos (v : State) (mv : vmem) (h : virtio_stalled v mv = true) :
    ∃ i, virtio_serve_ok v mv i = true ∧ virtio_chain_ok v.v_cfg mv i = false := by
  simp only [virtio_stalled, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨hl, i, hm, hc⟩ := h
  exact ⟨i, by simp [virtio_serve_ok, hl, Std.ExtTreeSet.contains_iff_mem,
    Std.ExtTreeSet.mem_toList.mp hm], by simpa using hc⟩

@[simp] theorem virtio_not_live_not_stalled (v : State) (mv : vmem)
    (h : virtio_live v.v_cfg = false) : virtio_stalled v mv = false := by
  simp [virtio_stalled, h]

/-- The malformed-chain signal never becomes a silently successful request/capture. -/
theorem virtio_chain_bad_no_step (v : State) (mv : vmem) (i : BitVec 16)
    (hc : virtio_chain_ok v.v_cfg mv i = false) :
    virtio_req_step v mv i = none ∧ virtio_capture_step v mv i = none := by
  unfold virtio_chain_ok at hc
  cases hh : chain_from v.v_cfg mv i with
  | some ds => simp [hh] at hc
  | none =>
    simp [virtio_req_step, virtio_capture_step, req_from, hh]

theorem virtio_stalled_pending (v : State) (mv : vmem) (h : virtio_stalled v mv = true) :
    virtio_pending v mv = true := by
  obtain ⟨i, hs, _⟩ := virtio_stalled_pos v mv h
  have hl := virtio_serve_live v mv i hs
  have hm := virtio_serve_in v mv i hs
  have hn : v.v_inflight ≠ ∅ := by
    intro he
    simp [he] at hm
  simp [virtio_pending, hl, Std.ExtTreeSet.isEmpty_eq_false_iff.mpr hn]

theorem virtio_req_step_seen (v : State) (mv : vmem) (i : BitVec 16) (v' : State) (w : ByteMap)
    (h : virtio_req_step v mv i = some (v', w)) : v'.v_seen = v.v_seen := by
  obtain ⟨r, _, _, _, he⟩ := virtio_req_step_shape v mv i v' w h
  have hs := congrArg Prod.fst he
  rw [virtio_complete_state] at hs
  have hp := congrArg State.v_seen hs
  exact hp

theorem virtio_req_step_inflight (v : State) (mv : vmem) (i : BitVec 16) (v' : State) (w : ByteMap)
    (h : virtio_req_step v mv i = some (v', w)) : v'.v_inflight = v.v_inflight.erase i := by
  obtain ⟨r, _, _, _, he⟩ := virtio_req_step_shape v mv i v' w h
  have hs := congrArg Prod.fst he
  rw [virtio_complete_state] at hs
  have hp := congrArg State.v_inflight hs
  exact hp

theorem virtio_req_step_isr (v : State) (mv : vmem) (i : BitVec 16) (v' : State) (w : ByteMap)
    (h : virtio_req_step v mv i = some (v', w)) : v'.v_isr = v.v_isr ||| 1 := by
  obtain ⟨r, _, _, _, he⟩ := virtio_req_step_shape v mv i v' w h
  have hs := congrArg Prod.fst he
  rw [virtio_complete_state] at hs
  have hp := congrArg State.v_isr hs
  exact hp

theorem virtio_capture_step_cfg (v : State) (mv : vmem) (i : BitVec 16) (v' : State)
    (h : virtio_capture_step v mv i = some v') : v'.v_cfg = v.v_cfg := by
  obtain ⟨_, _, _, _, _, rfl⟩ := virtio_capture_step_shape v mv i v' h
  rfl

theorem virtio_drain_step_cfg (v : State) (s : Int) (v' : State)
    (h : virtio_drain_step v s = some v') : v'.v_cfg = v.v_cfg := by
  obtain ⟨_, _, rfl⟩ := virtio_drain_step_shape v s v' h
  rfl

/-- A power cut following a successful drain keeps that drain's new durable image. -/
theorem virtio_reset_after_drain (v : State) (s : Int) (v' : State)
    (h : virtio_drain_step v s = some v') :
    ∃ bs, v.v_cache[s]? = some bs ∧
      (virtio_reset v').v_disk = disk_write v.v_disk (virtio_sector_size * s) bs ∧
      (virtio_reset v').v_cache = ∅ := by
  obtain ⟨bs, hb, rfl⟩ := virtio_drain_step_shape v s v' h
  exact ⟨bs, hb, rfl, rfl⟩

/-- Only the completing descriptor head may release a previously captured request. -/
theorem virtio_complete_other_latch (v : State) (mv : vmem) (r : vio_req) (i j : BitVec 16)
    (ht : v.v_taken = some j) (hne : i ≠ j) : (virtio_complete v mv r i).1.v_taken = some j := by
  rw [virtio_complete_state]
  simp [ht, Ne.symm hne]

theorem vreq_used_len_writable (r : vio_req) (h : r.vr_wr = true) :
    vreq_used_len r = r.vr_len + 1 := by simp [vreq_used_len, h]

theorem vreq_used_len_readonly (r : vio_req) (h : r.vr_wr = false) :
    vreq_used_len r = 1 := by simp [vreq_used_len, h]

/-- Concrete witness that a missing bus byte is not fixed to a default value. -/
theorem empty_memory_has_distinct_views (a : Address) :
    ∃ mv₀ mv₁ : vmem, mem_view MachCSL.Memory.empty mv₀ ∧
      mem_view MachCSL.Memory.empty mv₁ ∧ view_bytes mv₀ a 1 ≠ view_bytes mv₁ a 1 := by
  refine ⟨fun _ => 0#8, fun _ => 1#8, mem_view_empty _, mem_view_empty _, ?_⟩
  simp [view_bytes]

/-- An uncached request span observes the durable image, including a partial final sector. -/
theorem cache_view_read (v : State) (r : vio_req)
    (hd : cache_disjoint (vreq_touch r) v.v_cache = true) :
    disk_read (cache_view v) ((r.vr_sector.toNat : Int) * virtio_sector_size) r.vr_len.toNat =
      disk_read v.v_disk ((r.vr_sector.toNat : Int) * virtio_sector_size) r.vr_len.toNat := by
  apply List.map_congr_left
  intro j hj
  apply cache_view_miss
  apply (cache_disjoint_spec _ _).mp hd
  apply (vreq_touch_spec r _).mpr
  refine ⟨j / virtio_sector_bytes, sector_count_lt _ _ (List.mem_range.mp hj), ?_⟩
  simp only [vreq_key, virtio_sector_size, virtio_sector_bytes]
  omega


end MachCSL.Devices.Virtio
