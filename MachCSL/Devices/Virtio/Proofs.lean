import MachCSL.Devices.Virtio.Defs

/-!
Kernel-checked state/MMIO and sector laws for the pinned Virtio model.
Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.
-/
namespace MachCSL.Devices.Virtio

@[simp] theorem virtio_reset_not_live (v : State) :
    virtio_live (virtio_reset v).v_cfg = false := rfl
@[simp] theorem virtio_reset_seen (v : State) : (virtio_reset v).v_seen = zero16 := rfl
@[simp] theorem virtio_reset_used_idx (v : State) :
    (virtio_reset v).v_used_idx = zero16 := rfl
@[simp] theorem virtio_reset_cache (v : State) : (virtio_reset v).v_cache = ∅ := rfl
@[simp] theorem virtio_reset_inflight (v : State) : (virtio_reset v).v_inflight = ∅ := rfl
@[simp] theorem virtio_reset_taken (v : State) : (virtio_reset v).v_taken = none := rfl
@[simp] theorem virtio_reset_wce (v : State) :
    virtio_wce (virtio_reset v).v_cfg = false := by simp [virtio_wce, virtio_reset, virtio_cfg0, BitVec.getLsbD]
@[simp] theorem virtio_reset_disk (v : State) : (virtio_reset v).v_disk = v.v_disk := rfl
@[simp] theorem virtio_reset_cap (v : State) : (virtio_reset v).v_cap = v.v_cap := rfl
@[simp] theorem virtio_reset_idempotent (v : State) :
    virtio_reset (virtio_reset v) = virtio_reset v := rfl
@[simp] theorem virtio_reset_irq (v : State) : virtio_irq (virtio_reset v) = false := rfl
@[simp] theorem virtio_isr_ok_reset (v : State) : virtio_isr_ok (virtio_reset v) := by change (0#32 &&& 3#32) = 0#32; decide
@[simp] theorem virtio_init_cfg_live (pd pav pu : Address) :
    virtio_live (virtio_init_cfg pd pav pu) = true := by
  change virtio_live (virtio_init_cfg 0 0 0) = true
  decide +kernel
@[simp] theorem virtio_init_cfg_wce (pd pav pu : Address) :
    virtio_wce (virtio_init_cfg pd pav pu) = false := by simp [virtio_wce, virtio_init_cfg, BitVec.getLsbD]

theorem set_lo_hi_id (a : Address) : set_hi (set_lo zero64 (lo32 a)) (hi32 a) = a := by
  have hm (j : Nat) : (4294967295#64).getLsbD j = decide (j < 32) := by
    change Nat.testBit (2 ^ 32 - 1) j = decide (j < 32)
    exact Nat.testBit_two_pow_sub_one 32 j
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlo : i < 32
  · simp [set_hi, set_lo, zero64, lo32, hi32, hm, hi, hlo]
  · have hs : i - 32 < 32 := by omega
    have hadd : 32 + (i - 32) = i := by omega
    simp [set_hi, set_lo, zero64, lo32, hi32, hi, hlo, hs, hadd]


theorem set_lo_low (a : Address) (w : BitVec 32) : lo32 (set_lo a w) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [lo32, set_lo, BitVec.zeroExtend, hi, show i < 64 by omega]

theorem set_lo_high (a : Address) (w : BitVec 32) : hi32 (set_lo a w) = hi32 a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi32, set_lo, BitVec.zeroExtend, hi, show 32 + i < 64 by omega]

theorem set_hi_low (a : Address) (w : BitVec 32) : lo32 (set_hi a w) = lo32 a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : (0xffffffff#64).getLsbD i = true := by
    change ((BitVec.allOnes 32).zeroExtend 64).getLsbD i = _
    simp only [BitVec.zeroExtend, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
    simp [hi, show i < 64 by omega]
  simpa [lo32, set_hi, BitVec.zeroExtend, hi, show i < 64 by omega] using
    congrArg (fun b => a.getLsbD i && b) hm


theorem set_hi_high (a : Address) (w : BitVec 32) : hi32 (set_hi a w) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : (0xffffffff#64).getLsbD (32 + i) = false := by
    change ((BitVec.allOnes 32).zeroExtend 64).getLsbD (32 + i) = _
    simp only [BitVec.zeroExtend, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
    simp
  simpa [hi32, set_hi, BitVec.zeroExtend, hi, show 32 + i < 64 by omega, show ¬32 + i < 32 by omega] using
    congrArg (fun b => (a.getLsbD (32+i) && b) || w.getLsbD i) hm


/-- Successful MMIO writes, including reset, preserve the durable medium and capacity. -/
theorem virtio_write_durable (v : State) (off : Int) (w : BitVec 32) (v' : State)
    (h : virtio_write v off w = some v') : v'.v_disk = v.v_disk ∧ v'.v_cap = v.v_cap := by
  simp only [virtio_write] at h
  by_cases hc : off = vio_off_status
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_device_features_sel
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_driver_features_sel
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_driver_features
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_queue_sel
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_shm_sel
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_queue_num
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_queue_ready
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_queue_notify
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_interrupt_ack
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_queue_desc_low
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_queue_desc_high
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_driver_desc_low
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_driver_desc_high
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_device_desc_low
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  by_cases hc : off = vio_off_device_desc_high
  · rw [if_pos hc] at h
    repeat' split at h
    all_goals first | (cases Option.some.inj h; exact ⟨rfl, rfl⟩) | contradiction
  rw [if_neg hc] at h
  contradiction

theorem virtio_write_disk (v : State) (off : Int) (w : BitVec 32) (v' : State)
    (h : virtio_write v off w = some v') : v'.v_disk = v.v_disk :=
  (virtio_write_durable v off w v' h).1

theorem virtio_write_cap (v : State) (off : Int) (w : BitVec 32) (v' : State)
    (h : virtio_write v off w = some v') : v'.v_cap = v.v_cap :=
  (virtio_write_durable v off w v' h).2

@[simp] theorem virtio_write_notify (v : State) (w : BitVec 32) :
    virtio_write v vio_off_queue_notify w = some v := by
  simp [virtio_write, vio_off_queue_notify, vio_off_status, vio_off_device_features_sel,
    vio_off_driver_features_sel, vio_off_driver_features, vio_off_queue_sel,
    vio_off_shm_sel, vio_off_queue_num, vio_off_queue_ready]

@[simp] theorem virtio_write_ack (v : State) (w : BitVec 32) :
    virtio_write v vio_off_interrupt_ack w = some { v with v_isr := v.v_isr &&& ~~~w } := by
  simp [virtio_write, vio_off_interrupt_ack, vio_off_queue_notify, vio_off_status,
    vio_off_device_features_sel, vio_off_driver_features_sel, vio_off_driver_features,
    vio_off_queue_sel, vio_off_shm_sel, vio_off_queue_num, vio_off_queue_ready]

@[simp] theorem virtio_write_reset (v : State) :
    virtio_write v vio_off_status 0 = some (virtio_reset v) := by simp [virtio_write]

@[simp] theorem disk_read_length (dk : Disk) (off : Int) (n : Nat) :
    (disk_read dk off n).length = n := by simp [disk_read]

theorem disk_write_in (dk : Disk) (off : Int) (bs : List Byte) (a : Int) (b : Byte)
    (hle : off ≤ a) (hb : bs[(a - off).toNat]? = some b) :
    disk_write dk off bs a = b := by simp [disk_write, hle, hb]

theorem disk_write_out (dk : Disk) (off : Int) (bs : List Byte) (a : Int)
    (h : a < off ∨ off + (bs.length : Int) ≤ a) : disk_write dk off bs a = dk a := by
  unfold disk_write
  split
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rfl

@[simp] theorem disk_write_nil (dk : Disk) (off : Int) : disk_write dk off [] = dk := by
  funext a
  simp [disk_write]

theorem disk_read_write (dk : Disk) (off : Int) (bs : List Byte) :
    disk_read (disk_write dk off bs) off bs.length = bs := by
  apply List.ext_getElem
  · simp [disk_read]
  · intro i h₁ h₂
    simp [disk_read, disk_write, show off ≤ off + (i : Int) by omega,
      show off + (i : Int) - off = i by omega, h₂]

@[simp] theorem wr_apply_none (dk : Disk) : wr_apply none dk = dk := rfl
@[simp] theorem wr_sector_none (i : Nat) : wr_sector none i = none := rfl
@[simp] theorem wr_sector_bytes_none (i : Nat) : wr_sector_bytes none i = [] := rfl

theorem virtio_sector_size_bytes : virtio_sector_size = (virtio_sector_bytes : Int) := rfl

theorem sector_count_cover (n : Nat) : n ≤ virtio_sector_bytes * sector_count n := by
  simp only [sector_count, virtio_sector_bytes]
  omega

theorem sector_of_bounds (d : Nat) :
    virtio_sector_bytes * (d / virtio_sector_bytes) ≤ d ∧
    d < virtio_sector_bytes * (d / virtio_sector_bytes) + virtio_sector_bytes := by
  unfold virtio_sector_bytes
  omega

theorem sector_count_lt (n i : Nat) (h : i < n) :
    i / virtio_sector_bytes < sector_count n := by
  simp only [sector_count, virtio_sector_bytes]
  omega

theorem sector_chunk_len (bs : List Byte) (i : Nat) :
    ((bs.drop (virtio_sector_bytes * i)).take virtio_sector_bytes).length ≤ virtio_sector_bytes ∧
    (virtio_sector_bytes * i +
      ((bs.drop (virtio_sector_bytes * i)).take virtio_sector_bytes).length ≤ bs.length ∨
      ((bs.drop (virtio_sector_bytes * i)).take virtio_sector_bytes).length = 0) := by
  simp only [List.length_take, List.length_drop]
  omega

theorem wr_sector_miss (off : Int) (bs : List Byte) (i : Nat) (a : Int) (dk : Disk)
    (h : a < off + virtio_sector_size * i ∨
      off + virtio_sector_size * ((i : Int) + 1) ≤ a) :
    wr_apply (wr_sector (some (off, bs)) i) dk a = dk a := by
  apply disk_write_out
  have hlen := (sector_chunk_len bs i).1
  simp only [virtio_sector_size, virtio_sector_bytes] at *
  omega

theorem wr_sector_outside (off : Int) (bs : List Byte) (i : Nat) (a : Int) (dk : Disk)
    (h : a < off ∨ off + (bs.length : Int) ≤ a) :
    wr_apply (wr_sector (some (off, bs)) i) dk a = dk a := by
  change disk_write dk _ _ a = dk a
  rcases (sector_chunk_len bs i).2 with hlen | hnil
  · apply disk_write_out
    simp only [virtio_sector_size, virtio_sector_bytes] at *
    omega
  · have he := List.eq_nil_of_length_eq_zero hnil
    rw [he, disk_write_nil]

theorem wr_sector_hit (off : Int) (bs : List Byte) (i : Nat) (a : Int) (dk : Disk)
    (h₁ : off + virtio_sector_size * i ≤ a)
    (h₂ : a < off + virtio_sector_size * ((i : Int) + 1)) :
    wr_apply (wr_sector (some (off, bs)) i) dk a = disk_write dk off bs a := by
  have hidx : (a - off).toNat = virtio_sector_bytes * i +
      (a - (off + virtio_sector_size * i)).toNat := by
    simp only [virtio_sector_bytes, virtio_sector_size] at *
    omega
  have hj : (a - (off + virtio_sector_size * i)).toNat < virtio_sector_bytes := by
    simp only [virtio_sector_bytes, virtio_sector_size] at *
    omega
  have hbase : off ≤ a := by simp only [virtio_sector_size] at *; omega
  simp only [wr_apply, wr_sector, disk_write, if_pos h₁, if_pos hbase,
    List.getElem?_take_of_lt hj, List.getElem?_drop, hidx]

theorem wr_sector_write (off : Int) (bs : List Byte) (i : Nat) (dk : Disk) :
    disk_write dk (off + virtio_sector_size * i) (wr_sector_bytes (some (off, bs)) i) =
      wr_apply (wr_sector (some (off, bs)) i) dk := rfl

theorem cache_view_miss (v : State) (a : Int)
    (h : v.v_cache[a / virtio_sector_size]? = none) : cache_view v a = v.v_disk a := by
  simp [cache_view, h]

theorem cache_view_empty (v : State) (h : v.v_cache = ∅) : cache_view v = v.v_disk := by
  funext a
  apply cache_view_miss
  simp [h]

/-- Finite-map correspondence is extensional equality of lookup results. -/
theorem cache_ext (a b : Cache) (h : ∀ k : Int, a[k]? = b[k]?) : a = b :=
  Std.ExtTreeMap.ext_getElem? h

/-- Every stored cache byte-list is witnessed in a finite enumeration. -/
theorem cache_lookup_finite (m : Cache) (k : Int) (bs : List Byte) :
    m[k]? = some bs ↔ (k, bs) ∈ m.toList := by
  exact Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.symm

theorem inflight_finite (s : Inflight) (h : BitVec 16) :
    h ∈ s ↔ h ∈ s.toList := Std.ExtTreeSet.mem_toList.symm

theorem disk_write_congr_at (dk dk' : Disk) (off : Int) (bs : List Byte) (a : Int)
    (h : dk a = dk' a) : disk_write dk off bs a = disk_write dk' off bs a := by
  simp only [disk_write, h]

theorem disk_write_idempotent (dk : Disk) (off : Int) (bs : List Byte) :
    disk_write (disk_write dk off bs) off bs = disk_write dk off bs := by
  funext a
  unfold disk_write
  split
  · cases bs[(a - off).toNat]? <;> rfl
  · rfl

theorem wr_sector_congr_at (w : disk_wr) (i : Nat) (dk dk' : Disk) (a : Int)
    (h : dk a = dk' a) :
    wr_apply (wr_sector w i) dk a = wr_apply (wr_sector w i) dk' a := by
  cases w with
  | none => exact h
  | some ob => exact disk_write_congr_at dk dk' _ _ a h

/-- A sector transforms only its own interval, including a short final sector. -/
theorem wr_sector_eq_at (off : Int) (bs : List Byte) (i : Nat) (dk : Disk) (a : Int) :
    wr_apply (wr_sector (some (off, bs)) i) dk a =
      if off + virtio_sector_size * i ≤ a ∧
        a < off + virtio_sector_size * ((i : Int) + 1)
      then disk_write dk off bs a else dk a := by
  split
  · rename_i h
    exact wr_sector_hit off bs i a dk h.1 h.2
  · rename_i h
    apply wr_sector_miss
    omega

/-- Landing two sectors of one request commutes (also valid for repeated sectors). -/
theorem wr_sector_comm (w : disk_wr) (i j : Nat) (dk : Disk) :
    wr_apply (wr_sector w i) (wr_apply (wr_sector w j) dk) =
      wr_apply (wr_sector w j) (wr_apply (wr_sector w i) dk) := by
  cases w with
  | none => rfl
  | some ob =>
    obtain ⟨off, bs⟩ := ob
    by_cases he : i = j
    · subst j; rfl
    funext a
    by_cases hi : off + virtio_sector_size * i ≤ a ∧
        a < off + virtio_sector_size * ((i : Int) + 1)
    · have hj : a < off + virtio_sector_size * j ∨
          off + virtio_sector_size * ((j : Int) + 1) ≤ a := by
        simp only [virtio_sector_size] at *
        omega
      rw [wr_sector_miss off bs j a _ hj]
      exact wr_sector_congr_at _ i _ _ a (wr_sector_miss off bs j a _ hj)
    · have hi' : a < off + virtio_sector_size * i ∨
          off + virtio_sector_size * ((i : Int) + 1) ≤ a := by omega
      rw [wr_sector_miss off bs i a _ hi']
      exact (wr_sector_congr_at _ j _ _ a (wr_sector_miss off bs i a _ hi')).symm

/-- A whole write absorbs any further sector of the same payload. -/
theorem wr_sector_absorb (off : Int) (bs : List Byte) (i : Nat) (dk : Disk) :
    wr_apply (wr_sector (some (off, bs)) i) (disk_write dk off bs) =
      disk_write dk off bs := by
  funext a
  rw [wr_sector_eq_at]
  split <;> simp [disk_write_idempotent]

theorem wr_fold_outside (off : Int) (bs : List Byte) (is : List Nat) (dk : Disk) (a : Int)
    (h : a < off ∨ off + (bs.length : Int) ≤ a) :
    wr_fold (some (off, bs)) is dk a = dk a := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change wr_apply (wr_sector (some (off, bs)) i) (wr_fold (some (off, bs)) is dk) a = dk a
    rw [wr_sector_outside off bs i a _ h, ih]

theorem wr_fold_hit (off : Int) (bs : List Byte) (is : List Nat) (dk : Disk) (a : Int)
    (i : Nat) (hm : i ∈ is)
    (h₁ : off + virtio_sector_size * i ≤ a)
    (h₂ : a < off + virtio_sector_size * ((i : Int) + 1)) :
    wr_fold (some (off, bs)) is dk a = disk_write dk off bs a := by
  induction is with
  | nil => simp at hm
  | cons j is ih =>
    change wr_apply (wr_sector (some (off, bs)) j) (wr_fold (some (off, bs)) is dk) a = _
    rcases List.mem_cons.mp hm with he | hm
    · subst j
      rw [wr_sector_hit off bs i a _ h₁ h₂]
      unfold disk_write
      split
      · cases he : bs[(a - off).toNat]? with
        | some b => rfl
        | none =>
          have hlen := List.getElem?_eq_none_iff.mp he
          have hout : a < off ∨ off + (bs.length : Int) ≤ a := by omega
          exact wr_fold_outside off bs is dk a hout
      · exact wr_fold_outside off bs is dk a (by omega)
    · calc
        _ = wr_apply (wr_sector (some (off, bs)) j) (disk_write dk off bs) a :=
          wr_sector_congr_at _ j _ _ a (ih hm)
        _ = _ := congrFun (wr_sector_absorb off bs j dk) a

/-- Coverage alone suffices: order, duplicates and extra out-of-range sectors are unrestricted. -/
theorem wr_fold_all (w : disk_wr) (is : List Nat) (dk : Disk)
    (hcover : ∀ i, i < wr_nsectors w → i ∈ is) : wr_fold w is dk = wr_apply w dk := by
  cases w with
  | none =>
    clear hcover
    induction is <;> simp_all [wr_fold, wr_apply, wr_sector]
  | some ob =>
    obtain ⟨off, bs⟩ := ob
    funext a
    by_cases hin : off ≤ a ∧ a < off + (bs.length : Int)
    · let i := (a - off).toNat / virtio_sector_bytes
      have hm : i ∈ is := hcover i (sector_count_lt bs.length (a - off).toNat (by omega))
      have hb := sector_of_bounds (a - off).toNat
      apply wr_fold_hit off bs is dk a i hm
      all_goals dsimp [i] at *; simp only [virtio_sector_bytes, virtio_sector_size] at *; omega
    · have hout : a < off ∨ off + (bs.length : Int) ≤ a := by omega
      rw [wr_fold_outside off bs is dk a hout]
      exact (disk_write_out dk off bs a hout).symm

end MachCSL.Devices.Virtio
