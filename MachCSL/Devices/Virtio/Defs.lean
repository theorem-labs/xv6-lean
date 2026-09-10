import Std
import Iris.Std.HeapInstances
import Iris.Std.BitOp

/-!
State, MMIO and durable-disk/sector primitives from `iris/VirtioModel.v`,
xv6iris arxiv-v1 `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
Finite maps/sets use Std extensional trees; disk offsets retain signed integers.
This file does not yet implement autonomous DMA transitions.

Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.
-/
namespace MachCSL.Devices.Virtio

abbrev Byte := BitVec 8
abbrev Address := BitVec 64
abbrev Disk := Int → Byte
abbrev DiskMap := Std.ExtTreeMap Int Byte
abbrev Cache := Std.ExtTreeMap Int (List Byte)
abbrev Inflight := Std.ExtTreeSet (BitVec 16)

def virtio_base : Int := 0x10001000
def virtio_size : Int := 0x1000
def virtio_magic_value : Int := 0x74726976
def virtio_version : Int := 2
def virtio_blk_device_id : Int := 2
def virtio_vendor_id : Int := 0x554d4551
def virtio_device_features : Int := FromMathlib.Int.lor (1 <<< 9) (1 <<< 11)
def virtio_device_features_hi : Int := 1
def virtio_queue_num_max : Int := 1024
def vio_off_magic_value : Int := 0x000
def vio_off_version : Int := 0x004
def vio_off_device_id : Int := 0x008
def vio_off_vendor_id : Int := 0x00c
def vio_off_device_features : Int := 0x010
def vio_off_driver_features : Int := 0x020
def vio_off_queue_sel : Int := 0x030
def vio_off_queue_num_max : Int := 0x034
def vio_off_queue_num : Int := 0x038
def vio_off_queue_ready : Int := 0x044
def vio_off_queue_notify : Int := 0x050
def vio_off_interrupt_status : Int := 0x060
def vio_off_interrupt_ack : Int := 0x064
def vio_off_status : Int := 0x070
def vio_off_queue_desc_low : Int := 0x080
def vio_off_queue_desc_high : Int := 0x084
def vio_off_driver_desc_low : Int := 0x090
def vio_off_driver_desc_high : Int := 0x094
def vio_off_device_desc_low : Int := 0x0a0
def vio_off_device_desc_high : Int := 0x0a4
def vio_off_device_features_sel : Int := 0x014
def vio_off_driver_features_sel : Int := 0x024
def vio_off_shm_sel : Int := 0x0ac
def vio_off_shm_len_low : Int := 0x0b0
def vio_off_shm_len_high : Int := 0x0b4
def vio_off_shm_base_low : Int := 0x0b8
def vio_off_shm_base_high : Int := 0x0bc
def vio_off_queue_reset : Int := 0x0c0
def vio_off_config_generation : Int := 0x0fc
def vio_off_config : Int := 0x100
def vio_off_config_capacity_low : Int := 0x100
def vio_off_config_capacity_high : Int := 0x104
def virtio_window_size : Int := 0x200
def vring_desc_f_next : Int := 1
def vring_desc_f_write : Int := 2
def virtio_blk_t_in : Int := 0
def virtio_blk_t_out : Int := 1
def virtio_blk_t_flush : Int := 4
def vio_isr_used_buffer : Int := 1
def vq_desc_size : Int := 16
def vq_avail_ring_off : Int := 4
def vq_used_ring_off : Int := 4
def vq_used_elem_size : Int := 8
def vq_idx_off : Int := 2
def virtio_sector_size : Int := 512
def virtio_blk_s_ok : Int := 0
def virtio_blk_s_unsupp : Int := 2

def vq_size_ok (n : Int) : Bool :=
  decide (0 < n) && decide (n ≤ virtio_queue_num_max) && (FromMathlib.Int.land n (n - 1) == 0)

structure Cfg where
  vc_status : BitVec 32
  vc_dfeat : BitVec 32
  vc_qsel : BitVec 32
  vc_qnum : BitVec 32
  vc_ready : Bool
  vc_desc : Address
  vc_avail : Address
  vc_used : Address
  vc_devfsel : BitVec 32
  vc_dfsel : BitVec 32
  vc_dfeat1 : BitVec 32
  vc_shmsel : BitVec 32
  deriving DecidableEq

structure State where
  v_cfg : Cfg
  v_isr : BitVec 32
  v_seen : BitVec 16
  v_inflight : Inflight
  v_used_idx : BitVec 16
  v_disk : Disk
  v_cache : Cache
  v_taken : Option (BitVec 16)
  v_cap : BitVec 64

abbrev virtio_cfg := Cfg
abbrev virtio_state := State

def set_vcfg (v : State) (c : Cfg) : State := { v with v_cfg := c }
def disk_view (dmap : DiskMap) (dk : Disk) : Prop :=
  ∀ o b, dmap[o]? = some b → dk o = b

def zero32 : BitVec 32 := 0
def zero16 : BitVec 16 := 0
def zero64 : Address := 0

def virtio_driver_ok (c : Cfg) : Bool := c.vc_status.getLsbD 2
def virtio_live (c : Cfg) : Bool :=
  c.vc_ready && virtio_driver_ok c && vq_size_ok c.vc_qnum.toNat

def virtio_wce (c : Cfg) : Bool := c.vc_dfeat.getLsbD 9
def virtio_irq (v : State) : Bool := !(v.v_isr == 0)

def lo32 (a : Address) : BitVec 32 := a.extractLsb' 0 32
def hi32 (a : Address) : BitVec 32 := a.extractLsb' 32 32

def virtio_read (v : State) (off : Int) : Option (BitVec 32) :=
  let c := v.v_cfg
  if off == vio_off_magic_value then some (BitVec.ofInt 32 virtio_magic_value)
  else if off == vio_off_version then some (BitVec.ofInt 32 virtio_version)
  else if off == vio_off_device_id then some (BitVec.ofInt 32 virtio_blk_device_id)
  else if off == vio_off_vendor_id then some (BitVec.ofInt 32 virtio_vendor_id)
  else if off == vio_off_device_features then
    some (BitVec.ofInt 32 (if c.vc_devfsel == 0 then virtio_device_features
      else if c.vc_devfsel == 1 then virtio_device_features_hi else 0))
  else if off == vio_off_queue_num_max then
    some (BitVec.ofInt 32 (if c.vc_qsel == 0 then virtio_queue_num_max else 0))
  else if off == vio_off_queue_ready then
    some (if (c.vc_qsel == 0) && c.vc_ready then 1 else 0)
  else if off == vio_off_interrupt_status then some v.v_isr
  else if off == vio_off_status then some c.vc_status
  else if off == vio_off_queue_reset then some zero32
  else if off == vio_off_shm_len_low || off == vio_off_shm_len_high ||
      off == vio_off_shm_base_low || off == vio_off_shm_base_high then some 0xffffffff
  else if off == vio_off_config_generation then some zero32
  else if off == vio_off_config_capacity_low then some (lo32 v.v_cap)
  else if off == vio_off_config_capacity_high then some (hi32 v.v_cap)
  else if decide (vio_off_config ≤ off) && decide (off < virtio_window_size) &&
      (off % 4 == 0) then some zero32
  else none

/-- Splice a word, preserving the other half of the 64-bit address. -/
def set_lo (a : Address) (w : BitVec 32) : Address :=
  w.zeroExtend 64 ||| ((a >>> 32) <<< 32)

def set_hi (a : Address) (w : BitVec 32) : Address :=
  (a &&& 0xffffffff) ||| (w.zeroExtend 64 <<< 32)

def virtio_cfg0 : Cfg := ⟨0, 0, 0, 0, false, 0, 0, 0, 0, 0, 0, 0⟩

/-- A reset discards volatile queue/cache state and preserves the durable medium. -/
def virtio_reset (v : State) : State :=
  ⟨virtio_cfg0, 0, 0, ∅, 0, v.v_disk, ∅, none, v.v_cap⟩

def virtio_write (v : State) (off : Int) (w : BitVec 32) : Option State :=
  let c := v.v_cfg
  let qsel0 := c.vc_qsel == 0
  if off = vio_off_status then
    if w = 0 then some (virtio_reset v)
    else some (set_vcfg v { c with vc_status := w })
  else if off = vio_off_device_features_sel then
    some (set_vcfg v { c with vc_devfsel := w })
  else if off = vio_off_driver_features_sel then
    some (set_vcfg v { c with vc_dfsel := w })
  else if off = vio_off_driver_features then
    if c.vc_dfsel = 0 then some (set_vcfg v { c with vc_dfeat := w })
    else if c.vc_dfsel = 1 then some (set_vcfg v { c with vc_dfeat1 := w })
    else some v
  else if off = vio_off_queue_sel then some (set_vcfg v { c with vc_qsel := w })
  else if off = vio_off_shm_sel then some (set_vcfg v { c with vc_shmsel := w })
  else if off = vio_off_queue_num then
    if !qsel0 then some v else
    if !(vq_size_ok w.toNat) then none else
    some (set_vcfg v { c with vc_qnum := w })
  else if off = vio_off_queue_ready then
    if !qsel0 then some v else
    some (set_vcfg v { c with vc_ready := !(w == 0) })
  else if off = vio_off_queue_notify then some v
  else if off = vio_off_interrupt_ack then some { v with v_isr := v.v_isr &&& ~~~w }
  else if off = vio_off_queue_desc_low then
    if !qsel0 then some v else some (set_vcfg v { c with vc_desc := set_lo c.vc_desc w })
  else if off = vio_off_queue_desc_high then
    if !qsel0 then some v else some (set_vcfg v { c with vc_desc := set_hi c.vc_desc w })
  else if off = vio_off_driver_desc_low then
    if !qsel0 then some v else some (set_vcfg v { c with vc_avail := set_lo c.vc_avail w })
  else if off = vio_off_driver_desc_high then
    if !qsel0 then some v else some (set_vcfg v { c with vc_avail := set_hi c.vc_avail w })
  else if off = vio_off_device_desc_low then
    if !qsel0 then some v else some (set_vcfg v { c with vc_used := set_lo c.vc_used w })
  else if off = vio_off_device_desc_high then
    if !qsel0 then some v else some (set_vcfg v { c with vc_used := set_hi c.vc_used w })
  else none

def disk_read (dk : Disk) (off : Int) (n : Nat) : List Byte :=
  (List.range n).map (fun j : Nat => dk (off + (j : Int)))

def disk_write (dk : Disk) (off : Int) (bs : List Byte) : Disk :=
  fun a => if off ≤ a then (bs[(a - off).toNat]?).getD (dk a) else dk a

abbrev disk_wr := Option (Int × List Byte)
def wr_apply (w : disk_wr) (dk : Disk) : Disk :=
  match w with
  | none => dk
  | some (off, bs) => disk_write dk off bs

def virtio_sector_bytes : Nat := 512
def sector_count (n : Nat) : Nat :=
  (n + (virtio_sector_bytes - 1)) / virtio_sector_bytes

def wr_nsectors (w : disk_wr) : Nat :=
  match w with
  | none => 0
  | some (_, bs) => sector_count bs.length

def wr_sector (w : disk_wr) (i : Nat) : disk_wr :=
  match w with
  | none => none
  | some (off, bs) => some (off + virtio_sector_size * i,
      (bs.drop (virtio_sector_bytes * i)).take virtio_sector_bytes)

def wr_fold (w : disk_wr) (is : List Nat) (dk : Disk) : Disk :=
  is.foldr (fun i d => wr_apply (wr_sector w i) d) dk

def wr_sector_bytes (w : disk_wr) (i : Nat) : List Byte :=
  match wr_sector w i with
  | some (_, bs) => bs
  | none => []

def cache_view (v : State) : Disk :=
  fun a => match v.v_cache[a / virtio_sector_size]? with
    | some bs => (bs[(a % virtio_sector_size).toNat]?).getD (v.v_disk a)
    | none => v.v_disk a

-- Source §8/9: pure power-on/configuration helpers, not a reboot operation.
def byte_zero : Byte := 0
def virtio_capacity0 : Int := 128
def virtio0_state : State :=
  ⟨virtio_cfg0, 0, 0, ∅, 0, fun _ => byte_zero, ∅, none,
    BitVec.ofInt 64 virtio_capacity0⟩
def set_vcap (v : State) (cap : BitVec 64) : State := { v with v_cap := cap }
def virtio_init_cfg (pd pav pu : Address) : Cfg :=
  ⟨15, 0, 0, 8, true, pd, pav, pu, 0, 0, 0, 0⟩
def virtio_isr_ok (v : State) : Prop := v.v_isr &&& 3 = v.v_isr

end MachCSL.Devices.Virtio
