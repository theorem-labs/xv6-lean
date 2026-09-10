import MachCSL.Devices.Virtio.Defs
import MachCSL.Memory.Bytes

/-!
Operational DMA model from `iris/VirtioModel.v` at xv6iris arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476` (§3 DMA primitives and §4–6b).
Missing partial-map bytes remain unconstrained in a total bus view. A malformed
in-flight chain is reported by `virtio_stalled`; the machine caller must retain
the source's wild-write transition for that case.

Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.
-/
namespace MachCSL.Devices.Virtio

abbrev ByteMap := MachCSL.Memory.ByteMap 64
abbrev vmem := Address → Byte
abbrev Sectors := Std.ExtTreeSet Int

def read_byte_list (mm : ByteMap) (pa : Address) (n : Nat) : Option (List Byte) :=
  (List.range n).mapM (fun j => mm (MachCSL.Memory.addressAdd pa j))

/-- The right fold preserves the source's first-byte precedence even after address wrap. -/
def write_byte_list (mm : ByteMap) (pa : Address) (bs : List Byte) : ByteMap :=
  bs.zipIdx.foldr (fun (b, j) acc =>
    MachCSL.Memory.insert acc (MachCSL.Memory.addressAdd pa j) b) mm

def pa_off (a : Address) (z : Int) : Address := MachCSL.Memory.addressAdd a z.toNat

/-- Source `RiscvModelBytes.assemble_bytes`: unsigned little-endian assembly. -/
def assemble_bytes : List Byte → Int
  | [] => 0
  | b :: bs => (b.toNat : Int) + 2 ^ 8 * assemble_bytes bs

def read_bytes (mm : ByteMap) (pa : Address) (n : Nat) : Option (BitVec (8 * n)) :=
  (read_byte_list mm pa n).map (fun bs => BitVec.ofInt (8 * n) (assemble_bytes bs))

def mem_view (m : ByteMap) (mv : vmem) : Prop :=
  ∀ a b, m a = some b → mv a = b

def view_bytes (mv : vmem) (a : Address) (n : Nat) : List Byte :=
  (List.range n).map (fun j => mv (MachCSL.Memory.addressAdd a j))

def view_word (mv : vmem) (a : Address) (n : Nat) : BitVec (8 * n) :=
  BitVec.ofInt (8 * n) (assemble_bytes (view_bytes mv a n))

structure vq_desc where
  vd_addr : Address
  vd_len : BitVec 32
  vd_flags : BitVec 16
  vd_next : BitVec 16
  deriving DecidableEq

def vd_has (d : vq_desc) (flag : Int) : Bool :=
  FromMathlib.Int.land d.vd_flags.toNat flag == flag

def desc_at (c : Cfg) (mv : vmem) (i : Int) : vq_desc :=
  let base := pa_off c.vc_desc (vq_desc_size * i)
  ⟨view_word mv base 8, view_word mv (pa_off base 8) 4,
    view_word mv (pa_off base 12) 2, view_word mv (pa_off base 14) 2⟩

def avail_idx_at (c : Cfg) (mv : vmem) : BitVec 16 :=
  view_word mv (pa_off c.vc_avail vq_idx_off) 2

def avail_ring_at (c : Cfg) (mv : vmem) (i : BitVec 16) : BitVec 16 :=
  view_word mv (pa_off c.vc_avail
    (vq_avail_ring_off + 2 * ((i.toNat : Int) % (c.vc_qnum.toNat : Int)))) 2

/-- Exactly three descriptors. Direction flags and status length are intentionally not gates. -/
def chain_from (c : Cfg) (mv : vmem) (h : BitVec 16) :
    Option (BitVec 16 × vq_desc × vq_desc × vq_desc) :=
  let qnum := c.vc_qnum.toNat
  if !(decide (h.toNat < qnum)) then none else
  let d0 := desc_at c mv h.toNat
  if !(vd_has d0 vring_desc_f_next) then none else
  if !(decide (d0.vd_next.toNat < qnum)) then none else
  let d1 := desc_at c mv d0.vd_next.toNat
  if !(vd_has d1 vring_desc_f_next) then none else
  if !(decide (d1.vd_next.toNat < qnum)) then none else
  let d2 := desc_at c mv d1.vd_next.toNat
  if vd_has d2 vring_desc_f_next then none else
  some (h, d0, d1, d2)

def virtio_chain_ok (c : Cfg) (mv : vmem) (h : BitVec 16) : Bool :=
  (chain_from c mv h).isSome

structure vio_req where
  vr_head : BitVec 16
  vr_type : BitVec 32
  vr_sector : BitVec 64
  vr_buf : Address
  vr_len : BitVec 32
  vr_status : Address
  vr_wr : Bool
  deriving DecidableEq

def req_from (c : Cfg) (mv : vmem) (h : BitVec 16) : Option vio_req :=
  match chain_from c mv h with
  | none => none
  | some (h, d0, d1, d2) =>
    some ⟨h, view_word mv d0.vd_addr 4, view_word mv (pa_off d0.vd_addr 8) 8,
      d1.vd_addr, d1.vd_len, d2.vd_addr, vd_has d1 vring_desc_f_write⟩

def one16 : BitVec 16 := 1

def vdist (a b : BitVec 16) : Int := ((b.toNat : Int) - (a.toNat : Int)) % 65536

def vpos_pub (lo ai p : BitVec 16) : Bool := decide (vdist lo p < vdist lo ai)

/-- The writable-descriptor flag determines used length, even for unknown types. -/
def vreq_used_len (r : vio_req) : BitVec 32 :=
  if r.vr_wr then r.vr_len + 1 else 1

def virtio_used_writes (c : Cfg) (ui : BitVec 16) (r : vio_req) : ByteMap :=
  let qnum : Int := c.vc_qnum.toNat
  let slot := (ui.toNat : Int) % qnum
  let elem := pa_off c.vc_used (vq_used_ring_off + vq_used_elem_size * slot)
  let m1 := MachCSL.Memory.writeBytes MachCSL.Memory.empty elem 4 (r.vr_head.zeroExtend 32)
  let m2 := MachCSL.Memory.writeBytes m1 (pa_off elem 4) 4 (vreq_used_len r)
  MachCSL.Memory.writeBytes m2 (pa_off c.vc_used vq_idx_off) 2 (ui + 1)

def vreq_wr (mv : vmem) (r : vio_req) : disk_wr :=
  if (r.vr_type.toNat : Int) = virtio_blk_t_out then
    some ((r.vr_sector.toNat : Int) * virtio_sector_size, view_bytes mv r.vr_buf r.vr_len.toNat)
  else none

def vreq_nsectors (r : vio_req) : Nat :=
  if (r.vr_type.toNat : Int) = virtio_blk_t_out then sector_count r.vr_len.toNat else 0

def vreq_key (r : vio_req) (i : Nat) : Int := (r.vr_sector.toNat : Int) + i

/-- stdpp list_to_map gives the first duplicate precedence, hence a right fold. -/
def vreq_cache_of (mv : vmem) (r : vio_req) (is : List Nat) : Cache :=
  is.foldr (fun i acc => acc.insert (vreq_key r i) (wr_sector_bytes (vreq_wr mv r) i)) ∅

def vreq_cache (mv : vmem) (r : vio_req) : Cache :=
  vreq_cache_of mv r (List.range (vreq_nsectors r))

def vreq_sectors (r : vio_req) : Sectors :=
  Std.ExtTreeSet.ofList ((List.range (vreq_nsectors r)).map (vreq_key r))

def vreq_span (r : vio_req) : Nat := sector_count r.vr_len.toNat

def vreq_touch (r : vio_req) : Sectors :=
  Std.ExtTreeSet.ofList ((List.range (vreq_span r)).map (vreq_key r))

/-- Decidable finite-domain disjointness, corresponding to `S ∩ dom cache = ∅`. -/
def cache_disjoint (ss : Sectors) (cache : Cache) : Bool :=
  ss.toList.all (fun s => cache[s]?.isNone)

/-- Explicitly left-biased: a newly captured sector replaces an older cached one. -/
def cache_overlay (fresh old : Cache) : Cache :=
  fresh.mergeWith (fun _ new _ => new) old

/-- Completion updates status/ring/IRQ atomically but never the durable image or cache. -/
def virtio_complete (v : State) (_mv : vmem) (r : vio_req) (i : BitVec 16) : State × ByteMap :=
  let n := r.vr_len.toNat
  let doff := (r.vr_sector.toNat : Int) * virtio_sector_size
  let st := if (r.vr_type.toNat : Int) = virtio_blk_t_in ∨
      (r.vr_type.toNat : Int) = virtio_blk_t_out ∨
      (r.vr_type.toNat : Int) = virtio_blk_t_flush then virtio_blk_s_ok else virtio_blk_s_unsupp
  let ws := MachCSL.Memory.insert (virtio_used_writes v.v_cfg v.v_used_idx r)
    r.vr_status (BitVec.ofInt 8 st)
  let fl := v.v_inflight.erase i
  let tk := if v.v_taken = some i then none else v.v_taken
  let vd := { v with
    v_isr := v.v_isr ||| 1
    v_inflight := fl
    v_used_idx := v.v_used_idx + 1
    v_taken := tk }
  if (r.vr_type.toNat : Int) = virtio_blk_t_in then
    (vd, write_byte_list ws r.vr_buf (disk_read (cache_view v) doff n))
  else (vd, ws)

def virtio_pop_ok (v : State) (mv : vmem) : Bool :=
  virtio_live v.v_cfg && !(v.v_seen == avail_idx_at v.v_cfg mv)

/-- In-flight values are descriptor heads read from the ring, not ring positions. -/
def virtio_pop (v : State) (mv : vmem) : State :=
  { v with
    v_seen := v.v_seen + one16
    v_inflight := v.v_inflight.insert (avail_ring_at v.v_cfg mv v.v_seen) }

def virtio_pop_step (v : State) (mv : vmem) : Option State :=
  if virtio_pop_ok v mv then some (virtio_pop v mv) else none

def virtio_pending (v : State) (mv : vmem) : Bool :=
  virtio_live v.v_cfg && (!(v.v_seen == avail_idx_at v.v_cfg mv) || !v.v_inflight.isEmpty)

def virtio_serve_ok (v : State) (_mv : vmem) (i : BitVec 16) : Bool :=
  virtio_live v.v_cfg && v.v_inflight.contains i

def virtio_complete_ok (v : State) (r : vio_req) (i : BitVec 16) : Bool :=
  if (r.vr_type.toNat : Int) = virtio_blk_t_out then
    (v.v_taken == some i) && (virtio_wce v.v_cfg || cache_disjoint (vreq_touch r) v.v_cache)
  else if (r.vr_type.toNat : Int) = virtio_blk_t_flush then v.v_cache.isEmpty
  else virtio_wce v.v_cfg || cache_disjoint (vreq_touch r) v.v_cache

def virtio_req_step (v : State) (mv : vmem) (i : BitVec 16) : Option (State × ByteMap) :=
  if !(virtio_serve_ok v mv i) then none else
  match req_from v.v_cfg mv i with
  | none => none
  | some r => if !(virtio_complete_ok v r i) then none else some (virtio_complete v mv r i)

def virtio_capture_step (v : State) (mv : vmem) (i : BitVec 16) : Option State :=
  if !(virtio_serve_ok v mv i) then none else
  match req_from v.v_cfg mv i with
  | none => none
  | some r =>
    if (r.vr_type.toNat : Int) ≠ virtio_blk_t_out then none
    else if v.v_taken = none then
      some { v with v_cache := cache_overlay (vreq_cache mv r) v.v_cache, v_taken := some i }
    else none

/-- Any cached sector may drain at any time, without consulting RAM or queue liveness. -/
def virtio_drain_step (v : State) (s : Int) : Option State :=
  match v.v_cache[s]? with
  | none => none
  | some bs => some { v with
      v_disk := disk_write v.v_disk (virtio_sector_size * s) bs,
      v_cache := v.v_cache.erase s }

def virtio_stalled (v : State) (mv : vmem) : Bool :=
  virtio_live v.v_cfg && v.v_inflight.toList.any (fun p => !(virtio_chain_ok v.v_cfg mv p))

end MachCSL.Devices.Virtio
