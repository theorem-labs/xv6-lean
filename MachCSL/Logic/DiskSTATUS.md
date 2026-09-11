# Disk-image ownership

All definitions, timeless instances and lemmas in the 443-line paper-pinned
`iris/DiskImg.v` are implemented by this layer, using native Iris ownership.
The source pin is `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
This is the disk-image resource component; it does not claim the source's
subsequent disk-driver lifting, crash invariant, filesystem or adequacy proofs.

| Source `DiskImg.v` | Lean |
| --- | --- |
| `diskImgG`, `diskImgΣ`, `subG_diskImgG` (40–47) | `Capacity.image`, `ImageRA`/`ImageRF`, `imageFunctor`, explicit `imageSlot`/`registryCapacity` |
| `disk_img_auth` (56) | `imageAuth`, with native `mapAuth` |
| `disk_img_byte`, `disk_img_bytes` (91–95) | `imageByte`, `imageBytes` |
| byte/range timeless (97–102) | `imageByte_timeless`, `imageBytes_timeless` |
| `disk_read_cons` (72) | `diskRead_cons` |
| `disk_img_bytes_cons` (106) | `imageBytes_cons` |
| `disk_img_bytes_read` (120) | `imageBytes_read` |
| `disk_img_bytes_update_gen` (153) | `imageBytes_update_gen` |
| `disk_img_bytes_update` (200) | `imageBytes_update`, pure helper `diskView_write_of_range` |
| `disk_img_bytes_mint` (236) | `imageBytes_mint` |
| `disk_img_bytes_mint_dom` (275) | `imageBytes_mint_dom` |
| `disk_img_alloc` (328) | `imageAuth_alloc` |
| `disk_img_auth_sized`, timeless (355–363) | `imageAuthSized`, `imageAuthSized_timeless` |
| `disk_read_length` (365) | existing `Devices.Virtio.disk_read_length`, included as `DiskSpec.readLength` |
| `disk_read_lookup`, `disk_read_agree` (369–387) | `diskRead_lookup`, `diskRead_agree` |
| `disk_img_sized_alloc/read/write` (389–441) | `imageAuthSized_alloc/read/write` |

The carrier remains the actual total machine disk, `Int → BitVec 8`.
The authority's finite map is the extensional `ExtTreeMap Int Byte`; the
relation to that total function is exactly the existing
`Devices.Virtio.disk_view`. No zero default, unsigned-offset restriction,
sector alignment, nonempty-range premise or physical disk-size assumption
is added. Range ownership uses native indexed `BigSepL` at
`offset + Int.ofNat index`.

`imageBytes_update_gen` requires equal old and new list lengths. Its result
contains the new authority and full new fragments, every new list lookup at
the corresponding map offset, and equality of old/new map lookups at every
offset outside the range. The proof updates one full byte fragment at a time,
retaining the other fragments as Iris frames. `imageBytes_update` derives a
view of the machine's actual `disk_write` for every compatible old total disk.

Minting requires every selected offset to be absent. `imageBytes_mint_dom`
retains even the source's redundant old-map-to-`True` premise and reports that
each output binding either already existed with the same value or lies in
the new signed interval. `imageBytes_mint` follows by discarding that domain
report. Both allocation rules allocate a fresh native ghost-map name and mint
exactly the current disk bytes over `[0,n)`.

The sized authority bounds every minted key to `[0,n)`. Given that authority
and the **whole** `[0,n)` fragment, `imageAuthSized_write` can move ownership
to an arbitrary target total disk. The proof first establishes that the map's
domain did not grow outside the interval, then reconstructs its view from all
new range lookups. It imposes no equality on either total function outside the
minted interval, including when `n = 0`. This is the strength of the source
rule, and the whole-range ownership premise remains explicit.

`DiskSpec.lean` imports only definitions and independently states the complete
source contract. `diskSpec` proves it for an explicit capacity;
`DiskLink.lean` provides `registryDiskSpec` and re-establishes the previous
proved power-ghost contract in the extended registry. Slot 12 is the unique
disk-image camera. Slots 0–11 and all later slots are preserved by explicit
registry equalities. Per-era and fixed durable resources use this same
capacity with explicit runtime ghost names; this component does not invent
or equate those names. A full era/state allocation must allocate them as
required by its separate contract.

Validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.DiskLink
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/DiskAudit.lean
```

The 379-job build passes. The proof module takes about 1.2 seconds, and the
link about 0.8 seconds. The independent all-declaration transitive audit
checks 138 public and private disk-namespace declarations, rejecting all
axioms except `propext`, `Classical.choice` and `Quot.sound`; its output is
`/tmp/xv6-lean-research/disk-axioms.log`. No `sorry`, custom axiom,
`native_decide` or `bv_decide` is used.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
