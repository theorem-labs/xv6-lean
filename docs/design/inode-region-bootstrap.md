# Next native inode-region boundary (source inventory)

Source baseline: arxiv-v1 fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.
Read relevant IcacheBoot 265–303, 306–373, 525–760 and InodeRegion
1295–1418, 1525–1535, 1596–1611, 1955–1978, 2250–2263,
2500–2511, 2632–2705, 2776–2798, 2860–2921, 3239–3261.

The full target is IcacheBoot.ireg_alloc, not an abstract configuration
parameter. Its four pure premises are: 16*nib <= 2^32; nib=icfg_nib;
all supplied bss[bi] have 1024 bytes; and every decoded dss with exact
length/16-record WF/encoding satisfies the six image predicates already
ported. Its eleven resource inputs are:
1. per-region-inum inode-reference link_auth None 0 FrzOff 0;
2. per-inum ireg_lnk_at at N(z), type(D(z));
3. per-inum count half at 0;
4. per-inum freeze-mirror half false;
5. per-inum mono-nat observation authority at 0;
6. per-inum ireg_top_boot (free-node top fragment if type 0, emp otherwise);
7. full logged bytes for every supplied inode-region block;
8. the persistent fs_bytes_at row for the home set;
9. the actual ftop_inv;
10. the boot-shelter token;
11. the escrow registry map authority at empty.
At the same mask E it returns fresh gamma_i and dss, exact decoding facts,
ireg_reg, the SAME boot token, and one ireg_out at each decoded record.
ireg_reg contains inv iregN(ireg_body), the byte row, and ftop_inv; it
is deliberately the pre-seal bundle, distinct from ireg_inv.

The actual region body contains its dinode map authority, every block's
16 byte runs + coupled record list + 16 complete slots, and a covering
escrow registry authority. A slot is not merely a dinode and a link token:
it has the reference/count/freeze/shield/mirror resources, exact pure
transition clauses, disjoint in/marked/pending branches with full or half
registry entries and pending escrow, observation counter/log receipts,
and the filesystem-link column. ftop_inv additionally owns the arm store
and per-transaction parked resources. Several of these concrete cameras
and the logged epoch/byte invariants are not in the port yet. They must be
implemented; replacing them with arbitrary IProp fields would not close
this boundary.

Implemented bounded native subgraph in FsInodeRegion*:
- exact iregG ghost_map(Int,Dinode) camera/capacity (Xv6Cameras485–488),
  full/fractional raw record-map predicates and source full dinode_at;
- existential-valued imark at -(z+1), its exclusivity, and exact ireg_out;
- concrete M0(decoded records) and MK(empty-address marker records), full
  lookup/domain/disjointness laws, all native map-to-region-set routing;
- same-world native allocation at M0 union MK, giving the map authority
  and BOTH actual record and marker elements for every region inum,
  under the source 32-bit bound, with any supplied frame retained;
- exact source ireg_couple and ireg_recs; a full 16-record-run/block-byte
  equivalence under diblk_wf, and whole-region byte factorization;
- source image_decode using existing kernel-checked 64/1024-byte codecs,
  allowing a boot-prelude theorem from arbitrary full supplied bss to
  concrete dss, decoding facts, authority + all cells, and the SAME byte
  resources, with no initialSnapshot dependency.
This is the actual allocation-and-byte stage of ireg_alloc, not a claim
that the complete slot/invariant has been built. No opaque missing rows
are introduced. The coordinator assigned the record camera slot 27, extending
the actual LockSet.registry: slot 26 already holds the held-set camera. No sleeplock
camera is implemented by this extension. Generic Capacity proofs precede
the explicit registry link and preserve all existing slots 0–26.

Next native subgraphs required for the full target are the complete
icache count/reference/freeze and escrow registry cameras, exact link/top
parking rows, logged byte/epoch invariants and observation receipts, the
complete slot and block/body assembly, and invariant allocation with all
original inputs/output. No premise may be silently strengthened or erased.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
