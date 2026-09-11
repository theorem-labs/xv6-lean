# Actual shared-kernel TLB miss

All seven KptMiss modules compile (832 jobs). The coordinator approved the
actual Defs/Spec checkpoint (443 jobs) before proofs. Link now constructs
all four pure factor/coherence contracts and the native full-miss contract,
with the approved signatures unchanged. No prior frozen implementation or
umbrella was changed.

Sources read: complete frozen KptTreeWalk Defs/Spec/native walk, approved
KptAD Defs/Spec and its completed native Link (owned by the logic agent), generated
Vmem.translate_TLB_miss and VmemTlb.add_to_TLB, the existing Sv39Miss generic
factors, PtTreeAdue.v:1873–1934,2044–2250, KptTree.v:680–747 and its resident
routing, and the already reviewed TlbCoherence source sections. Artifact pin
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476; model source pin
23dcf8fd923eb8a1958795393d2975632aa940b2.

The program is actual translate_TLB_miss39, using the supplied tree's base,
Supervisor mode, arbitrary ASID, VPN, supported kernel access, MXR and SUM.
The Config supplies all three exact read-address hardware configurations
and the read/write hardware configuration at the leaf. Maps relates raw p2
and p1 to the tree and the reference KptLeaf RX/RW leaf. Upper PTEs are not
replaced with flag-one representatives; their valid G and RSW bits remain
arbitrary. The walk starts with global=false exactly as the generated miss
does, then accumulates G from both raw pointers and its returned leaf.

The initial resource bundle is six control cells: the five fractional KptAD
controls plus full TLB. It also contains the persistent shared invariant,
canonical tree snapshot, publication bound and per-hart credential, plus the
current reservation fragment and generation certificate. There are no direct
physical slot resources, no caller-chosen physical word and no successful
read/write equations. The snapshot leaf's A/D bits are reference data; the
ordinary walk's cached A/D pair and later exclusive observed word are chosen
by the actual shared events.

The exact sequencing is:

1. Three ordinary shared PTE reads with the full generated raw-upper and
   leaf checks. The native walk returns three view receipts and a cached
   A/D pair. Its register feature reads remain in the existing walk proofs.
2. Actual KptAD update on that cached word and the installing leaf address.
   Cached, disabled, reread and written branches have 0/0/1/2 further memory
   guards. The branch-dependent observed/new words occur ONLY in the branch
   result, not as initial inputs. BranchFacts is inside those guards, as in
   the approved KptAD interface.
3. Disabled returns PTW_PTE_Needs_Update without touching the TLB. Cached
   fills with the ordinary walk word; reread fills with the observed word;
   written fills with the new word. Each successful arm uses actual
   add_to_TLB with its read/write/read sequence, including the callback read.
   PPN/PBMT and global flag are the original walk's output fields. A/D
   stability proves agreement of those fields with the selected word.

`afterUpdate` and `afterWalk` reuse only the existing Sv39Miss GENERIC raw
continuations. Those definitions quantify arbitrary PTW_Output/global and
preserve all walk/update errors. KptMiss does not use Sv39Miss.Path, its
flag-one/G=false specialization, direct slots, fixed physical leaf, resource
predicate or native miss theorem. The new program factor targets the actual
KptTreeWalk program and these generic continuations. General factorization
retains errors before supported shared-memory reasoning discharges the
appropriate branches; it does not turn error outcomes into successful fills.

The final resources retain all six control cells (with the exact TLB update),
the same four persistent clients, all three walk receipts, the exact KptAD
receipt, and the exact branch reservation. Cached/disabled retain rr;
reread reserves the observed eight-byte snapshot; written clears reservation
and yields the positive authored history timestamp and view receipt already
specified by KptAD. No terminal or register-only guards are invented.

The caller supplies pure snapshot-relative Coherent for its initial TLB.
A separate pure contract derives an A/D Variant for the actual selected
fill word from BranchFacts and the canonical KptLeaf identity. The second
pure consequence proves the entire final TLB Coherent with the SAME snapshot:
raw global and PPN stability reconcile the actual old-walk fields with the
source new-word entry, then TlbCoherence.fill applies. The disabled branch
retains initial coherence unchanged. This preserves foreign VPN tags/hash
collisions and does not demand a frozen physical word or postulate that
all resident entries equal the queried VPN.

The principal continuation has exact form:

```
▷ ▷ ▷ (∀ cachedA cachedD view2 view1 view0 branch,
  KptAD.guarded branch (
    pure(BranchFacts cached reference access enabled branch) -∗
    resources(..., branch) -∗ WP(continuation(result branch))))
```

Thus BranchFacts cannot expose the unknown exclusive-read word before its
real event. Persistent clients may be copied using their native instances;
linear register and reservation resources must be split and reassembled,
never duplicated. The completed proof links to actual native KptTreeWalk and
KptAD implementations at the same KptShared.Capacity. No new camera, pure
success oracle, Initial allocator or new ghost world is part of this layer.

The pure proof derives fill-word canonical equality and then separately
derives unchanged PPN and accumulated G relative to the cached word. It
rewrites the actual fill into TlbCoherence.filled and applies the existing
source fill law. The native proof partitions the six cells for the walk,
reassembles them, partitions for shared A/D, and reassembles again before
the actual TLB fill. The three walk guards are consumed first; only then
is the KptAD branch selected, and its own guards are consumed before facts
and final resources are exposed. Persistent full clients are retained while
the shared+snapshot projection is passed to A/D. No physical bytes are
frozen between the ordinary read and exclusive reread.

Fresh full physical-origin audit covers all 89 declarations in seven modules,
including private/generated helpers, types, opaque bodies and constructors.
Only propext/Classical.choice/Quot.sound occur, with zero exclusions, no
unsafe/partial semantic dependency and no Initial dependency. Seven additional
kernel checks cover cached/observed/new selection, disabled unchanged TLB,
raw upper G set/clear and reread-selected A/D. Evidence is recorded in STATUS.

This closes only the full shared TLB MISS. It does not
provide lookup/miss dispatch, shared hit completion, SATP-switch two-tree
coherence, canonical virtual-address front matter or translated mycpu from
boot. Cross-backend correspondence remains separately tracked.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
