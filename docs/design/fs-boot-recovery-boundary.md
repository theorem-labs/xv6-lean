# Actual disk recovery and filesystem byte bootstrap

Proposed next boundary after the reviewed FsBytesBootstrap mint. This work
connects the mint to the current machine era's supplied physical disk bytes
and to the exact recovered view of those bytes. It does not allocate a new
physical disk authority or assume an unrelated committed block map.

Source baseline: xv6iris arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. Relevant complete contracts read:
LogDefs24–67/155–164, FsCrash349–366/460–480/640–810/844–940,
FsBoot86–329/332–445, DiskPtsto49–96/219–230, BioDefs132–153,
BioInv320–322, and FsBlocks96–120. FsCfgSnap's caller at approximately
1008 supplies the actual committed view and header exception set. Its
nearby clean-only comment does not narrow the executable lemma.

## Stage 1: exact recovery, with no native resources assumed

New owned files: `Xv6/Fs/RecoveryDefs.lean`, `RecoveryProofs.lean`, optional
split `RecoveryViewProofs.lean`, and `RecoverySTATUS.md`. Existing pure
SnapshotHome carriers, home/log sets and restriction are reused.

Definitions in namespace `Xv6.Fs.Recovery`:

- `headerN bs : Int := assembleBytes (bs.take 4)`.
- `headerWord bs i : Int := assembleBytes ((bs.drop (4*i)).take 4)`.
- `headerDecode bs : Nat × List Int`: convert word zero by `Int.toNat`,
  then decode words 1 through n. There is no truncation to 30 in this
  definition; short input, out-of-range words and arbitrary bytes retain
  the source's total behavior.
- `installStep P ls W i D` inserts `P (logSlot ls i)` at `W[i]?`, or returns
  D when absent. `install P ls W D` right-folds this over `List.range W.length`.
  Smallest index wins when W repeats an address; no malformed-input fold
  commutation is asserted.
- `recover P cov ls := install P ls (headerDecode (P (logHeader ls))).2
  (SnapshotHome.restrict P (SnapshotHome.homeSet cov ls))`.
- `Recovers P D cov ls := D = recover P cov ls` preserves the exact source
  equality predicate as well as its canonical constructor.
- `HeaderWF P cov ls` has exactly three source clauses: n at most 30,
  duplicate-free decoded list, and each member covered, outside the log
  region, and different from block 1. No extra padding or size premise.
- `view P D b := (D[b]?).getD (P b)`, and `writeSet P ls` is the finite set
  of every decoded header entry. This default differs intentionally from
  `SnapshotHome.view`, whose missing block is empty. The exception set may
  include writes whose payload already equals the raw disk.

Proofs: decode count/list agreement and clean-header identity; arbitrary
fold misses and duplicate-free hits; recovery determinacy and totality;
full block preservation without HeaderWF; write-set containment/exclusion,
exact home domain, restriction of recovered view equals D; full recovered
view; raw agreement off the header set, logged slot agreement on it, and
raw superblock preservation. For actual `blocks disk`, fullness is derived
from the existing reader theorem for every signed block number.

## Stage 2: exact client carrier and supplied-byte carve

New owned files: `MachCSL/Logic/DiskClientDefs.lean`,
`BioViewDefs.lean`, `FsBootBytesDefs.lean`, `FsBootBytesSpec.lean`, and split
`FsBootBytesPureProofs/CarveProofs/Proofs/Link.lean` as needed, plus STATUS.
No registry or existing module edits.

`DiskClient.Names` retains all fifteen source GNames: img, slot, nc, np,
claim, cfg, ord, nr, stage, head, perm, fl0, fl1, flr, pos. This is data;
it allocates no unported driver camera. `diskBytes capacity names` and
`diskBlock capacity names` use the existing Disk12 camera at `names.img`;
a block includes exactly length 1024 and its signed byte run.

`BioView GF` retains the full source record: DiskClient.Names, BitVec32
device, finite signed covered set, clean and dirty native predicates, and
both Timeless witnesses. `poolBlock capacity V b` is exactly an existential
byte list with physical diskBlock at V.names and V.clean b bytes.
`fsView` uses the existing FsBlockGhost mclean/mdirty definitions. These
are exact resource definitions, not an abstract Bio invariant or theorem.

`rawMap disk cov := SnapshotHome.restrict (blocks disk) cov` and
`dirtyMap := FsBytesBootstrap.cleanMap rawMap`. Source raw map lookups,
domain, full values, filters and map-to-set native distribution are proved.
Reuse existing CovIn without strengthening it: every covered block is
positive and its complete 1024 bytes fit inside the supplied disk length.

The carve takes the provided `Disk.imageBytes capacity names.img 0
(disk_read disk 0 ndisk)`. It returns every covered physical diskBlock.
The stronger primary form also retains the exact finite-map difference
between the full supplied byteRun and `flatten (rawMap disk cov)`, plus an
arbitrary supplied frame. This follows by the existing native image cut
once the signed subset fact is proved; full raw blocks discharge the
flatten guard. A source affine projection may forget that remainder.
No bytes are synthesized and neither disk authority nor name changes.

`fs_boot_ghosts` consumes those same physical bytes with the exact five
source premises: CovIn, home subset cov, committed view full on home,
exceptions subset home, and raw agreement off exceptions. Its output is
an existential exact six-name FsBlocks record retaining supplied link and
top names, plus:

1. poolBlock for every covered block, combining physical bytes with the
   clean machinery halves at raw contents;
2. raw cache authority and all-false dirty authority;
3. the actual nine-leg byte invariant at the fixed committed view;
4. the full, unsealed exception handle;
5. the second false dirty half for every covered block;
6. full committed byte runs for every home block;
7. parked cache halves at raw contents for covered non-home blocks;
8. the exact unused physical byte remainder and arbitrary frame.

All are produced by the reviewed native fs_alloc; the machinery half and
the second dirty half are not conflated. No empty exception seal is minted
for a dirty header.

## Stage 3: actual recovered disk and era integration

Use the canonical D = recover (blocks disk) cov ls, home = homeSet cov ls,
Dv = view (blocks disk) D, X = writeSet (blocks disk) ls. Public
`recovered_boot_ghosts` has only CovIn and HeaderWF as pure premises,
plus the original disk byte resource. Every other mint premise is derived
by Stage 1. It additionally returns the pure exact-domain/slot/raw ties
needed by recovery; D is definitionally the real replay result, not a
fresh parameter supplied by the caller.

An explicit coherent capacity record contains an Era.Capacity and an
FsBlockGhost.Capacity. Its FsBytesBootstrap capacity uses that exact
Era disk projection. The actual Link uses existing registry41, with no new
slots or physical camera. `forEra template era` changes only the img field
of the full DiskClient.Names template to era.disk.

`era_boot_ghosts` consumes `Era.interp era g` and `Era.bootClients era
memory g ndisk`, with arbitrary frame, CovIn and HeaderWF of the actual
`g.devices.virtio.v_disk`. It returns the same complete Era.interp, all five
non-disk boot client legs, the complete recovered filesystem bootstrap
bundle above, exact physical byte remainder, and frame. It does not
allocate another Era or replace the arbitrary current disk with the
initial artifact. Non-disk clients are stated explicitly in a new definition
and related to existing bootClients by a proved separating equivalence.

A separate literal leaf `Xv6/Fs/FsBootImage.lean` derives HeaderWF from the
already checked clean log and CovIn from Image.boot_image_wf, proves replay
is the actual initial home map, and specializes the same native rule for a
state whose actual disk equals Image.disk. The disk equality is explicit;
framing a disk authority alone is not presented as a proof of that equality.
Generic modules never import the literal image or Initial constructors.

## Validation and remaining source work

Stages freeze separately for source review. Stage 1 includes kernel checks
for short header input, repeated write-set addresses (first index wins),
a dirty header whose log payload differs from home, and an exception whose
payload already agrees. The model preserves these cases instead of changing
the decoder to simplify its proofs. Native stages audit every physical root,
opaque body, type and datatype constructor, with only the standard three
foundational axioms and no exclusions, unsafe/partial or Initial dependency.

This closes the concrete disk-to-fs_alloc bootstrap seam. The later native
FsCrash history/recovery record, persisted HeaderWF maintenance, permits,
commit/replay receipts, complete Bio invariant allocation, and the full
FsCfgSnap configuration/LogRes transaction state remain distinct source
interfaces to port next. In particular HeaderWF is an explicit generic
crash-state premise until obtained from the actual native P_fs recovery
predicate; only the clean initial leaf discharges it from literal bytes.
No pure snapshot validity is substituted for those future resources.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
