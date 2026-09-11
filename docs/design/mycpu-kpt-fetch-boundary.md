# Indexed mycpu fetch over the source register packet

This is the implemented native packet wrapper for
`Xv6.Kernel.MycpuKptFetch`. All sixteen approved contracts are implemented in six modules: ten pure,
five resource and one native fetch. The final Link build passes 1,068 jobs;
the full 117-declaration audit has zero exclusions.

Source pin: xv6iris arxiv-v1 `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
Read source `CodeMycpu.v` in full (all fourteen `myi_XX` facts),
`ProofMycpu.v` entry packet and instruction chain, `InstrBytes.v`53–73 and
533–540/646–673, alongside the complete generated fetch and the existing
MycpuDecode, MycpuFetchBytes, RegimeShell and KptFetch modules.

## Chosen code boundary

The input is an exact fourteen-window virtual code bundle, indexed by
`List.finRange 14`. Each window is the existing native
`KernelTextDatum.window`, at `MycpuDecode.address i`, with the actual
`MycpuFetchBytes.width i` and `MycpuFetchBytes.word i`, at discard share.
This is virtual RX mapping plus physical byte/pristine ownership through the
existing tier predicate; it is not a supplied physical-window or read oracle.
The full tier permits nonidentity PPNs. No physical mapping is inferred from
the concrete virtual address.

These windows cover exactly 34 bytes of the actual ELF-backed image, including
`01 11` after the 32-byte function. The two base instructions are four-aligned;
compressed instructions at four-aligned addresses still own/read four bytes.
The pure `image` and `coverage` laws tie every window value and the union of its
byte offsets to `Xv6.Machine.bootImage`, reusing the existing independent image
certificates. Repeated overlapping bytes are persistent discarded ownership.
No global kernel-text allocation or boot reachability is claimed.

The resource `instruction` law derives the precise existing KptFetch
InstrBytes at each index from this bundle. The returned fetch result is exactly
`MycpuFetch.result i`, based on MycpuDecode's encoding and compressed tag.
`decodeFetch` reproduces source InstrBytes' decoder selection, including its
zero-word error default. Its pure identity with `MycpuDecode.decode i` and the
existing actual decoder certificate identify `MycpuDecode.decoded i`. The
certificate uses its explicit known decoder snapshot; this fetch wrapper does
not execute decoding or assert a decoder WP for arbitrary MISA/MENVCFG values.
That remains the subsequent dispatch/decode composition.

## One packet and one translation resource

Capacity and Shares are the existing MycpuRegimeShell records. `fetchShares`
borrows PC full, MISA at its supplied share, mstatus full, and the four source
privilege/PMA/HTIF/MENVCFG shares. The seven keys are unique and members of the
same fifty-cell source footprint. The exact filter complement has 43 keys.
`packetFrame` retains these 43 cells, source SIE/SPP/SPIE/off bit ownership,
all ten MsFacts, and the software x0 fact. All 31 actual GPR cells are therefore
preserved, including the native pinned TP value; TP is not replaced by a pure
claim.

The approved memory-wrapper partition direction is reused: decompose the same
RegimeShell.packet into borrowed cells, its complement/bit/x0 frame, and the
existing folded KptResidue. That residue alone owns SATP/TLB/PMP vectors.
The wrapper never borrows a duplicate copy or pins its old TLB after a fetch.
The native conclusion reconstructs the entire original source packet after
the actual refreshed coherent residue returns.

Config includes Supervisor privilege, pmaBoot, HTIF-none, MISA.C=1 and
MENVCFG.ADUE=1, all attached to the owned control file. SXL=2 is derived from
the native packet's MsFacts rather than added as another caller premise.
The `sourceConfig` helper derives C/ADUE from the exact source literal
MISA/MENVCFG values. No translation-success, body WP, selected physical word,
PMA region match, or successful decoder is a native fetch premise.

## Actual guards and returned resources

The sole native contract consumes the same packet, code bundle, current
reservation, arbitrary frame and final guarded continuation. PC is tied to the
chosen actual instruction address. It invokes the already proved full
KptFetch internally. `finish` preserves the exact `guardChunks` structure:
path witnesses, actual hit/miss branches, scoped A/D facts, actual instruction
read guards and views. Though these fourteen concrete instructions each need
one chunk, the contract retains that existing structure and does not discard
possible miss/A-D event counts.

The final resources retain the full packet, code bundle, exact
`traceReservation rr trace`, every translation/read receipt and the arbitrary
frame. No allocator, registry change, Initial constructor or assumed boot
world is used. Fetch is the scope: no instruction body, retirement, clock,
restart or whole-function WP is promised here.

## Implementation and validation

`PureProofs` proves the footprint facts, source-literal Config bridge, actual
image read/coverage, result-to-decoder identity and original decoder certificate.
`Resources` proves the explicit seven/43 cell separation and reassembly using
the native shell partition, persistence/timelessness, and all fourteen
window-to-InstrBytes projections. Small kernel decision certificates establish
the concrete width/alignment facts before dependent byte-window rewriting.
They avoid treating opaque generated predicates as reduction oracles.

`Proofs.wp_fetch` unpacks the native packet, obtains its existing MsFacts,
rebuilds the bit/x0 frame, invokes the actual full KptFetch theorem, and lifts
its returned resources through the same modal guard fold. Every original
resource column is restored. `Link` supplies native Specs and the exact
existing RegimeShell registry capacity; no new camera or ghost world exists.

Six files: `MycpuKptFetch{Defs,Spec,PureProofs,Resources,Proofs,Link}.lean`.
Build: 1,068 jobs without warnings. Audit: 117 physical-origin declarations,
including private helpers and every type/opaque-body/constructor dependency;
only propext/Classical.choice/Quot.sound, zero exclusions, no unsafe/partial
or Initial dependency. Eight kernel checks confirm all 31 GPRs remain in the
43-cell complement, TP is not duplicated, translation registers appear in
neither side, the 44 overlapping window bytes cover precisely 34 image bytes,
and the final actual four-byte JR fetch and decoder-program identity.

Evidence under `/tmp/xv6-lean-research/`:
`MycpuKptFetchOwnerAudit.lean`, `MycpuKptFetchChecks.lean`, and
`mycpu-kpt-fetch-{build,owner-audit,checks}.log`.
`MycpuKptFetchSTATUS.md` records this frozen boundary. No neighboring frozen
files or umbrellas were changed. Native decoder, body/retirement/cycle and
whole function composition still require their own resource proofs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
