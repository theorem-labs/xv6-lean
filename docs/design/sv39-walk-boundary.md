# Actual three-level supervisor page walk

Owner: Codex coordinator. New Sv39Walk prefix under Xv6/Kernel; existing
frozen modules remain unchanged. Source Pt4kWalk385 onward, PtTree435–448,
and actual generated Vmem.pt_walk364–414. KptLeaf supplies the independently
reviewed actual leaf validator. This stage proves the real walk through
three directly owned slots; shared KPT invariant access is a later layer.

Path carries four symbolic44-bit numbers: root, level1 and level0 table
pages, and the final leaf PPN. The two pointer words are exact source
mk_pte(next,1). Addresses concatenate the selected9-bit VPN slice and
three zero bits below the table PPN. Pure contracts establish field
extraction, pointer classification/validity, exact natural address value,
alignment and reconstruction of any canonical-family leaf word as one of
the four actual A/D variants. No physical address is selected by the proof.

The public program is actual pt_walk39 at level2, Supervisor and arbitrary
MXR/SUM/global input. Kernel permission and access use the exact KptLeaf
classes; stores to RX remain excluded. Config supplies the actual existing
checked-read grant for each computed address: common TOR/PMA/PMP/HTIF
register state, source match/grant/aligned RAM. The shared fractional
register footprint has four cells. No MISA or menvcfg cell is needed by
the universally quantified register plans.

Input memory is the existing source pinned slot resource, with independent
per-level fractions and arbitrary actual physical byte functions. A common
publication credential and bound authorize ordinary reads at every allowed
TSO view. Pointer families force exact pointer words; the leaf family permits
arbitrary A/D bits. No fixed read result, stable selected view or physical
leaf word is assumed. All three slots and the credential are returned, as
is the incoming reservation, because these are ordinary reads.

The genuine terminal continuation receives the actual PTW_Output: symbolic
leaf PPN, exact just-read leaf A/D variant, computed level0 slot address,
level0, PBMT_PMA and unchanged incoming global flag. It also receives all
three actual view receipts; no additional ordering claim is made. Exactly
three guards come from the three native memory reads. Every register event
is folded separately through actual native rules; there is no per-node WP
or supplied interpreter theorem in the public contract.

Implementation will factor the real read/error/invalid/recursive/leaf
branches, preserving all arbitrary-response residuals. Pointer validity
uses five universal eager reads. The level0 path checks invalidity and
then invokes check_leaf_pte, which checks invalidity again; both executions
must remain. Expected successful path has three real memory reads and37
register reads (three checked prefixes5 each, three invalid checks5 each,
and the leaf validator7); counts are descriptive and must be verified,
not premises. No A/D write occurs inside pt_walk: actual update_and_write
belongs to translate_TLB_miss, and is being proved independently.

The contract is useful for direct stable ownership. Shared table ownership
must later supply genuine per-event accessors with its invariant closed
between Sail events. TLB insertion/hits, translation-mode/effective-address
composition and the whole supervisor kernel regime remain open. No fresh
camera, initial-state assumption or whole-system closure is introduced.
Definitions/Spec receive independent review before proofs; every physical
module and dependency is audited before publication.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
