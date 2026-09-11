# Fresh static map installed in the actual text-owning boot era

The unchanged approved four pure and two native contracts are now fully
implemented in four KernelTextBootMap modules:876 jobs pass. All33 physical
declarations passed a strict full type/opaque/constructor audit, standard
three axioms only and zero exclusions. Coordinator final review is pending. It combines existing native allocators
without assuming map authority, matching names or preexisting text ownership.

Source boundary: RiscvPtsto.v175–381 includes the actual era kernel-map name
beside the separately allocated tree/bound/translation names. KptPt.v's
static map and BootCarve.v sections1/3/5 supply the mapping-claim and named
text roles. The native KernelMapStatic and KernelTextBoot APIs already
prove allocation/persistence and actual boot-byte carving. Paper pin:
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

The order is dictated by names and resources:

1. KernelMapStatic.allocate creates actual initialMap authority and persistent
   claims at a fresh runtime name gamma. This is an actual native ghost-map
   allocation, with the caller's frame preserved.
2. install template gamma is a record update of kernelMap alone. Pass that
   exact template to KernelTextBoot.allocate. This allocator uses actual
   Xv6.Machine.boot before, its exact finite-map decoding witness, native
   Era.allocate and the proven sparse text carve/persistence.
3. Its AuxiliarySame output yields era.kernelMap=gamma. The pure auxiliary_iff
   exposes precisely the other ten unchanged source auxiliary fields:
   tree, bound, translation, SIE, SPP, SPIE, parked-hart, process-state,
   log-mirror and held-lock names. Machine component names remain freshly
   allocated and are not asserted equal to the template.
4. Rewrite the actual allocated map resources to era.kernelMap, and use
   KernelTextImage.physical with the real same-name claims and physicalText.
   This attaches native identity RX claims to the actual physical bytes.
   Both text and physicalText are persistent, so both survive. The full
   linear static-map authority is retained.

Installed is an output proposition: exact era.image, installed kernelMap
name and OtherAuxiliarySame. Neither that equality nor any map resource is
an input to allocate or allocate_frame. The framed contract preserves an
arbitrary actual resource alongside the complete result. The output resources
contain Era.interp, map authority and claims indexed by the era's actual
kernelMap, persistent physicalText and identity text, and the full exact
KernelTextBoot.retained bundle (unselected byte/timestamp maps, log receipt,
all metadata, registers, devices, disk and reservation clients).

FiniteMap.encodeAll is used only symbolically through the existing allocator
and decoding theorem. There is no64-bit enumeration or trust in a caller's
image-byte oracle. The native freshness/frame rules pay the new map instance;
no fresh-name inequality is manufactured as an unrelated pure hypothesis.

This installs only the mapping ghost name and its actual authority/claims
into the era record. It does not install a physical KPT, allocate or shoot
the tree/bound one-shots, switch SATP, mint translation receipts, configure
supervisor registers or establish a complete boot handler/function WP. The
other auxiliary names are preserved as names; their camera resources remain
separate obligations.

Owned files: KernelTextBootMapDefs/Spec/Proofs/Link plus STATUS. The private
generic allocation-framing helper prevents proofmode from expanding the
large static map. The public theorem instantiates its predicates and laws
with the exact native authority/claims, static-map allocator and identity
text bridge. It adds no caller obligation. No existing allocator, generated
artifact, other owner's module or umbrella was changed.

Validation: PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build
Xv6.Kernel.KernelTextBootMapSpec. Log:
/tmp/xv6-lean-research/kernel-text-boot-map-signatures.log.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
