# Installed static-map boot text: frozen native allocation

The four approved pure and two native contracts are implemented in four
modules. Full build876 jobs (Proofs997ms, Link989ms). Strict owner audit
checked all33 physical declarations, including the private generic helper,
with exporting disabled and full types/opaque bodies (allowOpaque=true)/
constructors. Standard three axioms only, no unsafe/partial dependencies,
zero exclusions. No sorry/custom axiom/native_decide/bv_decide. Generic
nativeSpec and the existing48-slot registrySpec discharge all fields.

Source boundary: RiscvPtsto.v175–381 actual era names; KptPt.v static map;
BootCarve.v sections1/3/5 static claims and persistent named text. This is
composition of the already native KernelMapStatic allocator,
KernelTextBoot allocator and KernelTextImage physical-to-identity bridge.
Pin: fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

allocate_frame first creates actual initialMap authority and persistent
claims at a fresh native ghost-map name. install modifies only the caller
template's kernelMap field. Actual KernelTextBoot.allocate then creates
the boot era and its exact interpretation/clients using that template.
AuxiliarySame proves era.kernelMap is the newly allocated name and preserves
all other ten source auxiliary fields. Installed exposes that fact together
with the actual era.image equality. No name equality or map authority is
assumed as a producer input.

The same-name persistent claims and physicalText produce actual identity
text. Both persistent text resources remain available. The full linear map
authority is returned at era.kernelMap, together with claims, Era.interp,
and every exact KernelTextBoot.retained client. The arbitrary caller frame
survives both native allocations and the attachment step. allocate is the
empty-frame specialization of that implemented theorem.

The private allocate_frame_generic helper abstracts only the map predicates
and their two already-proved native operations during proofmode elaboration.
The public theorem instantiates authority/claims with exact KernelMapStatic
predicates, allocation with KernelMapStatic.nativeSpec.allocate, and text
attachment with KernelTextImage.nativeSpec.physical. No public callback or
component-law assumption remains. This avoids repeatedly normalizing the
large static map. Local irreducibility affects proof elaboration only;
the full opaque/type/constructor audit still checks the entire proof cone.

FiniteMap.encodeAll stays symbolic inside the proven actual boot allocator;
no exhaustive64-bit enumeration occurs. Machine-component names are fresh,
not asserted equal to the template. Other auxiliary fields are retained as
names, without claiming their kernel-camera resources were installed.

This establishes positive native identity-text ownership at the actual
fresh era's map name. It installs no physical page table, tree/bound shot,
SATP translation mode, per-hart publication receipt or supervisor register
configuration. It does not establish a boot handler, full function entry
bundle or paper adequacy root.

Reproduction:

- PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.KernelTextBootMapLink
- PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/KernelTextBootMapOwnerAudit.lean

Evidence: /tmp/xv6-lean-research/kernel-text-boot-map-{build,owner-audit}.log;
exact hashes in kernel-text-boot-map-frozen.json. Coordinator independent
review is pending. See docs/design/kernel-text-boot-map-boundary.md.

No existing owner module, allocator, generated artifact, registry slot or
umbrella was modified.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
