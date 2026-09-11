# KernelTextImage independent peer review

PASS for the declared resource boundary. No implementation correction is
required. This review independently read all five Lean modules, their final
STATUS and design, and the complete pinned KernelText.v. It reran the Link
build, a strict physical-origin dependency audit, eight kernel boundary
checks, and the exact source-map importer check/self-test.

Source pin: xv6iris arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
Reviewed modules: KernelTextImage{Defs,Spec,PureProofs,Proofs,Link}.lean.
All six pure and seven native contracts are supplied by the final native
constructors. No unproved interface instance remains in the exported Spec.

## Source and representation

Source kernel_text is the persistent per-byte finite conjunction over the
actual KernelInstrs.kernel_bytes map. Lean text quantifies only successful
lookups in the exact imported first-winning ordered run map. The source,
listed_lookup and lookup_listed laws establish the correspondence in both
directions; the native listed theorem proves equivalence to the finite
nested separating conjunction. Persistence permits extraction of overlapping
windows while retaining the original text resource.

The seven runs have lengths 4096, 4096, 4096, 4096, 4096, 2976 and 292,
for exactly 23,748 source-byte obligations. Their starts are
0x80000000, 0x80001000, 0x80002000, 0x80003000, 0x80004000,
0x80005000 and 0x80006000. They are disjoint. The gap beginning
0x80005ba0 and the interval beginning 0x80006124 are absent; the resource
contains no obligation there. The byte-count theorem does not infer a dense
interval from the physical text range. The exact importer check additionally
verified the pinned source blobs and reproduced the generated maps without
changing them; its negative-path self-tests passed.

Every source address is proved positive and inside the source physical text
interval, including the physical trampoline code. The physical producer
requires actual raw byte ownership and discarded pristine timestamps at the
same era names, plus actual KernelMapStatic RX claims. It attaches the exact
identity PPN claim and closes the existing native text-byte predicate.
The generic private map entailment is instantiated with the real static map
in the public native rule. Neither byte ownership nor a map is minted.

The source default tier is identity. The extra tier parameter and monotonicity
use the established native byte rule; the generic full-tier assertion still
owns RX mappings and pristine physical bytes and does not assume identity.
The producer from this literal physical text specifically returns identity
tier. No trampoline virtual alias or arbitrary physical-word substitution
is inferred from the source integer address.

## Windows and scope

The generic window law requires every byte lookup, transports integer address
addition into actual modular addressAdd, and uses the native per-byte
predicate. It introduces no same-page condition and no default value.
All fourteen mycpu fetch windows are derived at the exact same capacity and
era while retaining text. The independent final-fetch checks establish the
four bytes `82 80 01 11`, actual width four and word 0x11018082. Thus the
resource covers the 34-byte fetch union, including the two bytes after the
32-byte function body. No decoder, physical table or successful execution
premise is used in this extraction.

The complete source KernelText.v also provides default-zero kb_byte/kb_word_at
convenience functions and generic reference-state instr_intro constructors.
Those wrappers are not exported by this boundary. Their default values are
never substituted for missing bytes here. The current native producer and
window contracts are source-compatible resource work, not a claim that all
of KernelText.v or source boot allocation has been closed. The final design
and STATUS accurately keep physicalText allocation, entry establishment and
whole-function/system closure separate.

## Independent validation

The fresh Link build passed 858 jobs. The strict audit independently selected
all 127 declarations by the five physical module origins, including private
and generated declarations. It checked all axioms and traversed every type,
opaque value and referenced datatype constructor. Only propext,
Classical.choice and Quot.sound occur; there are zero exclusions, no
unsafe/partial dependencies and no Initial allocator dependency.

Eight kernel checks passed: exact seven interval shapes, total count, eight
absent-address edge cases, the last/beginning bytes surrounding sparse gaps,
the final four literal fetch bytes, actual final width, actual final word,
and the native retained-text/all-window contract. The audit and checks ran
against the rebuilt frozen modules. No implementation, source map or umbrella
was edited by the reviewer.

Evidence under /tmp/xv6-lean-research/:
KernelTextImagePeerAudit.lean, KernelTextImagePeerChecks.lean,
kernel-text-image-peer-{build,audit,checks,map-check}.log.
The importer command was
`python3 tools/kernel_maps.py .upstream/xv6iris --check --self-test`.

Reviewed SHA-256 values:

| File | SHA-256 |
| --- | --- |
| Defs | f53a481138def757a964f7cdd5eed0f400f778f38c6d4e66b314de3c56b7f2ad |
| Spec | 476bb0e1213def2d747bf14d59dab9b25913312bfba0d6481412197e4e721de4 |
| PureProofs | 6e3bebf7cc4973383b3accad2100aedaacca68866386f2dbcf5f308f7bcc01a6 |
| Proofs | 0b2313d8ebf63f251d45b6e9c942bfc14f3b65f634e349bbe20ffb2bd94dd6c1 |
| Link | f1c78e542c9a7596a8389cd3e36dc15a1c558da04f2acb3da0d95958b2d61168 |
| STATUS | 50c7205cbba8f76bc5614bd35bfdb3782c46fdb9503674849b20b528d25a522a |
| Design | b2f9fbab93c387f5a6e74014a0c1256b06741dc592aee5632c17a766ae4a2c0a |

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
