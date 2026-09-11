# KernelTextImage interface review

PASS for the frozen Defs/Spec checkpoint. OpenAI Codex subagent
artifact_audit independently read both coordinator-authored modules, the
complete pinned iris/KernelText.v, and the relevant native KernelTextDatum,
KernelMapStatic, MycpuKptFetch and MycpuFetchBytes definitions. No signature
change is requested. Native implementations were not part of this review.

The six pure and seven native contracts retain the source distinction
between the sparse kernel byte map and default-valued kb_byte computation.
text asks only for actual successful sourceMap lookups. It owns actual
virtual RX text bytes and discarded pristine timestamp receipts; it has no
hart, running-context, returned-value, translation or execution premise.
The source kernel_text persistent finite-map conjunction is represented
extensionally, with a separate exact finite listedText equivalence contract.
The listedLookup and lookupListed fields make the correspondence obligations
explicit. The source/listMap equality and literal byte count are proof goals,
not trusted producer assertions or implicit disjointness assumptions.

The physical introduction consumes the existing native physicalText and
actual static-map claims. Positive/text-address geometry and the static RX
classification can attach the required identity claims. It allocates no
physical bytes, upgrades no timestamp fractions, and assumes no ghost map
agrees with a physical page table. Tier weakening follows the actual byte
ownership law; the full-tier text predicate still permits nonidentity pages.

The window contract uses every supplied successful sparse byte lookup, with
actual modular address addition and no hidden alignment or same-page
premise. This matches kernel_window_pc's resource role. The indexed mycpu
contract targets the actual14 MycpuKptFetch windows, whose alignment-dependent
2/4 widths include the34-byte fetch footprint. Persistence permits repeated
overlapping discarded-byte extraction while retaining text. Exact capacity
equality ties the shell's translation resources to this text capacity.

This checkpoint does not implement KernelText.v's complete instr constructors,
reference-state decoder transfers, landing-pad checks or any fetch WP.
Nor does it establish physicalText at boot. Those distinctions are preserved
by the actual statements; no whole-function or native-inhabitation conclusion
is advertised here.

Independent validation:

- PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.KernelTextImageSpec
- Result:582 jobs pass; log /tmp/xv6-lean-research/kernel-text-image-interface-peer-build.log.

Source pin: fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. A complete native
implementation and physical/type/opaque/constructor audit remain for the
final review; this report is deliberately an interface review only.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
