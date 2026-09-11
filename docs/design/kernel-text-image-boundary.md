# Exact kernel text image and virtual fetch windows

Source: full KernelText.v, pinned xv6iris arxiv-v1
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. Its kernel_text is the finite
persistent conjunction over KernelInstrs.kernel_bytes, with hart-independent
RX byte ownership and discarded pristine timestamps. The Lean byte table
already imports the exact ordered sparse source runs, with earlier entries
winning and absent addresses remaining none.

KernelTextImage.text expresses the conjunction extensionally: for every
successful actual source-map lookup, own the actual KernelTextDatum byte
at that virtual address with discard share. It contains no hart, context,
decoder, translation or execution premise. The native listed theorem proves
this assertion equivalent to a finite nested separating conjunction over
the seven source runs and each run's byte indices. The listedLookup and
lookupListed pure contracts prove both directions of the enumeration;
source proves equality to the imported first-winning listMap semantics.
There are exactly23,748 obligations. The sparse gaps after0x80005ba0 and
after the trampoline code ending0x80006124 remain absent, not zero-filled.

All mapped source addresses are positive canonical virtual addresses inside
the physical text interval0x80000000..0x80007000. The source assertion is
identity tier. The native physical theorem attaches the actual static map's
identity RX claim to every already owned physical byte/pristine pair. Its
inputs are actual KernelMapStatic.claims at the era's existing map name and
physicalText; no map or physical byte is allocated. A private generic proof
parameter avoids normalizing the49,154-entry static map; the exported native
constructor instantiates it with that exact map and its proved lookup rule.
There is no generic map callback or alternative physical image in the public
Spec. Establishing physicalText from boot allocation is separate work.

The general window theorem projects any finite source-backed byte window,
including windows that cross pages. Tier monotonicity only moves identity
to full using the actual KernelTextDatum rule. Full tier keeps virtual RX
ownership and can support nonidentity mappings in generic clients; the
specific physical-text producer constructs identity ownership.

The mycpu theorem retains text and produces all fourteen existing native
MycpuKptFetch windows. Every byte is checked against sourceMap, including
the two successor bytes read by the final aligned return fetch. This is a
34-byte union with overlapping persistent windows, not only the32-byte
function body. It does not assert a native decode or successful execution.
The caller supplies an existing shell capacity whose translation component
is the same actual capacity; this is camera identity, not a resource oracle.

Five modules implement six pure and seven native contracts, plus persistence
and supporting lookup proofs. Defs/Spec were independently approved before
native implementation. Pure proofs use kernel-checked decide for finite
source checks; no native_decide, runtime snapshot or axiom is used. Full
build858 jobs and strict all127 physical/type/opaque/constructor audit pass
with standard3 axioms only, no unsafe/partial dependency and zero exclusions.
Independent final review is separate from this owner record.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
