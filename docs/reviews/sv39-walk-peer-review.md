# Independent review: actual direct-slot Sv39 walk

PASS for the stated direct-slot scope. No semantic correction requested.
Reviewed all seven frozen Sv39Walk modules, STATUS and the design, against
actual generated `LeanPaperStock/Vmem.lean:243–414`,
`VmemPte.lean:258–285`, source `Pt4kWalk.v:385–477` and
`PtTree.v:435–453`, plus the existing checked PTE-read, KptLeaf and native
register/pinned-slot rules they compose. Source pin is arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

## Behavior and ownership

The public program is the actual generated `pt_walk 39` beginning at level2.
There is no replacement walk evaluator in the production proof. The four
44-bit PPNs and three selected nine-bit VPN indices compute the actual
physical slot addresses. The natural-address equation is kernel proved;
there is no wrap hidden in conversion from the 56-bit concatenation to64.
Computed addresses must still satisfy the explicit checked RAM/PMA/PMP
Config at all three levels.

`node_eq` separately instantiates all legal levels and preserves the
complete memory-error, invalidity, recursive and leaf-result branches.
Generated callbacks are pure model hooks, and the generated xlen assertion
reduces at this pinned64-bit model. The explicit64-bit PPN projection and
fixed-width continuation use kernel equality; no cast or unification
assumption changes the program. `afterInvalid` propagates each PTE's G bit
before its branch. The proved path specializes upper words to flags1 and
the kernel leaf to G=0, so preserving the incoming global flag is correct.
This does not prove traversal for arbitrary source G/RSW upper words.

Each pointer step executes its own ordinary checked memory read, obtains
canonical membership from the native pinned-slot rule and uses exact
nonleaf reconstruction to identify the next PPN. Leaf membership derives
one of all four A/D variants; the returned PTE is that actual observed
variant, with its actual address, level0, PBMT_PMA and symbolic leaf PPN.
It is not replaced by the reference word. No A/D update is performed by
pt_walk; that remains the separate generated update/translation path.

The validity plans universally quantify all responses of unowned control
register reads. They do not assume those controls equal the register
fixture. Pointer validity requires five such reads. At level0, the first
five-read invalidity test is followed by the actual leaf validator, which
repeats that test and performs two further extension/PBMT control reads.
The12-read leaf segment is retained. Each checked memory prefix contains
one PMA read, three PMP reads and one HTIF read. Thus the successful route
contains37 register reads and three ordinary memory reads; that count is a
reviewed consequence, not a premise enabling native execution.

Native composition retains the same four fractional register cells,
publication credential, each of the three independent slot fractions and
byte functions with its complete floor/anchor assertions, incoming
reservation and all three actual view receipts. The two other slots and
prior receipts are framed through each event. Exactly three later guards
are discharged by the three native memory reads. There is no ordering
claim between the three selected TSO views, no invariant held open across
Sail events, and no supplied per-node WP or fixed-read-value oracle.
Supported accesses remain exactly fetch, data load, data store and AMOSWAP,
with RX/RW permission constraints. The proof does not grant unsupported
access kinds or broaden kernel leaves to a general permission family.

## Independent checks

Fresh `tools/lake.py build Xv6.Kernel.Sv39WalkLink`: PASS,633 jobs.
Fresh physical-origin audit: **108 declarations across all seven modules**,
including private/generated roots, transitive types, opaque bodies and
constructors. Only propext, Classical.choice and Quot.sound; zero exclusions
and no unsafe/partial logical dependencies.

Six additional scratch theorems use kernel reflexivity on the actual free
register-event tree, with a concrete all-default register response fixture:

- pointer validity performs five reads and returns false;
- a valid RW leaf with A=false/D=true performs12 reads and returns that
  exact A/D variant;
- incoming global=true remains true for a G=0 leaf, while a different
  observed A/D variant is retained;
- a failed PTE read becomes PTW_No_Access;
- a V=0 leaf is checked twice, performs10 reads and returns PTW_Invalid_PTE;
- a valid nonleaf pointer at level0 is also checked twice and rejected
  after10 reads.

All six theorems pass and use only the standard three axioms. These are
sensitivity checks of the factor/control tree, not an alternative machine
semantics or a claim that the concrete register fixture meets the full
native walk Config. The generic production proof uses the universally
quantified plans and native memory rules.

Local evidence: `/tmp/xv6-lean-research/Sv39WalkPeerAudit.lean`,
`Sv39WalkPeerChecks.lean`, `sv39-walk-peer-audit.log`,
`sv39-walk-peer-checks.log`, and `sv39-walk-peer-build.log`.

Reviewed hashes (SHA256, abbreviated for identification):
Defs c6c8e088bfc6472c; Spec53aecc66aa49b029;
Pure13911144a2a4d7b6; Factor bfc99e2ad94ecb12;
NodeProofs a85ad49f8316b1a9; Proofs5440692fc28386b5;
Link d25936d251f9bad7; STATUS5f9a7300dd7b773b.

The documented remaining shared-KPT, raw upper-bit/G accumulation,
publication, TLB, full supervisor translation and virtual-myCPU integration
are real separate obligations. This review does not assert cross-backend
whole-model equivalence or whole-xv6 closure. No production file was edited.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
