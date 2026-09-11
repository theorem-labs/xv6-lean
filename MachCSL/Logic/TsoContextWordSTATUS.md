# Physical context words and stack frames

This checkpoint implements the physical word and stack algebra underlying
`TsoCtx.v:845–940`, `StackOwn.v:45–57,151–315`, and the two-slot save/restore
sequence in `ProofMycpu.v:97–135,208–266`. The pinned xv6iris source is
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The complete relevant word,
stack split/join, and `mycpu` prologue/epilogue source was inspected.

The seven modules are `TsoContextWord{Defs,Spec,Proofs,Link}` and
`StackPhysical{Defs,Proofs,StoreProofs}`. This is a **physical prerequisite**:
the source `ctx_word_pointsto` also owns virtual translation and kernel-tier
claims, which these modules do not assert. Accordingly `StackPhysical.own`
is not advertised as the full source `stack_own` predicate or a function WP.

| Source operation | Native Lean implementation |
|---|---|
| Eight aligned context bytes | `TsoContextWord.pointsto` |
| Exact source/generated alignment guard | `Aligned`, `aligned_iff_sail` |
| Word agreement | `agree`, through native byte-camera agreement and byte extensionality |
| Full registered finite-map bridge | `pointsto_map` |
| Every permitted ordinary read view, one common view for all bytes | `load_fact`, `load`, `Readback` |
| Actual eight-byte ordinary registered store | `ordinary`, with unchanged views |
| Constructed resource contract | `Spec`, `actual`, `registrySpec` |
| Modular `pa_stk` geometry | `paStk`, `paStk_assoc`, `paStk_shift`, `paStk_add_back` |
| Exact indexed existential stack contents | `words`, `own` |
| Split/join at any natural depth | `words_append`, `own_append`, `own_split` |
| Empty, one- and two-slot frames | `own_zero`, `own_one`, `own_two`, `frame_two` |
| The caller's concrete save addresses | `frame_two_addresses` |
| Two separate ordinary save updates with retained deeper stack | `save_two` |
| All-view restoration facts and exact stack recombination | `restore_two` |

Word ownership uses exactly eight existing `TsoContext.physPointsto` cells,
with the same runtime context names, physical heap name, timestamp name,
and fractions. Every byte retains its clean-floor or authored-dirty
justification. The word store converts the full eight-cell window to the
actual `TsoStore.windowMap`, using the already proved finite-window key
injection at length eight. The old and new maps have exactly the same
domain. The existing registered store payer performs one actual authored
message append and preserves complete heap metadata, TSO interpretation,
and the running context. Its ordinary transition keeps every CPU view
unchanged. No resource callback or store-correctness assumption is added.

`Readback` contains both actual `ReadsBytes` and `readBytes = some word` at
every view above the CPU's current view. Loads preserve the complete input
resources. `save_two` takes two separate `OrdinaryTransition` premises with
an explicit intermediate state; it does not collapse the two instructions
into an atomic step. After the second save, the first saved word's readback
is re-established from its retained physical/context ownership in the new
state. `restore_two` returns the stack with existential contents, so the
saved ra/s0 values need not equal the caller's previous scratch contents.
The exact deeper remainder is framed throughout both compositions.

Stack addresses are modular 64-bit subtraction `sp - 8*k`. The actual
indexed source length/list representation is retained; no global no-wrap
bound, finite-depth cap, canonical-address assumption, or 16-byte alignment
is introduced. Every owned word separately asserts the source eight-byte
alignment. The exact `mycpu` address facts are `(sp-16)+8=sp-8`,
`(sp-16)+0=sp-16`, and `(sp-16)+16=sp`, all proved for arbitrary `sp`.

The registry is unchanged from `TsoContext.registry` (held-lock slot 26).
No camera is added and no full writable token is converted to discarded
ownership. Virtual-address/tier interpretation, S-mode translation, SIE and
stack-register capabilities, actual load/store instruction WPs, and the
complete supervisor `mycpu` proof remain separate obligations. This slice
also does not port the source's virtual-context morphisms, base-order
stack enumeration, or every fractional word convenience lemma.

Validation: the combined `TsoContextWordLink` and `StackPhysicalStoreProofs`
build completed **436 jobs**. The fresh physical-origin audit checked **47
logical declarations across all seven modules**, including opaque theorem
bodies and inductive constructors. It found only `propext`, `Classical.choice`,
and `Quot.sound`, with no unsafe or partial dependency and **zero exclusions**.
The constructed contract, exact Sail alignment bridge, two-slot algebra,
and save/restore compositions were also checked with `#print axioms`.
Raw evidence remains outside the repository at
`/tmp/xv6-lean-research/TsoContextWordStackAudit.lean` and
`/tmp/xv6-lean-research/tso-context-word-stack-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
