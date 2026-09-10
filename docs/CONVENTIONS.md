# Lean port conventions

These are implementation contracts for new specifications and proofs, checked
against the pinned paper artifact and the selected native Iris implementation.
They are design decisions; the concrete xv6 ghost registry and kernel function
contracts described here have not yet been implemented. Exact whole-system
acceptance criteria live in [THEOREM_TARGETS.md](THEOREM_TARGETS.md).

## Concrete Iris functor slots and instance derivation

Native Iris at `728a17140939e49af9236f7cb0d037da9ec52435` does **not** represent
its functor collection as a list. In
[Iris/Algebra/IProp.lean:21](https://github.com/leanprover-community/iris-lean/blob/728a17140939e49af9236f7cb0d037da9ec52435/Iris/Iris/Algebra/IProp.lean#L21),
`GType` is `Nat`, `GFunctor` bundles an `OFunctorPre` with its
`RFunctorContractive` witness, and `BundledGFunctors` is `GType → GFunctor`.
`BundledGFunctors.default` uses the constant `Unit` functor at every index;
`.set` replaces a designated index. The source explicitly declines to port the
Rocq list combinators and `subG` API.

[ElemG](https://github.com/leanprover-community/iris-lean/blob/728a17140939e49af9236f7cb0d037da9ec52435/Iris/Iris/Instances/IProp/Instance.lean#L64)
is a class containing a chosen slot `τ : GType` and a dependent equality
`FF τ = ⟨F, ‹RFunctorContractive F›⟩`. Membership is therefore evidence about
one specific slot, including the functor's contractiveness witness. It is not
merely a proposition saying that an equivalent resource algebra occurs somewhere.

Use the following construction discipline:

1. Define a finite registry of named xv6 slots, their natural-number indices,
   and the contractive functor assigned to each. Prove that the declared slot
   indices are distinct. Embed that registry in a total `BundledGFunctors`, with
   unused indices mapped to the default `Unit` functor. Record the source bundle
   and purpose of every slot. The paper's `xv6Σ` at
   `iris/SystemAdequacy.v:922` combines seven groups (`riscvΣ`, `xv6GΣ`, `fileΣ`,
   `fdslotΣ`, `irefslotΣ`, `pavΣ`, `ufdΣ`); the final flattened slot count must be
   derived from their actual ported contents, not guessed from a review estimate.
2. Define a canonical bundled functor and contractiveness witness for each
   entry. Construct each `ElemG` certificate explicitly using its assigned
   index and a proof of the dependent equality. Build higher-level capability
   instances from those certificates in a recorded acyclic dependency order.
   Generic libraries may accept capability parameters; the concrete system
   instantiation must discharge them from this registry.
3. When the same functor occurs in multiple slots, pass the intended certificate
   explicitly to ownership and allocation APIs. Distinct resources must not
   accidentally alias because typeclass search selected another `ElemG` of the
   same functor type. Prefer named parameters and scoped instances; avoid broad
   global instance builders that search for the capability they are constructing.
4. Keep functor capacity separate from runtime ghost allocation. Slot membership
   provides a place to allocate; it neither chooses a ghost name nor proves
   ownership, freshness, an invariant, or the initial state interpretation.
   Derive pre-allocation capabilities from the registry, then prove the relevant
   allocation updates and produce the runtime ghost-state records. Preserve the
   source distinction between resources fixed across eras and resources freshly
   allocated at a power cycle. Reboot must preserve the durable disk.
5. Audit each concrete theorem's elaborated type and dependency cone. A closed
   system root may not leave an arbitrary functor family, unproved capacity
   instance, runtime ownership record, or kernel function specification as a
   hidden premise. Its permitted parameters are the exact documented source
   parameters and explicit platform assumptions.

This choice uses Iris's existing functor implementation and slot certificates;
it does not introduce an alternative recursive proposition model. Any further
transport lemmas must prove equality or the required nonexpansive equivalence
at the real Iris types. No cast axiom, opaque computational placeholder, or
unproved instance is an acceptable way to finish the registry.

## Function contracts, proofs and linking

The paper artifact uses real Rocq module signatures and functors. For example,
`SpecAcquire.v:399` declares `ACQUIRE_GEN`; `ProofAcquire.v:82` defines
`AcquireGenProof (Mycpu : MYCPU) (Holding : HOLDING) (PushOff : PUSHOFF) :
ACQUIRE_GEN`; and `LinkAcquire.v:9` applies that proof functor to the linked
callee modules. The proof file imports callee specifications, while the link
file connects their implementations. This separation prevents an unfinished
callee proof from forcing downstream proofs to depend on its implementation.

Lean namespaces and imports do not reproduce Rocq module sealing. Preserve its
contract boundary explicitly through the following file and declaration roles:

| Role | Contents and permitted dependencies |
| --- | --- |
| `Defs` / shared abstractions | Semantic data, ownership predicates, invariant definitions, state and context interfaces. These are actual definitions used in statements and included in the semantic audit. |
| `CodeF` / generated image facts | Reproducible concrete instruction bytes and checked symbol/offset facts for the pinned binary. Generated files are never hand-edited. |
| `SpecF` | The public function contract, parameterized by the required shared interfaces, and a named proposition-valued record of proof obligations. It may import shared definitions and callee specification vocabulary when necessary, never callee implementations. |
| `ProofF` | A proof constructor that receives explicit callee contract records, proves every field of `SpecF`, and imports its own code facts and needed logic. It imports callee specifications, not their proof or link files. |
| `LinkF` | Applies `ProofF` to already proved callee contract records and exports the resulting contract theorems. This is where the independent proofs meet. |

A proposed `FSpec ... : Prop` record contains proof fields for the exact required
entailments and weakest-precondition claims. Its preconditions, postconditions,
and separating conjunctions remain expressions of native `IProp GF`; they must
not be replaced with ordinary Lean `Prop` conjunctions. Shared ownership
predicates and other computational data belong in explicit definitions or
interface data records outside the proposition-valued proof record. Keep those
data arguments identical across the specification, proof and link layers.

Use ordinary explicit parameters such as a named callee contract value for the
proof constructor. A Lean `structure` is not automatically a typeclass, so do
not write instance-implicit brackets around such records unless they are
intentionally declared as classes. Explicit proof dictionaries are the default
for kernel callees: a concrete link should visibly enumerate the contracts it
uses, and a missing proof should appear as an unfilled linking dependency.

Declare completed proof results as kernel-checked theorems. Lean proof opacity
is useful for modular checking, but does not provide Rocq's full module-sealing
semantics. Enforce the specification boundary through imports, reviewed public
interfaces, and dependency checks. Do not hide executable definitions behind
unreviewed `opaque`, `partial`, `unsafe`, external implementations or axioms.
Import restrictions must be checked transitively: a shared helper cannot smuggle
a callee implementation into its caller's proof layer.

Mutual recursion in the kernel call graph requires the actual guarded
weakest-precondition/Löb argument, or another justified simultaneous proof.
Cyclic Lean definitions or recursive instance search are not linking proofs.
Strengthen an abstraction only through an explicit reviewed contract change;
never add a convenient precondition, weaken a conclusion, alter the binary, or
change the machine rules merely to make a local proof close.

Before scheduling broad `Spec*` ports, compile a small genuine end-to-end
example with this arrangement: the selected concrete functor entries, a callee
contract, a caller proof receiving it, and a link that supplies it. Check the
exported theorem type, all implicit arguments, and transitive assumptions. This
will settle elaboration, universes and the exact native Iris API. The prose here
is not a claim that a proposed untested record layout already compiles.

## Semantic and review records

Each ported module records its pinned source symbols, its exact Lean exports,
any representation correspondence still outstanding, and remaining obligations.
Checked pure lemmas and a successful build must not be reported as instruction,
kernel, filesystem or whole-system verification. The exact six exported targets
and their conditional-versus-concrete distinction control completion.

Task ownership includes files and signatures before agents implement dependent
proofs. A reviewer should check semantics, possible vacuity, implicit parameters,
axioms and defining-module provenance, not only proof syntax. Definition
correspondence and concrete binary/image facts remain separate obligations even
when a theorem has no unexpected axioms.

These conventions incorporate Claude Code's `claude-fable-5-1` reviews at effort
`max`, with two source-validated corrections: native Iris uses a natural-number
indexed functor family rather than a list, and Lean contract records require an
explicit replacement discipline rather than an assertion of Rocq-equivalent
module sealing.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
