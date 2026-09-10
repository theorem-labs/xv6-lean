# Independent review of the generated free V1 model

Scope: the adapter pipeline in `lean-sail`'s `prototype/`, its generated
`LeanPaperBoundPlatform` output, and the `RootJal.lean` instruction fixture.
This review does not establish Rocq/Lean compiler correspondence, the paper's
machine semantics, MachCSL adequacy, or an xv6 boot theorem.

## Sources and reproducibility

The source model is `zeldovich/sail-riscv` commit
`23dcf8fd923eb8a1958795393d2975632aa940b2`; the configuration and module list
come from `mit-pdos/xv6iris` paper tag `arxiv-v1`, commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. Generation uses official Sail
0.20.2, source commit `3b7af38d66466ecadad563158b07ce2f82fe05da`, rather than
the paper's Rocq generator version 0.20.1. This version difference is an explicit
correspondence obligation. Runtime reviewed here is
`28c729b5bb574ae7c32c13353403e57c575d85dd` on Lean 4.32.2.

I independently replayed the four adapters in order against the preserved raw
output and compared all 132 generated model Lean files with the final two-hook
output. They match byte for byte. This establishes deterministic reproduction
of the inspected adaptation from this raw input, not verified compilation from
Sail. The adapters' inspected SHA-256 hashes are:

| Adapter | SHA-256 |
| --- | --- |
| `adapt_paper_0202_signature.py` | `50e83c45972537e4c255b8f8edf1e55ed466f8078c32fb0d95a490fea76453f1` |
| `parameterize_paper_0202_externs.py` | `9cb631970ce1d2429931531e0312e36ab9292449e3848e7fbe91d1b613e2f36c` |
| `normalize_paper_0202_rvfi.py` | `52d28bd6d427cf694647b9d4a5fb42b6cd772415eb4f19e281dc2730baad24e2` |
| `bind_paper_platform.py` | `26a27eb607f57ba67e46e418b30054a0118a07d4bd8df859a1dbdaf2b3d2fa45` |

The transformations replace the sequential monad with the dependent free event
monad, make the generated architecture instance reducible, install specialization
wrappers, expose foreign functions as explicit parameters, normalize one RVFI
printing block, and bind the paper's platform definitions. The generated sequential
IO `main` is omitted; no executable emulator is asserted by this package.

## Platform bindings

The [paper's `xv6iris_extras.v`](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/model-xv6iris/xv6iris_extras.v)
provides the comparison source. Its two fixed reservation predicates remain
explicit parameters: the Lean `match_reservation` at physical-address width and
`valid_reservation : Unit → Bool`. No constant result is selected for either.
Rocq's second predicate is a Boolean; the Unit function is an equivalent carrier.
Rocq's first predicate is width-polymorphic, whereas this generated architecture
uses 64-bit physical addresses. That is a specialization, not a proof of the
polymorphic source interface.

`load_reservation`, `cancel_reservation`, and `plat_term_write` return pure unit
in the pinned source and in the adapter. The load hook's unused width is an
integer in Rocq and a natural number in Lean; its constant result makes this
local binding consistent, but it does not discharge integer-width translation
elsewhere. The false experimental-extension flag agrees with
[`riscv_extras.v:28`](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/model-xv6iris/riscv_extras.v#L28).

The remaining 67 pure foreign operations and two effectful hooks have separate
`UnboundPureHooks` and `UnboundEffectfulHooks` classes. These are arbitrary
parameters, not implemented semantics. Compilation or an axiom-free report alone
cannot justify an entry point that requires either class. Their absence must be
checked in entry-point types and transitive dependencies; adding all three class
variables to a source section relies on Lean retaining only variables actually
used in each declaration.

## RVFI transformation and announcement behavior

The RVFI adapter names each register read immediately before its pure printing
helper. Independent comparison confirms all 18 `(register, getter, label)` triples
remain in their original order. No read is removed, duplicated, or moved across
another read. The digest check and residue check restrict the rewrite to the
specific recorded block. `normalizePureArgument` proves the corresponding local
free-monad equality by reflexivity. This is a generic local identity; the script
has not generated a theorem equating the two complete source files.

Both actual generated announcement wrappers in `Common0.lean` are pure unit,
matching the paper's [`rv64d.v:6799–6803`](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/model-xv6iris/rv64d.v#L6799-L6803).
They are not replaced by the generic free runtime's effectful announce wrappers.
The corrected runtime also handles an absent memory-write payload as pure
`Ok None`, matching coq-sail 0.20.1's builtin. These checks settle those particular
wrapper behaviors; choice carriers, request encodings, and other correspondence
obligations remain as listed in [the correspondence audit](../Sail-correspondence.md).

## JAL fixture and proof scope

`RootJal.lean` executes the actual generated `execute` definition on a zero-offset
JAL with destination register zero. Its explicit interpreter handles only register
reads/writes; every other event returns `none`. Fuel exhaustion also returns
`none`. The fixture uses synthetic register values, including PC `0x80000000`,
nextPC `0x80000004`, and an explicit `misa` value. The proved trace reads nextPC,
PC and misa, then writes nextPC to `0x80000000`; a second theorem checks that
final register value.

The finishing tactic asks Lean to prove reflexive equality with full transparency.
It does not call `native_decide`, introduce an axiom, or replace execution by an
external evaluator. Nevertheless, this theorem is about the stated register
interpreter and fixture. It does not fetch/decode bytes from the ELF, initialize
the real machine, execute memory effects, establish a relation to `mnode_step`,
or discharge the whole-machine gate. The file's own scope comment is accurate.

## Validation and remaining gate

The final two-hook package completed its full build: 100 jobs. I independently
ran a stronger compiled check over all six entry points. It traversed **8,378**
transitive type/body constants and checked **3,070** constants originating in
the inspected generated-model and Sail runtime modules. It found no dependency
on either unbound class, no custom axioms, and no partial, unsafe, extern,
implemented-by or opaque-data hooks in those model/runtime cones. Standard
Lean library computational primitives were outside the implementation-hook
check; axiom and unbound-class searches traversed their dependencies too.
The temporary check used module origins in this exact package environment;
the root package audit must use physical package origins for its durable gate.

`execute` and `try_step` retain only `[Platform]`. `tick_clock`,
`sail_model_init`, `init_model`, and `init_boot_requirements` require neither
`Platform` nor either unbound class. The first five roots have only `propext`,
`Classical.choice`, and `Quot.sound`; `init_boot_requirements` has only
`propext`. This checks assumptions of the definitions, not correctness of the
encoded architecture.

I reran both JAL proofs against this final two-hook output, rather than relying
on their earlier 75-field prototype environment. Both pass and have only
`propext`, `Classical.choice`, and `Quot.sound`. I also reran the generic RVFI
normalization proof; it passes with only `propext`.

The earlier `ExecuteAudit.lean` and `FullModelAudit.lean` logs were useful
exploratory inventories, but walked only
generated definition bodies and reported selected leaves. They did not traverse
all types or enforce rejection of unbound classes and computational hooks. They
must not be used alone as the gate.

The durable entry-point check must continue to inspect `execute`, `try_step`, `tick_clock`,
`sail_model_init`, `init_model`, and `init_boot_requirements`, including transitive
types and bodies. It must reject either unbound hook class, custom axioms, and
unreviewed model/runtime partial, unsafe, extern, implemented-by or opaque-data
hooks. Standard Lean axioms are separate from semantic platform parameters.
The root package audit should additionally cover every imported generated
declaration by physical package origin, including private declarations, rather
than exempting the model as a trusted library.

Review result: no blocker found to publishing this as a compiled, explicitly
parameterized generated model with the stated small execution fixture. The
whole-machine semantic gate remains open. In particular, the two fixed
reservation predicates do not instantiate the paper's concurrent reservation
state, and no result of this review substitutes for request/choice correspondence,
ELF-linked instruction execution, the `mnode_step` relation, or system adequacy.
