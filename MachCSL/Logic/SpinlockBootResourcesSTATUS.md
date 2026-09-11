# Concrete spinlock boot-memory resource extraction

`SpinlockBootResourcesDefs`, `SpinlockBootResourcesProofs` and
`SpinlockBootResourcesLink` extract the nineteen four-byte windows required
by the literal spinlock integration image from the existing initial heap and
timestamp fragments. The descriptor list is exactly the seventeen instruction
words in `List.ofFn` order, followed by the zero lock and zero counter. Its
seventy-six modular byte addresses are proved jointly duplicate free, with
all byte addresses in actual RAM.

`word_read` reuses the already checked actual loaded-image instruction,
lock and counter reads. `boot_lookup` obtains every finite-map byte lookup
from `BootFacts SpinlockImage.image g` and the actual allocation decoder
equation `FiniteMap.decode memory = g.memory`, using `readBytes_spec`.
`boot_time_lookup` maps those same present keys to the exact initial
`(0, payNone)` timestamp. No preferred finite-map enumeration, new memory
hypothesis, preboot register witness or replacement heap is chosen.

`extract_initial` instantiates the independently reviewed generic
`BootWindow.extract_words`. It returns full `storedWindow` ownership at
index zero for every instruction, the lock and the counter, together with
both exact residual maps after deleting all seventy-six keys. `windows_split`
keeps instruction resources as a separating list in descriptor order;
the writable lock and counter are separate conjuncts. The residual maps
retain every unselected full byte and timestamp cell. Explicit lookup laws
prove unchanged byte/time lookups outside the selected keys.

`boot_resources` consumes the existing `Tso.Interp.bootClients` component
of actual era allocation and returns those windows and remainders, preserving
the original log-length lower bound at zero. It reuses the supplied era's
heap, view and history capacities and runtime names. The result is an ordinary
separating entailment: no resource, name, camera or invariant is allocated,
updated, discarded or replaced. Heap metadata and the other era-allocation
client resources remain outside this component.

This is concrete integration glue over the source-backed physical/timestamp
ownership assertions and actual machine boot state. The paper pin remains
arxiv-v1 `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. It does not allocate the
lock protocol invariant, share code among CPUs, prove instruction WPs,
assemble all boot workers or establish exclusion/adequacy. The literal test
program is distinct from the pinned xv6 kernel image.

Validation: `python3 tools/lake.py build MachCSL.Logic.SpinlockBootResourcesLink`
passes all 423 dependency jobs (concrete proof module 1.8 s, link 0.883 s).
A fresh physical-origin audit checked all 41 declarations in the three
modules and their full type/body dependency cones. Only `propext`,
`Classical.choice` and `Quot.sound` occur; no unsafe/partial logical dependency
was found, and zero declarations were excluded. The seventy-six-key
nonduplication certificate uses ordinary kernel `decide`; all other links
are proofs over the existing checked semantics. No `sorry`, custom axiom,
`native_decide` or `bv_decide` is used.

The separate independent review of the root-authored generic extraction
appears in `docs/reviews/boot-window-review.md`; its fresh audit covered all
35 declarations in those two modules and passed all 418 dependency jobs.
Independent review of this concrete specialization remains an integration
step.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
