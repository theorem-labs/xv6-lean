# Native event-plan WP fold

The four `EventWP{Defs,Spec,Proofs,Link}` modules are checked and frozen. They provide a native-Iris fold over a finite, universally branching plan for the actual Sail free-event tree. Each register or RAM event consumes its existing machine WP rule separately; no instruction or cycle becomes an atomic machine step.

`ownedMap` removes exactly `sig_seip` and `sig_meip` from the actual typed initial register map. `ownedMap_lookup` covers every register constructor. `initialCells_split` preserves the full initial resource: 178 CPU-owned cells and both full typed pin cells, allowing the PLIC actor to own the latter. The symbolic register table's pin entries are ignored by `ownedCells`. Consequently, an `ExecPlan` postcondition concerns that symbolic table and its owned entries; it is not an assertion that actual hardware pin values equal the table's ignored entries.

`ExecPlan.readPin` quantifies independently over every typed result at every read. Owned reads/writes use an accessor that extracts and restores exactly one full register cell. RAM plans require a plain, nondevice request and explicit `ReadAllowed` evidence. `RamAccess` extracts actual byte ownership and pristine timestamp windows from a framed resource and provides their restoration wand. This is a resource contract, with no assumed callee WP. The fold calls the linked pristine read rule, which handles every allowed TSO view and returns byte ownership. No full-RAM ownership contract is imposed by the generic interface.

The terminal continuation remains a WP of the actual `.pure ()` hart node: this node restarts a cycle in the machine semantics and is not a native language value. A later guarded loop proof must discharge that continuation. The fold alone is neither an infinite-loop proof nor a closed safety/adequacy theorem.

`EventWPProofs` imports the callee specs only. `EventWPLink.registryEventWPSpec` supplies the actual proved register and RAM implementations and the actual initial-map lookup theorem, using the existing final registry with no new camera slot. Structural bind and monotonicity lemmas are proved directly; no unavailable `LawfulMonad SailM` instance is assumed.

Validation: the concrete link rebuilt successfully (446 dependency jobs in the integration build). Fresh module-origin audit covered all 69 logical declarations in the four modules, including private helpers: only `propext`, `Classical.choice`, and `Quot.sound`; no unsafe/partial logical dependency and no runtime-companion exclusions. Audit source/log: `/tmp/xv6-lean-research/EventWPAudit.lean`, `event-wp-audit.log`.

Actual generated callback, clock, and interrupt-dispatch plans are developed separately in `Machine/JalLoopPlan.lean`. The full fetched-cycle plan, extraction/restoration from its concrete four-byte resources, preservation of a universal arbitrary-preboot register family, and the all-actor loop/adequacy gate remain separate obligations. Earlier finite canonical `RegisterExec` witnesses do not discharge those universal obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
