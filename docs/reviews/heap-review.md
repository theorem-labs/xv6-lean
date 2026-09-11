# Independent review: full heap and metadata

Reviewer: Codex coordinator, independent of the implementing subagent.
Read the complete Heap modules and the native Iris GenHeap definitions used by
the adapters. The source memory interpretation requires the full gen_heap,
including metadata, alongside the already ported byte/timestamp resources.

The adapter retains the existing byte camera at slot0; pointsto and physical
pointsto equality are definitional. Only metadata indirection and reservation
cameras are added, at13 and14. Runtime byte and metadata names are explicit.
Native gen_heap requires a lawful finite map and explicit absent keys for cell
allocation; no infinite physical-address assumption is introduced.

The important attachMetadata proof consumes the existing byte authority at its
existing name. Finite-map induction allocates only metadata, one top-mask token
per present key, retaining the full indirection authority and the native domain
condition. It returns every token and reconstructs the full genHeapInterp.
Existing byte and timestamp fragments can therefore be framed throughout. The
fresh allocation also returns every full points-to and metadata token. Updates,
metadata setting/agreement and token splitting use the native laws without
changing their conditions or discarding client ownership.

The fresh module-origin audit covered all164 declarations, including private
helpers, with only the standard three axioms and no unsafe/partial implementation.
Review result: PASS. Complete era allocation and machine lifting remain separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
