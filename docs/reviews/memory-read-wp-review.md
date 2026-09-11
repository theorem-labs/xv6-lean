# Independent review: native plain RAM-read WPs

Reviewer: Codex coordinator. Read all four MemoryReadWP modules, actual node
rules and supporting timestamp/view proofs; compared with HartEvents.v137–276
and RiscvExec.v534–656 at the paper pin.

The generic callback explicitly receives and returns the original power
interpretation. It must establish readability at every allowed view. The rule
proves reducibility at the current view, inverts every actual successor,
uses byte determinism, and independently pays the chosen view update and
receipt. Silent trace preservation follows the actual step. Older generations
use strict death receipts; current live operations cannot use dead stuttering.
The fixed-word rule correctly moves its existential outside the view quantifier.

The concrete pristine specialization closes the callback from native heap and
timestamp agreement, preserves the byte window, and returns the selected-view
receipt. The minting variant consumes writable timestamp-zero fragments and
returns persistent pristine ownership explicitly. No log emptiness or no-wrap
hypothesis is introduced. All native masks and guarded continuations match
step lifting, and final registry wrappers discharge component specifications.

Review: PASS for these constructor rules. Resume contexts, ordinary shared
context loads, exclusive reservations and MMIO are separate remaining layers.
The generic callback is an explicit conditional adapter of the source's
mstate/tso callback; it is not the complete source context interface.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
