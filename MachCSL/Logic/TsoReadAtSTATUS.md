# Latest-value reads with timestamp and view receipts

`view_bound` derives the current CPU view bound from native TSO authority and
its persistent receipt. `byte_read` combines actual heap-byte agreement with the
complete timestamp invariant, retaining arbitrary payloads, and proves the
latest owned value readable at every permitted later view. `window_read` lifts
this to the exact modular byte window without adding an alignment or size bound.
`power_read` accesses the current era through its generation certificate;
`registry_power_read` instantiates the existing shared 23-slot machine capacity.

This differs from the pristine-code bridge: timestamps need not be zero. The
caller must provide a view receipt at least as recent as the owned byte timestamps.
These are native ownership-to-read facts, not a memory-event WP, lock invariant,
or proof that a fence advances a CPU to the global log top.

Validation: component build passes (423 jobs). Fresh physical-origin audit checks
all 6 declarations and their complete type/body dependencies; only propext,
Classical.choice and Quot.sound, no unsafe/partial dependencies or exclusions.
Independent review passed; see docs/reviews/tso-read-at-review.md. Next consumer: the exact exclusive-read view receipt
and the store timestamp window for the two-hart counter read.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
