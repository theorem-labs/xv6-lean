Ordinary four-byte physical memory operations

SupervisorRead4 and SupervisorWrite4 implement the actual generated
checked data access programs with 32-bit payloads. Both borrow the PMA,
PMP configuration, PMP address and HTIF cells at their stated fractions.
The actual matched region, consumed read/write attribute, alignment and
TOR RAM bounds are explicit physical-layer facts. They do not replace a
source virtual mapping or a successful translation proof.

The read uses the generic plain-event boundary also used by fetch, with
Load.Data permissions throughout. It reconstructs the full 32-bit payload,
retains all generated response tails, and folds the actual event with the
native context-byte read rule. The continuation gets its actual universally
quantified view and the same fractional window, running context and cells.

The store retains all successful optional payloads and the actual error
Boolean, then uses full context-byte ownership to prove native success.
TsoContextBytesStore handles the registered finite-map heap and timestamp
update for n <= 2^64 distinct byte offsets. TsoContextBytesWriteWP constructs
the exact ordinary successor and payer inside the actual event's later,
leaves blocked retries unchanged, appends one authored message, preserves
all CPU views and clears only the writing hart's reservation. The four-byte
adapter discharges the width bound internally and returns all register
fractions, the updated word, running context and actual view receipt.

These are physical data operations. Virtual translation, mem_read and
mem_write_value outer effective-privilege paths, write-EA announcement,
full LOAD/STORE execution and push_off composition remain separate work.
The native source word4 resource bridge is KernelDatumWord4.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
