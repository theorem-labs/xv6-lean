# Root review: actual spinlock fetch plans

Verdict: PASS. The root implemented the initial fetch decomposition and read
the complete final modules after the artifact agent completed the alignment
and compressed-result cases. This is a joint implementation review, with
fresh separate kernel/dependency checks, rather than independent authorship
of the whole module.

The final theorem covers all seventeen instruction addresses and arbitrary
register files satisfying the source reset fields and PMP OFF facts. PMP
addresses and unrelated configuration bits remain arbitrary. The plan uses
actual translation, PMA, priority/PMP checks, MMIO rejection and RAM read
functions. The exported fetch theorem discharges the intermediate PMP plan
premise. The exact four-byte read predicate is separately tied to loaded
image bytes, and the final register file equals the initial one.

Each checked alignment and low-word encoding fact is an ordinary equality
certificate, checked by Lean's kernel. The final symbolic proof explicitly
follows the enabled compressed-extension checks and rules out a compressed
result for the actual words. No branch, register event or memory read is
replaced by a silent assumption. Resource preservation and instruction
execution remain subsequent composition obligations.

A fresh separate audit passed for all 69 declarations, including private
helpers and full type/body dependency cones. Only the standard three axioms
occur; no unsafe/partial semantic dependencies and zero exclusions.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
