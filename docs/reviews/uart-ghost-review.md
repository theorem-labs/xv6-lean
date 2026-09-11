# Independent review: UART ghost algebra and PLIC plan

Reviewer: Codex coordinator. Read the complete UartGhost definitions,
specification, proofs, registry/link and Plic/Plan. Compared the source four
UART quantities and capacities in WpUart.v and PlicPlan.v41–65.

Accepted and transmitted prefixes use separate runtime names in the same
MonoList camera. Transmitter agreement tracks accepted output (out ++ tx),
not just pending bytes. DLAB is fractional agreement, with a paid persistent
freeze. Initial allocation preserves arbitrary DLAB; it does not assume reset.
The ready/poll laws use actual agreement and output-prefix inclusion, and
transmit/receive preservation relies on the exact pure UART transition laws.

The extended registry preserves slots0–19 and uses20–22 for trace, transmitter
and DLAB capacities. It reconstructs every machine and native invariant
capacity explicitly; no cross-registry ownership cast is assumed. PlicPlanOK
quantifies every Nat context/word and masks unsigned values, matching the
source's nonnegative integer bit test. Reset and latch preserve all enable
words. Further PLIC driver plan laws remain outside this component.

Review: PASS for the ownership algebra and these plan laws. Native device
invariants, trace permits and the loop WP are the next layer; this component
does not establish an output protocol or whole-system result.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
