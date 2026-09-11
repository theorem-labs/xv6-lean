# Independent full-pool witness extension review

PASS. The Codex coordinator reviewed the single new PoolProofs module
separately from its author. full_pool instantiates the existing focused
node-to-pool theorem with the exact four preceding threads (power and
CPU0–2) and seven following threads (CPU4–7, UART, disk and PLIC).
The resulting endpoints reduce to power :: powerFork0, with the original
configured state, actual14-cycle derivation and exact final writeBack.
No state or instruction certificate is changed. The other workers remain
present and unscheduled. Positive length follows from the actual CPU3 PC
change; the zero-step case entails equal complete configurations.

full_pool_length proves twelve threads. entry_ms_facts separately checks
all ten mstatus facts by kernel reflexivity, without creating Iris bit
resources. The original nine witness modules are unchanged.

Target passed735 jobs. The fresh coordinator audit checks all five physical
declarations, including the private zero-step helper, types, opaque bodies
and constructors. Only the standard three axioms occur, zero exclusions
and no unsafe/partial dependency. Evidence:
MycpuBareWitnessPoolRootAudit.lean and mycpu-bare-witness-pool-root-audit.log
under /tmp/xv6-lean-research. This extension addresses Fable round eight's
pool wording request; it was not included in that review's frozen packet.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
