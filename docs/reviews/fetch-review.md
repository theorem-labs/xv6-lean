# Independent actual-fetch witness review

PASS: no soundness or fixture-fidelity defect found in the reviewed snapshot.

- `MachCSL/Machine/FetchRun.lean` SHA-256:
  `a89e0012af9f17f2089745ae2ce1f85d6167759d81b92fac8b919b41b2ecf059`.
- `MachCSL/Machine/FetchJal.lean` SHA-256:
  `f8bed16bab5036015660045db251625c6719657888f7601b6b91aec182ae5fa4`.

`fetchRun` interprets dependent register reads/writes and actual nonexclusive RAM
read events. It obtains each memory word through `Memory.readBytes`, which
rejects missing bytes and has a bytewise specification with modular addresses.
The evaluator has no JAL-specific event handler, instruction decoder or success
case. Unsupported events return `none`; this narrows only the proof evaluator,
not the `NodeStep` relation.

`fetchRun_sound` embeds each accepted event into an existing `NodeStep`.
For reads, its explicit hypothesis identifies the evaluator's map with the TSO
observation at the state's fixed view, and its view bound satisfies the node
read rule. Register updates preserve this hypothesis and bound. The terminal
case uses the ordinary reflexive finite closure; it neither introduces a new
terminal node transition nor skips an event. `fetchRun_bind_pure` preserves fuel
because mapping a return value does not insert events.

The fixture is `0x0000006f` at the requested RAM reset vector, with remaining
RAM zero, running from the register file produced by actual generated boot.
`fetchedJal_observation` reduces actual generated `try_step 0 false`, not a
handwritten JAL execution function. It checks the returned waiting flag, PC,
nextPC and retirement count. The complete generated path includes instruction
fetch/decode, `execute_JAL`, and the step postlude. The cycle theorem uses the
shared `Machine.cycle false`, corresponding to pinned `RiscvLang.v:222–224`,
without ticking the clock. This is a local one-instruction witness; arbitrary
external schedules, whole-machine reachability, repeated-cycle safety and
adequacy are separate obligations.

Read generated source: `Fetch.lean:216–279` (memory-backed fetch),
`InstsEnd.lean:17470–17478` (JAL), and `Step.lean:406` onward (`try_step`, PC update
and retirement). The underlying generated Sail/Rocq correspondence remains a
separate repository obligation; this review concerns the actual Lean model.

Two independent ordinary-kernel sensitivity checks passed:

1. With the same actual boot registers and program, replacing RAM by the empty
   map makes the evaluator return `none`.
2. Changing only the instruction bytes to JAL x0,+4 makes the actual program
   return PC = nextPC = `0x80000004` and minstret = 1.

These checks establish that this computation observes the supplied RAM, and that
its result changes with the fetched instruction. Scratch driver
`/tmp/xv6-lean-research/FetchReview.lean` passed in 3.13 seconds wall with maximum
RSS 1,950,764 KB. Both sensitivity proofs have only `propext`, `Classical.choice`
and `Quot.sound` transitively; the production file enforces the same allowlist
for all nine handwritten proof roots. Log: `fetch-review.log` in the same scratch
directory. No production edits were required.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
