# Independent review of the common mycpu body footprint

Result: PASS for the declared body-only scope. The artifact-audit Codex agent independently read all five frozen MycpuCycleBody modules, their design/status, and the underlying MycpuScalar, MycpuMemory and MycpuReturn definitions. This is a separate review of the coordinator-authored implementation.

The instruction partition matches pinned `iris/CodeMycpu.v`: scalar indices 0,3–9,12; stores 1,2; loads 10,11; return 13. The bodies run the actual generated `execute` and its one `ExecuteAs` redirection. The four `*_tail_eq` theorems compare those bodies with the complete `MycpuActive.executeTail` result wrapper; they preserve all execution-result cases, including a second ExecuteAs result. Generated `Step.lean:321–396` and source `SmodeCore.v:167–248` provide the active-step context, but this layer does not assert the source progress lemmas or run dispatch/fetch.

The 28 distinct keys are the fourteen Active cells, six GPRs, four retirement cells, three clock cells and hart-state. PC/nextPC and every written register have full ownership. Read-only control, TP and hart shares remain explicit; the two retirement control shares are discarded. The membership certificates retain these exact fractions. Structural widening changes proof-side membership only; RegisterPlan and memory-boundary native folds operate on one bundle, without splitting overlapping footprints or allocating replacement ownership.

The store rule uses actual context-backed write, full old word and reservation custody. On success it returns the new word, cleared reservation and actual view receipt. The load rule retains its arbitrary fraction and reservation, pays the real read and then the actual destination-register write. The one guarded continuation in each memory rule remains present. The original error residuals remain in the boundary proofs; owned RAM readability and the actual native rules justify successful execution, rather than an assumed returned value or preservation callback. Scalar and return rules use the genuine register fold. Setup/complete/clock membership facts are interface certificates only.

Independent verification passed: `python3 tools/lake.py build Xv6.Kernel.MycpuCycleBodyLink` (656 jobs), then a fresh physical-origin audit of all 90 declarations in the five modules. The audit inspects opaque bodies, types and inductive constructor fields, permits only propext/Classical.choice/Quot.sound, and rejects unsafe/partial dependencies. Zero roots were excluded. Evidence: `/tmp/xv6-lean-research/MycpuCycleBodyPeerAudit.lean`, `mycpu-cycle-body-peer-build.log`, and `mycpu-cycle-body-peer-audit.log`.

No correction requested. Full fetched cycles, retirement, supervisor-entry establishment, KPT translation and complete mycpu/function correctness remain outside this layer.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
