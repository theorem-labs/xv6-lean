# Held-lock interference witness review

The coordinator read all seven modules, including the closed generated-code
certificates and the composition into actual PoolSteps. The 431-job build
passed. An independent audit checked all 178 physical-origin logical
declarations and their full opaque-body and constructor dependency cones.
Only the three standard axioms occur. One verified compiler-generated
companion of a safe total recursive definition is excluded as an audit root;
none appears in a logical dependency cone.

The execution starts from the previously checked first conflict. CPU 0
commits its successful swap, reads and increments the counter, and commits
the counter store. CPU 1 then reads the held lock and retains its reservation
while its generated continuation reaches the conditional write. CPU 0 runs
the actual rw,w fence and attempts its plain unlock store. That separately
counted step is blocked by CPU 1's reservation and retains both continuations.

Every write and reservation guard is proved against the actual machine state.
The readonly certificate interpreter has a checked NodeSteps soundness theorem;
unsupported events are handled by explicit actual event rules. No certificate
fallback supplies a missing request or continuation. The endpoint has exactly
two log messages, lock = 1, counter = 1, CPU 1's snapshot of 1, all twelve
pool entries and the unchanged physical disk. Power-on composition supplies
the complete initial-pool execution.

This checkpoint is approved. CPU 1's failed swap commit, CPU 0's successful
unlock, and CPU 1's later successful increment and unlock remain the final
part of the seven-message witness.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
