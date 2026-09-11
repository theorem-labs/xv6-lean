# First actual spinlock conflict execution review

The coordinator read all five witness modules. pauseRun_sound contributes
only actual register/plain-read NodeSteps, and unsupported pauses contribute
zero steps. cyclesRun_sound inserts real restarts. Fourteen closed kernel
certificates cover both seven-instruction setup sequences; two request and
two complete register-file certificates tie the exact paused continuation
and reject every fallback. The proof terms are ordinary checked equality,
without native evaluation axioms.

The full pool proof starts from one powered-off power thread, retains all
eleven boot workers, executes CPU0's successful exclusive zero read and a
separately counted CPU1 blocked read. The actual footprint conflict follows
from CPU0's exact zero snapshot. Disk preservation and unchanged RAM/log,
other-six-register files, generation and twelve pool occurrences are proved.
This is before any swap commits; it does not establish lock acquisition,
blocked unlock, two increments or the final seven-message trace.

Review approved. Build424 jobs; coordinator fresh audit160 physical logical
declarations through all opaque bodies/constructors, standard three axioms.
Three total-recursion compiler companions are excluded only as roots and
absent from logical cones. Explicit Fin8/Fin2 argument normalization fixes
a kernel conversion slowdown without changing semantics or proof premises.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
