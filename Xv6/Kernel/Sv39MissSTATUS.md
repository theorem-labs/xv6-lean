# Native Sv39 translation-miss composition

The six modules Defs, Spec, Factor, Rules, Proofs and Link prove the actual
generated `translate_TLB_miss 39` program. The native Link supplies the
three-level ordinary walk, exclusive A/D reread, conditional A/D write and
actual level-zero TLB fill implementations. The contract is a genuine
continuation WP, with no assumed successful execution or caller-supplied
callee specification.

The input is six actual register cells (five A/D configuration cells plus
the full TLB), two upper pointer slots and a full physical leaf slot.
Upper pointers are the direct walk's flag-one words. The ordinary leaf read
may observe A/D bits different from the physical leaf: those cached bits
are universally quantified after the walk. The physical slot has an
independent canonical A/D variant. Config supplies actual physical read
conditions at all three addresses and actual conditional-write conditions
at the leaf. Permissions and supported access remain explicit.

The exact generated program factors through every walk/update response;
errors are retained before specialization to the supported slot resources.
The walk contributes three memory-event guards. A/D contributes zero guards
for cached/disabled branches, one for exclusive reread, or two for reread
and conditional write. The disabled-update error leaves the TLB unchanged.
Successful cached, reread and written branches fill with their respective
actual words and retain the walk's PPN, PBMT and originating PTE address.
The native fill retains its read/write/read callback sequence.

The proof splits and reassembles the same six cells without allocating or
duplicating any. It returns both upper slots, the updated full leaf slot,
the original credential/floors/anchors, all three ordinary-read view
receipts, the branch's actual reservation and A/D receipt, and the proved
canonical physical word. The terminal continuation has no additional guard.
No invariant is held open across the memory events.

This direct-slot result does not yet expose shared KPT ownership, arbitrary
raw upper pointers, TLB-hit coherence, page faults for absent mappings, or
the complete translated instruction front end. Those remain separate proof
layers, and all six whole-system theorem roots remain open.

Validation: the final layout build passed 675 jobs. The full audit checked
all 89 declarations in six modules, including types, opaque bodies and
constructors, with only the standard three axioms, zero exclusions and no
unsafe/partial semantic dependencies. Evidence:
/tmp/xv6-lean-research/Sv39MissAudit.lean, sv39-miss-build.log and
sv39-miss-audit.log.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
