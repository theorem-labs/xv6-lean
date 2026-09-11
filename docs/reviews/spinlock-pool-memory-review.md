# Selected-hart spinlock memory transport review

The coordinator read MemoryTransports and StoreTransports completely. Code
reads use actual all-view CodeUnwritten facts and record view advancement.
Counter reads derive the returned word using counterTime ≤ winningPosition
≤ currentView ≤ chosenView. The source rw,w fence is exactly non-draining.
Counter stores increment modulo32 and use the actual new log position;
unlock closes the holder phase only at its successful zero-store event.
Blocked writes retain the same program, state, cursor and reservation.

Every theorem consumes actual Machine.Step evidence and returns the
functional Transition, selected cursor/phase/history facts and concrete
effect records. Ordinary appends preserve the original winning receipt and
view. No successful-access guard or other-hart reservation condition is
assumed away. Other-hart/occurrence preservation remains a separate proof.

Review approved. The 524-job combined build and coordinator's full-body audit
of all282 declarations across12modules pass using standard three axioms,
zero exclusions and no unsafe/partial logical dependency.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
