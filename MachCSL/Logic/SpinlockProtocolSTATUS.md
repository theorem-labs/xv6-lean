# Concrete native spinlock protocol: native callback checkpoint

`SpinlockProtocolDefs` and `SpinlockProtocolSpec` state the reviewed design in
`docs/design/spinlock-native-resources.md`. The nine modules through
`SpinlockProtocolLink` now implement that interface. `actual` proves allocation,
all four native `EventPlan.Access` callbacks and exclusive holder fragments;
`registrySpec` instantiates it in the existing `FsTop` registry and its native
invariant world. It has no assumed resource-update or WP callback.

The requests are the actual generated-wrapper requests from
`Machine.SpinlockAccess`. An exclusive read records zero/one and retains its
exact reservation outside the protocol resource. Counter and holder resources
transfer only at the conditional-write commit of a reserved zero. A failed
swap still writes one but preserves the existing holder/position. Counter
addition is modular 32-bit addition. The actual `rw,w` fence preserves the
stored phase and receives no invented drain receipt.

The invariant owns one full native Lock authority. Its free branch also owns
the matching free fragment and full counter ledger; its held branch leaves
those resources with the client. The source acquisition-position product is
retained. The CPU-field marker stays `false`: this integration program never
writes an owner field. The latest lock writer and storage timestamp are not
identified with the owner or its winning acquisition position.

The winning payload retains both the actual authored-message receipt and a
view receipt at the acquisition position. Held/loaded phases require the
counter timestamp below that position. The stored phase makes no such claim,
because an ordinary counter store need not advance the view. Full bytes and
full timestamps stay linear. Only the invariant handle and generation
certificate are duplicated as persistent idle scenery.

The implementation proves current-word reads from the actual full heap,
timestamp bounds from the actual TSO interpretation, and visibility at every
allowed ordinary-read view from timestamp and view receipts. Successful writes
use the existing full-metadata heap/TSO store proof and actual authored-message
receipt. The invariant is closed before returning from each event callback;
there is no invariant opening across separate AMO read and write events. `writeModeEnabled` requires the actual
matching reserved proof mode for AMOs, and ordinary mode for counter/unlock
stores; these select proof contracts without changing machine guards.

This restricted machine-mode protocol is not the full source `lock_word_pin`,
context-indexed floor, `lock_pay` transport or xv6 acquire/release API. It does
not prove the annotated-pool `Covers` contract, cyclic control invariants,
operational exclusion, the interference witness or a closed two-hart gate.
The generic capacity reuses the existing machine cameras and native Lock slot
24. The concrete link preserves the complete `FsTop` registry through slot 25;
no extra camera or second native invariant world is introduced.

Validation: the complete `SpinlockProtocolLink` target builds successfully
(516 jobs; individual new proof modules at most 1.1 seconds in the final replay).
The fresh origin-based audit includes private/generated declarations and
traverses statements, proof terms and inductive constructors: all 199 logical
declarations passed with only `propext`, `Classical.choice` and `Quot.sound`.
There were zero excluded runtime companions and no unsafe/partial dependency.
The audit source/log are `/tmp/xv6-lean-research/SpinlockProtocolAudit.lean` and
`/tmp/xv6-lean-research/spinlock-protocol-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
