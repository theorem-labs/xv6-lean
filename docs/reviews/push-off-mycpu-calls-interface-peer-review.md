# push_off mycpu call-code interface review

PASS for the compiled Defs/Spec checkpoint. I am the separate
`lean_logic_audit` agent reviewing the coordinator's proposed resource
producer. I read both complete modules, the source CodePushOff preamble
and surrounding instructions through both call sites, the imported symbol
metadata, the actual KptJal encoder/code definitions and the native text
window/resource interfaces.

`CodePushOff.v:74–76` identifies `push_off+0x10`, JAL x1 immediate3370,
word0x52b000ef. Lines86–88 identify `push_off+0x18`, immediate3362,
word0x523000ef. The imported symbols are push_off=0x80000b80 and
mycpu=0x800018ba; both stated signed-immediate target equations agree with
those source locations. Four-byte base instruction ownership and two-byte
PC alignment match the actual KptJal resource contract.

The four pure fields require actual encoder equality, target equality,
alignment and every source-map byte. The byte index is explicitly Nat,
so the bounded window introduces no unintended negative offsets. There
are no default bytes or assumed decoder results.

The native resource field can derive the exact window from persistent
identity source text, weaken its tier to either requested tier, and apply
the native KptJal window constructor with the proved encoding/alignment.
It retains the original identity text. No physical-table ownership,
configuration, execution WP, fetch response or code-resource assumption
is smuggled into the input. No Platform or native invariant instance is
needed for this pure ownership conversion.

This interface produces resources for either selected call site. It does
not claim that push_off reaches either site, executes a call, preserves
interrupt state or implements the whole function. Proof implementation
and full declaration audit are separate; the coordinator reported the
signature target GREEN590 jobs. No changes requested or made.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
