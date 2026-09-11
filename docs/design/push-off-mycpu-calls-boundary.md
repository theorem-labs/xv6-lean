# Source text for the two push_off mycpu calls

The five `PushOffMycpuCalls` modules prove the exact two source call-site
encodings, target/alignment geometry and native instruction-resource
production. This is a resource theorem with no execution WP dependency.

`CodePushOff.v:74–76` specifies the call at push_off+0x10 as JAL x1 with
immediate3370 and encoding0x52b000ef. Lines86–88 specify push_off+0x18,
immediate3362 and encoding0x523000ef. Imported symbols place push_off at
0x80000b80 and mycpu at0x800018ba. The pure target theorem checks both
actual sign-extended JAL additions, and the encoder theorem checks the
actual JAL bit layout. The byte theorem checks all four Nat-indexed source
map lookups at each site, against the encoded word's little-endian bytes.

The native proof retains persistent identity kernel text, weakens it to
the requested tier, extracts the exact four-byte virtual window, and
applies `KptJal.nativeResourceSpec.window` using the checked alignment and
encoder equality. It returns the original text and actual tier-indexed
JAL code. It requires no physical-word input, decoder-success assumption,
translation configuration, invariant instance or component execution WP.
The proof imports the already-built KptJalResources module, not the
separately compiling full JAL decoder/native Link.

The public native constructor supplies all four pure contracts and the
single resource contract. Actual call execution, reaching these sites,
push_off's interrupt-state transition, remaining instructions and full
function correctness remain separate.

Pinned-source SHA256 values:

```text
e3269c7fabec63b67a405608016a77041b7b1ccc23efce56247fcd4463ea6560  iris/CodePushOff.v
ff91c7ea4ccd8f33604675499a39f37a994ebaa87b5cf2be3a700500b32e99d0  kernel-rocq/KernelSyms.v
b694faf4d40d45bbe954d670b45ac825be633bbdc5be02235c4138ffb05609f5  kernel-rocq/KernelInstrs.v
```

The source and generated input manifest is recorded at
`/tmp/xv6-lean-research/push-off-mycpu-calls-sources.sha256`.
No generated or upstream source file was edited.

Validation: final native build passed1,134 jobs; strict fresh audit checked
all34 physical declarations across five modules, including full type,
opaque-body and constructor cones. Only the standard three foundational
axioms occur, with no unsafe/partial dependencies and zero exclusions.
Audit script/log: `PushOffMycpuCallsAudit.lean` and
`push-off-mycpu-calls-audit.log` in the same research directory.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
