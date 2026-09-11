# push_off mycpu call-site resources

FROZEN: five modules Defs/Spec/PureProofs/Proofs/Link implement all four
pure contracts and the native code-resource contract. Native Link GREEN
1,134 jobs (Proofs1.2 s/Link1.4 s). No execution WP or decoder-success
premise is required to produce any call site's resources.

All three actual sites at push_off+0x10/+0x18/+0x2c have checked encoder words,
target mycpu, alignment and all four source-map bytes. Persistent identity
source text produces actual code at either tier and remains available.
The former Fin2 scope covered only +0x10/+0x18. Their definitions are
unchanged at indices0/1; index2 now certifies the zero-depth branch call
+0x2c (3342/0x50f000ef). The unchanged native/pure proof bodies extend to
Fin3. Fresh extension build passes1,134 jobs. The proof imports
KptJalResources, without its full execution decoder Link.
No source/generated files were changed.

Fresh strict audit PASS: all34 declarations in five physical modules,
full types/opaque bodies/constructor cones, standard three axioms only,
no unsafe/partial dependency and zero exclusions. Logs/script under
`/tmp/xv6-lean-research`: `push-off-mycpu-calls-fin3-build.log`,
`push-off-mycpu-calls-fin3-audit.log`, `PushOffMycpuCallsFin3OwnerAudit.lean`.
Input source hashes: `push-off-mycpu-calls-sources.sha256` in the same
directory and `docs/design/push-off-mycpu-calls-boundary.md`.

Actual call execution, call-site reachability and full push_off correctness
are separate; no interrupt-state behavior follows from code ownership alone.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
