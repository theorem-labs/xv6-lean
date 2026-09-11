# Mycpu register-packet adapter

FROZEN: all thirteen pure and one native contract are implemented in five
modules (Defs, Spec, Pure, Proofs, Link). `nativePureSpec`, `nativeSpec` and
`registrySpec` are actual proof constructors.

The nine scalar bodies and final compressed return occupy image indices
0/3/4/5/6/7/8/9/12 and 13. The actual generated execute/ExecuteAs programs use
the existing scalar and return RegisterPlans, widened to the same fifty-key
packet. No read, write, success hypothesis or body WP is substituted.

Each scalar changes one explicitly mapped typed GPR (SP/S0/a5/a0); return
changes only nextPC to the real low-bit-cleared RA. Exact full-entry overlay
equalities are proved, and the native fold reconstructs the updated pinned
software map, original SIE/SRET/off resources, x0 fact and unchanged KPT
residue. Return retains its actual Supervisor/LPE-disabled/C-enabled facts;
scalar bodies require no hardware-value premise.

The literal frame preserves context, reservation and virtual save words at
fixed addresses across SP changes. There is no silent word reindexing. The
later all 14 family needs a fixed save-area anchor, normally entrySP−16.
Fetch, retirement, full cycle/function composition and source sconf remain
separate. The final returned-body continuation is the genuine WP premise.

Validation:
`PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.MycpuKptRegisterLink`
passed 890 jobs (Pure 10 s, Proofs 1.0 s, Link 901 ms). Fresh full physical-origin
inspection audited all 118 declarations in five modules, including complete
opaque bodies, types and constructors: standard propext/Classical.choice/
Quot.sound only, no unsafe/partial dependency and zero exclusions.
Research logs are `mycpu-kpt-register-build.log` and
`mycpu-kpt-register-audit.log`; exact source/contract mapping is in
`docs/design/mycpu-kpt-register-boundary.md`.

No frozen dependency, generated model, umbrella or registry was edited.

Coordinator final peer review also passed: all implementation files read and
a fresh full audit checked 118 physical declarations through types, opaque
values and constructors, with standard axioms only and zero exclusions.
The corresponding peer report is in docs/reviews.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
