# Independent filesystem recovery review

Reviewed all six frozen Recovery modules and all 27 public contract laws against
LogDefs43–67/155–164 and FsCrash349–354/460–464/844–850 at the paper source pin.
The decoder is total and unclamped; missing words assemble to zero. Installation
right-folds indices, so the first index wins on duplicate destinations. HeaderWF
retains the exact count, distinctness, coverage/log exclusion and superblock
exclusion clauses. Recovery is defined on arbitrary physical views without
requiring HeaderWF; validity is used only in the laws that need it.

The recovery view falls back to raw physical blocks. The exception set contains
all decoded destinations even for equal payloads. Fullness, exact home domain,
readback/restriction, unchanged blocks, log-slot payloads and the raw superblock
are derived with their stated premises. Kernel-checked fixtures cover short and
unclamped headers, duplicate order, changed and equal payloads, full blocks and
absent raw fallback; neither fixture introduces a native_decide axiom.

A fresh independent audit checked all 128 logical declarations across six
physical modules, including private helpers, transitive types, opaque bodies
and constructors. Only propext, Classical.choice and Quot.sound occur; zero
exclusions, unsafe/partial dependencies or Initial allocation dependencies.
Evidence: RecoveryPeerAudit.lean and recovery-peer-audit.log under
/tmp/xv6-lean-research.

PASS for the exact pure recovery algebra. Runtime disk-resource carving, native
recovery boot installation, preservation of HeaderWF over crashes and the final
filesystem theorem remain separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
