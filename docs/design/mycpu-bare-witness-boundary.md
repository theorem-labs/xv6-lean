# Concrete operational Bare mycpu witness

This witness starts in an explicitly configured supervisor machine, with the
actual `Xv6.Machine.bootImage` RAM. It does not claim that the real boot path has
reached this configuration or that its native Iris resources have been allocated.
The source body is the fourteen instructions at 0x800018ba, including the real
34-byte aligned-fetch footprint; generated `cycle false` performs each complete
fetch, decode, execute and retirement. Choosing false is one permitted clock
choice, without restricting the machine relation.

CPU 3 starts with TP=3, SP=0x80040000, RA=0x80000100, and S0=0x123456789abcdef0.
The two stack words at SP-8 and SP-16 start at zero in the actual zero-filled
RAM beyond the ELF's file-backed interval. All other GPRs initially use their
zero default. MISA, MENVCFG, supervisor privilege, active state, SXL=2, SIE=0,
MPRV=0, MXR=0, SATP Bare, zero interrupt enables, and a readable/writable/
executable TOR entry covering RAM are explicit fields. PMA is exactly pmaBoot.
The initial log is empty, its view is zero, and all reservations are absent.

Use the existing sound `pauseRun` to run actual register and ordinary RAM-read
events until each real write boundary. A bounded outer evaluator permits only
ordinary RAM writes with actual present payload, appends the exact snapshot and
hart author to the real TSO log, updates physical RAM, and resumes the retained
continuation. Every accepted write is justified by NodeStep with the other-hart
reservation set empty. Reads use `Memory.read` at the current fixed view, so the
two restores observe the hart's own writes even above view zero. The evaluator
rejects unsupported effects; this does not narrow NodeStep. Each of fourteen
cycles is separately checked and composed with the actual restart transition.

A small transparent read cache specializes the known 34 ELF bytes and the
zero-filled RAM interval. Its total map is proved equal to loadedRam bootImage;
all other addresses retain the real ELF fallback. Thus no alternate code image
or unchecked byte oracle enters the witness. Kernel certificates compare the
actual generated execution to compact register checkpoints, including retirement
counters. The two store requests retain actual metadata and return types.

The final contract includes the existing MycpuBare.Result, exact RA/S0/SP
restoration, A0=0x80012568 for CPU3, two actual log messages, saved entry values
in the physical stack words, and preservation of the complete 34 code bytes.
NodeSteps are lifted through the existing writeBack/fixed-thread PoolSteps
lemma, preserving every other hart and all device state. No WP adequacy or
supervisor resource-inhabitation claim follows from this existential run.

Owned prefix: Xv6/Kernel/MycpuBareWitness*.lean and STATUS. Defs/Spec are reviewed
before proofs. Every certificate uses Lean's kernel, and every physical-origin
declaration is audited through types, opaque bodies, and constructor fields.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
