# Actual mycpu image and decoder review

The coordinator read all four modules and checked the source instruction
sequence against CodeMycpu. The 456-job target build passes. The independent
combined prerequisite audit checks all 65 declarations from these modules,
including complete opaque-body, type and constructor dependencies. Only the
standard three axioms occur; no unsafe/partial dependencies or exclusions.

The complete 32-byte body is read from the actual imported ELF at file offset
0x28ba and tied to the actual boot RAM at 0x800018ba. Fourteen mixed-width
rows cover every byte, and their machine read values and RVC tags are checked.
The generated decoder returns the actual AST at every row. The twelve
compressed instructions then produce the exact ExecuteAs expansion; the base
rows already have their normalized form. The AUIPC/ADDI immediates compute
0x800123e8. This does not certify ELF symbol-table parsing.

The sufficient configuration is the source's full MISA_C constant and, for
the two base rows, Supervisor with MENVCFG_S = 0xA000000000000000. Every
unmentioned register is arbitrary. The generic compressed rule under only
misa.C remains a separate generalization; the full constant is already the
production hardware contract. No supervisor fetched execution, native code
ownership, page translation or complete function WP is claimed.

Approved as the exact image/decode prerequisite.

Reviewed Lean source hashes (SHA-256):

```text
7f5d89da08c4f79f89f3bdc820d33ca92ab401b9824e30497037b1ffee2dbfb0  Xv6/Kernel/MycpuDecodeDefs.lean
e12240a7cd9bded7cd9d8bf49dbb471fca88707fa8b840b674acd1faa8643add  Xv6/Kernel/MycpuDecodeCertificates.lean
57f1d0284b37a2a29227098ae78d437ee179efd06b2dd4de9185394496e0b431  Xv6/Kernel/MycpuDecodeProofs.lean
ea9329856bb2237f28ac0ede44e113df8a9c4811f93aae1198ec1971455be8d1  Xv6/Kernel/MycpuDecodeImage.lean
```

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
