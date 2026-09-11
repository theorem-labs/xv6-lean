# Concrete mycpu fetch footprint

The two MycpuFetchBytes modules certify all 34 ELF-loaded bytes needed by the
pinned model's aligned fetch path for the 14 instructions in mycpu. The body
itself is still exactly 32 bytes. At the final compressed JR address
0x800018d8 the model reads four bytes, yielding 0x11018082; the following bytes
01 11 come from the actual ELF rather than an expected-code fallback.

The width definition uses the actual is_aligned_vaddr query. ziccif_enabled
proves the generated currentlyEnabled Ext_Ziccif query returns pure true for
this stock model. Every base instruction here is four-aligned, so this concrete
body does not require a split uncompressed fetch. The deduplicated union of
all concrete read windows is exactly List.range 34. Each full read word is
proved against loadedRam; its low halfword and, for base instructions, full
word agree with the existing decode certificate.

Validation: the target Xv6.Kernel.MycpuFetchBytesProofs passed 456 build jobs.
An opaque-body, type and constructor dependency audit checked all 25 logical
declarations with only propext, Classical.choice and Quot.sound, no unsafe or
partial logical dependencies, and zero excluded roots.

This is a byte/layout certificate and one pure extension-query equality.
It does not prove the ELF symbol parser, virtual-to-physical translation,
code ownership, the complete generated fetch program or mycpu's function WP.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
