# Spinlock integration image independent review

Reviewed the root-authored frozen `SpinlockImageDefs.lean` and
`SpinlockImageProofs.lean` against the actual `BootImage`, `loadedRam`,
`readBytes`, address-addition, and footprint definitions. Result: pass for
the declared image/byte/separation scope.

The image contains 68 explicitly listed bytes. All seventeen consecutive
four-byte reads at `0x80000000 + 4*i` are proved equal to their claimed
little-endian words, using the actual loaded RAM map. `loadedRam` retains
the real platform RAM bounds; the image does not redefine the RAM domain.
The image's byte function supplies zero outside its 68-byte code interval.
The lock and counter four-byte words at `0x80001000` and `0x80001004` are
therefore both zero initially. The separate checked instruction-address,
RAM-bound, code/lock, code/counter, and lock/counter lemmas concern the full
modular byte footprints and do not merely compare their base addresses.

I manually checked the intended instruction layout in conjunction with the
actual decoder certificates: the first CSR reads `mhartid` into x5; the
unsigned selector and branch send IDs at least two to the final JAL self-loop.
AUIPC at offset 12 followed by ADDI -12 computes the lock address. The
acquire AMOSWAP word uses x15 for both input and returned old value; its retry
branch returns to the preceding move from x14. The counter accesses use
lock+4. `FENCE rw,w` precedes the zero store to the lock, and the final
backward JAL returns to the retry setup. These are checks of the intended
AST/offset layout, not proofs of execution, mutual exclusion, or safety.

This is a new test image on the existing machine, not the pinned kernel ELF.
It requires no assembler-correctness premise: the displayed literal bytes
are the image being proved. Fetch/execution plans and the full eight-CPU
safety theorem remain separate work. In particular, “two-hart” describes the
intended selector behavior and does not remove other machine CPUs.

Independent validation of the image:

- `python3 tools/lake.py build MachCSL.Machine.SpinlockImageProofs`: passed
  109 jobs.
- `/tmp/xv6-lean-research/SpinlockDecodeAudit.lean`: checked all 159 physical
  logical declarations across image and decoder modules, including private
  helpers; recursively checked type and body dependencies. Standard
  `propext`, `Classical.choice`, and `Quot.sound` only; no unsafe/partial
  semantic dependencies and no runtime companions excluded.

The reviewer independently read the root-authored image modules. The same
reviewer subsequently corrected and implemented the adjacent decoder
certificates, so the latter are covered by implementation validation in
`SpinlockDecodeSTATUS.md`, not claimed as an independent decoder review.
The reviewer also previously contributed underlying memory/boot proofs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
