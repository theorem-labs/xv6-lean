# Actual xv6 boot-image specialization

`Boot.lean` instantiates the shared `MachCSL.Machine.BootImage` with the actual
pinned kernel ELF. Its vector comes from the successfully parsed header; the
checked value is `0x80000000`. Its bytes come from `Elf.loadedImage Images.kernel`
and default to zero outside that image. Conversion from image `UInt8` bytes to
machine `BitVec 8` bytes preserves their unsigned value.

The 36 explicit public theorems cover:

- Parsed entry and contiguous-list parser/image correspondence.
- The one actual PT_LOAD file range: address `0x80000000 + j` maps to ELF byte
  `4096 + j`, for `j < 41632`. Coverage proves these bytes are present, so the
  default is unused there.
- BSS through `0x80000000 + 144840`, then free RAM, are zero. The RAM map contains
  exactly physical addresses in `[0x80000000, 0x88000000)` and no addresses outside.
- Actual boot runs for all eight harts, unchanged RAM/devices during the register
  initialization run, PC/nextPC at the parsed entry, and computed MISA
  `0x800000000014112d`. The public boot predicate still permits arbitrary initial
  register files; this module supplies one proved witness.
- BootFacts/BootShape, memory and reservation invariants, real power-on
  transitions, and boot-state existence for every incoming durable disk and
  advertised capacity.
- The actual packed fs.img as an integer-indexed disk, zero outside the file,
  with a proved contiguous-list lookup bridge. Reboot preserves the incoming live
  durable disk; initial-image equality is propagated only when it held beforehand.

Source mapping at `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`:
`ElfFile.v:274–309` (entry/loaded image), `RiscvLang.v:974–1024,1325–1382`
(image defaulting, boot facts and shape), `PowerBoot.v:161–167` (boot-state witness),
`FsImgDisk.v:47–69` and `SystemAdequacy.v:1087–1094` (initial disk and zero padding).
There is no `SystemBoot.v` at this pin.

The upstream language uses a filtered union of dumped `KernelInstrs.kernel_bytes`
and `KernelData.kernel_data`, defaulted to zero. `Correspondence.lean` now proves
that this specialization using the actual parsed ELF has identical bytes at every
integer address, and that the complete boot images agree. It uses the independently
imported source maps and `Xv6.Kernel.fileBytes_eq_fileImage`, preserves the source's
upper-only filter at `0x8000a2a0`, and proves that the BSS/default contribution is
zero. The checked input correspondence is described in `Xv6/Kernel/STATUS.md`.
This module does not
claim kernel safety, ELF instruction decoding correctness, filesystem-image
well-formedness, the full reset postcondition for arbitrary initial registers,
or any exported system adequacy theorem.

Validation: `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build
Xv6.Machine.Boot` passed (1.7-second module). Enforced transitive axiom audit passed
all 50 imported `Xv6.Machine` theorems, including compiler-generated equations;
only `propext`, `Classical.choice`, and `Quot.sound` occur. No added axioms,
`sorry`, native decision procedure, or `bv_decide` was used. Temporary independent
audit driver/log: `/tmp/xv6-lean-research/Xv6BootAudit.lean` and
`xv6-boot-axioms.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
