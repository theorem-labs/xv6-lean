# Actual xv6 mycpu bytes and mixed-width decoding

The four `MycpuDecode{Defs,Certificates,Proofs,Image}.lean` modules certify the complete 32-byte body at concrete address `0x800018ba` against the imported full kernel ELF and the actual generated LeanPaperStock decoder. The fourteen rows cover all 32 bytes exactly, with twelve compressed instructions and two 32-bit instructions. This is a byte/decode prerequisite; it does not assert a supervisor instruction WP, kernel-text ownership resource, successful execution of the memory operations, or correctness of mycpu.

| Source lemma | Offset | Width | Encoding | Normalized operation |
|---|---:|---:|---:|---|
| `myi_00` | 0x00 | 2 | 0x1141 | ADDI sp,sp,-16 |
| `myi_02` | 0x02 | 2 | 0xe406 | SD ra,8(sp) |
| `myi_04` | 0x04 | 2 | 0xe022 | SD s0,0(sp) |
| `myi_06` | 0x06 | 2 | 0x0800 | ADDI s0,sp,16 |
| `myi_08` | 0x08 | 2 | 0x8792 | ADD a5,zero,tp |
| `myi_0a` | 0x0a | 2 | 0x2781 | ADDIW a5,a5,0 |
| `myi_0c` | 0x0c | 2 | 0x079e | SLLI a5,a5,7 |
| `myi_0e` | 0x0e | 4 | 0x00011517 | AUIPC a0,0x11 |
| `myi_12` | 0x12 | 4 | 0xb2050513 | ADDI a0,a0,-1248 |
| `myi_16` | 0x16 | 2 | 0x953e | ADD a0,a0,a5 |
| `myi_18` | 0x18 | 2 | 0x60a2 | LD ra,8(sp) |
| `myi_1a` | 0x1a | 2 | 0x6402 | LD s0,0(sp) |
| `myi_1c` | 0x1c | 2 | 0x0141 | ADDI sp,sp,16 |
| `myi_1e` | 0x1e | 2 | 0x8082 | JALR zero,0(ra) |

The mapping follows the complete pinned `iris/CodeMycpu.v` at `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. `kernel-rocq/KernelSyms.v:79,230` supplies the source names for the concrete mycpu and cpus numbers, but these modules do not treat those names as certified ELF symbols. `cpus_literal` checks that the AUIPC instruction's concrete PC, its 0x11 immediate and the ADDI's signed 0xb20 immediate compute `0x800123e8`.

## Actual image and decoder contracts

`file_bytes` proves all 32 lookups at ELF file offset `0x28ba` against `Images.kernel`. `ram_byte` and `ram_bytes` use the existing parsed-ELF file-window and actual boot-image theorems. `layout_complete`, `span_bound`, `word_bytes`, and `instruction_bytes` then prove the exact complete layout and every modular two-/four-byte machine read from `loadedRam Xv6.Machine.bootImage`. No missing image byte is replaced by the expected code table. These image facts have no register-state assumption.

`decode00` through `decode13` separately kernel-check the actual generated `ext_decode_compressed` or `ext_decode`, including `encdec_compressed_backwards` and `encdec_backwards`; they are not certificates for an independent decoder. `decode_certificate` combines all fourteen cases. `compressed_tag` checks the actual `isRVC` classification. Compressed decoding returns the raw `C_*` AST. `compressed_expansion` separately proves that actual `execute` returns `ExecuteAs` with the normalized AST from CodeMycpu, for arbitrary Platform parameters. It does not execute that resulting base instruction.

The explicit sufficient per-row configuration is:

- Compressed rows: `misa = 0x800000000014112d`, with all other registers arbitrary.
- Base rows: current privilege Supervisor and `menvcfg = 0xa000000000000000`, with all other registers arbitrary.

The two base decodes retain actual eager Zicfilp matching reads through `get_xLPE`; the supervisor value has LPE clear. `snapshot_covers` connects every supplied snapshot register to the actual dependent register file, and `decode_plan` uses the existing sound evaluator-to-`EventWP.Returns` bridge, with no read-memory oracle. `source_config` and `decode_supervisor_plan` provide the uniform three-field source configuration for all rows. These plans preserve the entire register file.

The constants are the source's `MISA_C` and `MENVCFG_S` in `iris/RiscvFetchExec.v:202–225`. The former is its model-reset misa and persistent hardware configuration; the latter is explicitly pinned by supervisor `IntrDefs.sconf` at line 595 onward. MENVCFG_S enables ADUE (bit 61, Svadu) and STCE (bit 63); PBMTE and LPE remain zero. The individual upstream compressed `kd_*` lemmas admit the weaker premise `misa.C = 1`; that more general bit-only theorem remains separate work. The present full-MISA specialization is sufficient for the source production configuration and is not represented as that generic theorem.

## Validation

`PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.MycpuDecodeProofs Xv6.Kernel.MycpuDecodeImage` passes all 456 jobs, with the final proof module taking 2.0 seconds. Proof construction uses ordinary kernel equality/decision checks, not native decision procedures.

The fresh physical-origin audit checks all 65 declarations in all four modules, including private helpers, and explicitly traverses opaque theorem bodies (`info.value? (allowOpaque := true)`), types and inductive constructors. It has zero exclusions. Only `propext`, `Classical.choice`, and `Quot.sound` occur; no unsafe or partial semantic dependency occurs. No `sorry`, new axiom, unchecked execution, source-resource premise or preservation oracle was introduced.

Evidence: `/tmp/xv6-lean-research/MycpuDecodeAudit.lean`, `mycpu-decode-audit.log`, and `mycpu-decode-build.log`. A symbolic C-bit-only normalization probe was stopped for cost; it is not validation evidence for the final specialization.

*Authorship note: this was researched and written by an AI coding agent (OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is posted from this account.*
