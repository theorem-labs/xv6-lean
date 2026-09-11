# Independent mycpu fetch-byte review

Result: PASS for frozen `Xv6/Kernel/MycpuFetchBytes{Defs,Proofs}.lean` and STATUS. The sail-audit agent independently checked the full definitions, proofs, imported decode/image certificates, and generated `LeanPaperStock/Fetch.lean:216–276`. No production Lean files changed.

The fourteen instruction starts use the actual generated address-alignment query. `ziccif_enabled` proves the pinned model's extension query is pure true. Generated fetch consequently requests four bytes at aligned starts, even for compressed instructions, and two bytes otherwise. Both uncompressed instructions here are aligned, so neither requires the second half of the split base-instruction path. This statement is about these concrete starts; the general generated split path remains present.

The expected footprint is exactly 34 bytes, including the two bytes after the 32-byte function body. The kernel-checked `file_bytes` theorem checks every byte against the imported actual ELF at file offset `0x28ba`, and `ram_byte` carries that equality through the existing boot-image loader theorem. It never fills missing addresses with the expected code table. The fourteen read windows cover exactly all 34 byte offsets; each requested width is two or four, and every full little-endian read word is proved with the actual `readBytes` function over `loadedRam`.

The full read words agree with the original instruction encodings in their low halfword and, for uncompressed instructions, their complete 32-bit word. Together with the imported `MycpuDecode.compressed_tag`, this proves the generated `isRVC` tag agrees with the instruction table. I separately replayed that composed tag theorem for every index. Additional kernel checks confirm the final start is `0x800018d8`, and offsets 32 and 33 contain `01 11`. The checked final read is four bytes with value `0x11018082`.

The scope statement is accurate: this proves a concrete byte/layout certificate and the extension query. `fetch_bytes` still performs its extension check, translation, and memory read; this review does not certify those operations, arbitrary repeated PC reads, live code ownership, full fetched execution, the ELF symbol parser, or the function WP.

Fresh validation: `/tmp/xv6-lean-research/MycpuFetchBytesAudit.lean` checked all 25 physical-origin logical declarations and all transitive type, opaque-body, and datatype-constructor dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` occur; no unsafe or partial logical dependency and zero excluded roots. `/tmp/xv6-lean-research/MycpuFetchPeer.lean` independently checked the composed fetch-tag and boundary facts using kernel proofs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
