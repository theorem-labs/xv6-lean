# Kernel datum: complete independent peer review

Reviewer: OpenAI Codex subagent `lean_logic_audit`, reviewing all four
coordinator-authored `KernelDatum` modules (Defs, Spec, Proofs, Link), after
a separate agent's signature review. Result: **PASS for the declared resource
algebra scope**. All definitions and proof bodies were read; no implementation
correction was required.

The review read complete `Ktier.v`, `RiscvPtsto.v:1147–1262` and
`TsoCtx.v:608–640,805–870`. The two tiers and order match source KT0/KT1:
identity may weaken to full, with no converse. The identity pin states actual
PPN-plus-offset physical equality to the virtual address. Tier arguments are
explicit, so no ambient default silently removes this pin.

A byte retains every source `ctx_pointsto` conjunct: persistent native RW
mapping claim at `era.kernelMap`, positive Sv39-half bound, physical RAM
membership, tier pin, actual physical heap byte, matching timestamp fraction
with payNone, and the context's clean-or-dirty evidence. `physicalByte` reuses
the existing context camera and era names. No context ownership, physical
byte authority or timestamp is replaced by an ordinary pure assertion.
The arithmetic VPN, physical address and RAM predicates match source
extraction/concatenation and unsigned bounds. The positive-half lemma proves
canonicality; it does not broaden source data to negative canonical addresses.

The access wand captures only the persistent mapping/pin claim. It returns
the one existing physical byte and accepts one replacement byte, avoiding
linear duplication. Agreement first uses native mapping agreement to equate
the existential PPNs, then uses the physical byte camera across arbitrary
contexts and fractions. Identity access rewrites the physical address with
the owned pin. Tier weakening preserves the same context, fraction, mapping
and byte value. The word definition retains virtual eight-byte alignment and
all eight modular-address byte assertions; word weakening applies the byte
law pointwise. No physical-contiguity or translation-success conclusion is
assumed by these statements.

The Link constructs all five pure and seven native specification fields.
There is no function WP, translation WP, source capability, boot-installation,
RX text or virtual free-slot claim in this boundary. In particular the next
virtual-word/physical-word bridge must prove the page/offset geometry and
reassemble ownership; it is not supplied as a callback here. No camera or
registry slot is introduced.

Independent validation: `Xv6.Kernel.KernelDatumLink` rebuilt successfully at
653 jobs. A fresh audit checked all **96 physical-origin declarations** in
four modules, including private declarations and every type, opaque proof
body and constructor dependency. Only `propext`, `Classical.choice` and
`Quot.sound` occur; no unsafe or partial semantic dependency, zero exclusions.
All four SHA256 hashes remained unchanged throughout review/build/audit.
Evidence is retained under `/tmp/xv6-lean-research/KernelDatumPeerAudit.lean`,
`kernel-datum-peer-audit.log`, `kernel-datum-peer-build.log` and
`kernel-datum-peer-before.sha256`. At review time STATUS still described the
older interface-only checkpoint; the coordinator is updating that owned
record for this completed implementation.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
