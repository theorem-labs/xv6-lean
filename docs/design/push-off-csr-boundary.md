# Disabled CSR execution boundary

Source: push_off+0x0a, row5 of the pinned PushOffCode table, with CSRImm
(0x100,2,x15,CSRRC). The generated doCSR checks access, reads old supervisor
status, writes its SIE-cleared value through legalize_sstatus, then writes
the old supervisor status to x15. The output is Retire_Success for the
owned source Supervisor/MISA configuration.

The native rule takes the actual common50 disabled packet at an arbitrary
actual Bare/KPT regime. Configuration states only Supervisor privilege and
the full source MISA. Existing MS ownership and same-name half/eighth SIE
agreement derive MsFacts and SIE0 internally. The separate legalizer's
native off_plan discharges the actual program. No caller gives a CSR
success, evaluator certificate, component WP, MS identity assumption or
physical register file beyond its actual packet ownership.

The implementation keeps read_CSR and write_CSR as separately factored
actual programs, avoiding eager expansion of the full generated CSR
switches in monadic composition. read_status_plan and write_status_plan
retain full-width slice normalization and all real reads/writes. The
concrete access-check certificate has a MISA-only snapshot and a private
transfer proof rejecting writes, memory events, missing values and unowned
reads. The ordinary kernel checks its Eq.refl term.

The physical MS write requires full ownership even when its value is
unchanged. All MS ghost fragments and arbitrary saved landing-pad fields
therefore remain tied to the same value. after_entry proves equality over
all180 physical registers, and pure GPR facts preserve x0 and pinned TP.
The body theorem restores all50 cells, translation residue and literal
frame; it does not retire an instruction or assert enabled-state behavior.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
