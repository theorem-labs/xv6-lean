# Checked supervisor PTE reads

This boundary proves the actual generated read_pte and read_pte_exclusive
wrappers at width eight, through mem_read_priv, metadata drop, and the
complete checked_mem_read prefix. It uses the existing four-cell partial
footprint: PMA regions, PMP config/address arrays and HTIF base. Supervisor
is the wrapper's explicit privilege argument; no cur_privilege/mstatus
read is invented, and no full register snapshot is assumed owned.

The Config retains the source TOR grant, aligned RAM range, actual PMA
match/read grant and disabled HTIF. Alignment is explicit because the pin
predicate alone does not impose it; the later page-tree path must supply
it. The actual PMA priority, split handling, PMP check, eager MMIO tests,
read-kind selection and singleton byte assembly remain in the program.
Both normal and exclusive modes use the same checked prefix with their
actual res flag and actual Read_plain/Read_RISCV_reserved request.

A finite boundary reaches the real V1 event while preserving all success
tag and error tails. Normal reads use the native pinned-read event rule:
the actual returned word has canonical equality to the reference and exact
equality for an interior PTE. The physical byte-value function is separate.
Exclusive rereads use native physical ownership to return the actual word
and snapshot reservation while preserving all original slot anchors and
payloads, without a publication credential. Each real memory event pays
one guard and returns its view receipt. Register-only prefixes preserve
the complete four-cell bundle.

The public Spec contains no caller read-success or instruction/body
correctness hypothesis. These direct rules do not yet open a shared KPT
invariant; that accessor must close independently at each actual event.
Page-tree allocation, TLB coherence, leaf validation and the complete
hardware walk remain subsequent source obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
