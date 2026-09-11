# Actual Bare fetch-bytes composition

Root owns SupervisorBareFetch{Defs,Spec,Plan,Proofs,Link}+STATUS. Compose actual
fetch_bytes through its pure extension check, actual Bare translateAddr, actual
outer mem_read effective-privilege reads, checked physical fetch and actual
FetchBytes_Success constructor. Keep checked fetch widths two/four and exact
width-specific alignment; arbitrary fetch-start value and granule value remain
separate. Do not skip actual register reads or replace the program with a trace.

A single seven-cell fractional footprint contains mstatus, current privilege,
satp, PMA regions, PMP cfg/address arrays and HTIF base. Translation and outer
access reuse the same status/privilege cells sequentially. The proof widens
already proved finite register plans and the actual OneRead boundary; it does
not duplicate cells by separating overlapping footprints. Eleven actual
register reads precede the same one real read event. No writes occur.

Explicit configuration: Supervisor, SXL=2, satp Bare, TOR RAM and matching
executable PMA, HTIF disabled, and width-specific alignment. Fetch needs no MPRV
restriction. Other status/satp fields stay arbitrary. Native WP uses actual
context byte-window ownership and derives all-view readability internally,
returning the unchanged seven cells, running context, same word and chosen-view
receipt through the real guarded continuation. No new camera or oracle.

The result is only actual fetch_bytes under the explicit Bare tier. The outer
fetch selection/PC reads/compressed decoding, actual KPT translation and the
source supervisor function specification remain subsequent composition work.
No full xv6 function theorem may be claimed from this Bare result.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
