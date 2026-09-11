# Independent review: timestamp-bounded TSO reads

Reviewed by the independently assigned Codex Sail/filesystem agent. **PASS**:
no source or proof correction requested in the frozen `TsoReadAtDefs`,
`TsoReadAtProofs`, and `TsoReadAtLink` modules.

The source comparison is xv6iris `arxiv-v1`
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, `iris/TsoCtx.v:6262–6283`
(`ledger_read_at_ok`), together with the actual timestamp invariant and
`tso_read_of_latest`. The new bridge provides the sufficient source case where
the view receipt is at the owned timestamp. It retains arbitrary timestamp
payloads and uses heap authority to identify the latest value with the owned
byte. Native view authority proves that the reader's current view is at least
that timestamp; every permitted later view therefore sees the latest byte.

`window_read` obtains both resources at each index of the same byte range and
uses a single read view throughout. Addresses retain the actual modular physical
address addition, with no extra alignment or range premise. `power_read` obtains
the current era using the actual generation certificate and `ThreadLive`
condition. The registry wrapper uses the existing shared machine capacity and
introduces no ghost slot or assumed interpretation.

This is a visibility bridge, not an event WP or the complete source context
API. In particular, the separate own-author forwarding arm of source
`ledger_read_at_vis_ok` is not claimed by this module. The source's general
two-time premise `t ≤ F` is specialized here to a receipt at `t`; this is a
stated API scope, not a restriction of machine read behavior.

Independent validation: `python3 tools/lake.py build
MachCSL.Logic.TsoReadAtLink` passes (423 jobs). A fresh physical-origin audit
checks all **6 declarations** from the three modules and follows their complete
type, body, and referenced constructor-field dependencies. Only `propext`,
`Classical.choice`, and `Quot.sound` occur; no unsafe or partial semantic
dependency, and zero excluded declarations. The audit source is retained at
`/tmp/xv6-lean-research/TsoReadAtIndependentAudit.lean` in the working environment.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
