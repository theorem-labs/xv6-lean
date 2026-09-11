# Separate durable link checks

`DurableLinksDefs` ports exact FsImg.v3337–3440: `linksEqual` checks exact link
counts only for live non-directory records; `rootNoSelf` accepts a live root-self
entry only under the two dot names. The latter keeps source branch order and
reads the name only for a live entry naming inode1. Neither modifies initial W9.

The two source bounded projection lemmas are proved. `DurableLinksImage` proves
both source sweeps on the actual pinned disk using the checked ordered ticket list
and full1024-byte root-directory data equality. Build241jobs; leaf5.3seconds;
all imported filesystem and inode-certificate theorem cones checked against the
standard-three axiom allowlist.

These are prerequisites to the durable filesystem composition, not that full
composition itself. The source tokenless-entry bridge remains subsequent work.

Authorship note: researched and written by OpenAI Codex on Jason Gross's behalf.
