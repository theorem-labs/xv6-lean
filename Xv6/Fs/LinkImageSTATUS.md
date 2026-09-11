# Directory tickets and image link validity

Source: `xv6iris` tag `arxiv-v1`, commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, `FsDurImg.v` §9d–h.

`LinkDirectoryProofs.lean` ports the generic §9e inclusion over the native
`FsLink.FamilyRA`. `view_ops_incl` takes an arbitrary byte reader, inode,
orphan flag, ticket function, value/type functions, excluded name, and
record count. Its premise applies only to records that win their name,
differ from the excluded name, and owe a token. The conclusion includes
the map's token product in the exact ordered ticket-list fold.

The first-winner map is unchanged. The proved `dirView_succ` equation
bridges its ordered list representation to the source's one-record map
recursion. Insertion factors a camera element only when the key is fresh.
The proof handles losing records, the excluded name, tokenless entries,
and charged entries separately. It imposes no directory-name uniqueness
or additional well-formedness assumption. `view_ops_incl_tickets` uses the
existing exact `recTicket`, including its self-inode exemption.

`LinkImageProofs.lean` closes the source image theorem:

```
image_link_valid image sb nib
  (fsimgValid image sb = true)
  (regionValid image sb nib = true)
  (linksEqual image sb = true)
  (rootNoSelf image sb = true)
  (sb.ninodes ≤ 16 * nib)
:
✓ (elem (imageNodes image sb nib) (imageChoice image sb)
    • tokElem 1 (imageValue image sb 1))
```

The camera validity is proved, not assumed. The argument isolates the
root as the only directory, separates its dot token, bounds ordinary
directory tickets by the whole filesystem's tickets, and covers both the
dot token and the extra root token with the root's multiplicity two.
Nonroot live files use the checked link-count equality; all rounded-region
inodes, including free ones, remain in the map. The underlying supply
retains the distinction between present empty fragments and absent keys.

The theorem retains all five source premises. The source's executable
`ent_tokenless` exempts every nondot self-target, so `rootNoSelf` is
redundant in this particular inclusion proof; it is explicitly retained
and remains part of the full initial-image contract. No prose claim about
a narrower exemption is substituted for the executable formula.

For §9d's image reader transport, the existing checked
`imageNode_data_all` and `imageNode_dirEntries` give exact equality of the
node and image readers. This avoids the source's intermediate bounded
byte-window lemmas without changing the final map or imposing a new
premise. Those general window-agreement API wrappers are not exported by
this module. `bootImage_link_valid` projects the five inputs from the
already ported fifteen-premise `BootImageWF`.

Both proof modules are generic and import no literal image data.
Validation: `python3 tools/lake.py build Xv6.Fs.LinkImageProofs` passed
245 jobs. The directory and image proof modules took 1.1 and 1.2 seconds.
Their enforced audits cover 22 and 17 namespace declarations. A separate
physical-origin audit covers all 40 declarations, including the generated
`dirTicketsAt.eq_1` equation; all transitive axioms are among `propext`,
`Classical.choice`, and `Quot.sound`, and no unsafe/partial logical
dependency occurs. No `sorry`, custom axiom, `native_decide`, or
`bv_decide` is used.

The thin concrete leaf `LinkImage.lean` exports
`Xv6.Fs.Image.link_family_valid` for the actual checked mkfs image and all
208 rounded-region inode records. It applies `bootImage_link_valid` to
`Image.boot_image_wf`; no bytes are regenerated or recertified. Local
irreducibility attributes stop elaboration from unfolding the complete
literal map and have no effect on the theorem's kernel meaning. The leaf
build passed 467 jobs, taking 735 milliseconds for the new module. The
combined physical-origin audit passed all 41 declarations in the three
modules and their complete type/body dependency cones, including this
concrete theorem, with only the three standard foundational axioms.

This discharges the link-family component of the later durable snapshot
tie, including its extra root token. The complete `snap_bytes`/`snap_ok`
bundle still needs its other byte, bitmap, ownership/disjointness, and
coverage clauses, followed by the native ownership allocation/transport
proofs. No complete snapshot or kernel correctness theorem is claimed.
Frozen `FsLink`, `LinkFamily`, `LinkSupply`, and image files were unchanged.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
