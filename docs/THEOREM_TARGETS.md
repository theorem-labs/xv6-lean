# Exact theorem targets

This is the completion contract for the paper baseline, mit-pdos/xv6iris
`arxiv-v1`, commit `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
The Lean names below are reserved targets, **not implemented declarations**.
The Rocq excerpts are copied verbatim from the pinned files, from `Corollary`
through the statement's final period; their proof bodies are omitted.
They are the authoritative source statements, not compiler-ready Lean sketches.

There are four exports at the concrete `xv6Σ` in `SystemAdequacy.v`, plus two
active UART exports in `SystemUartAccepted.v`. All six interfaces are in scope.
The four-export count in the review does not exclude the UART results. Of the
six, the FS, observable-trace, and UART acceptance roots have no remaining
software-correctness or client-resource premise. “Closed” here still permits
exactly the displayed initial-state hypotheses and the documented foundational
and platform assumptions; it does not mean that the theorem has no parameters.

Generic invariant or trace theorems remain useful required interfaces. Proving
them, choosing `phi = True`, or leaving a function contract as a hypothesis
cannot count as completion of a concrete root. Porting a conditional UART
receipt result does not close the receipt-identification obligation that the
upstream file explicitly leaves open.

## 1. `xv6_power_adequacy_xv6Σ`

Conditional invariant interface; `Hphi` remains a client obligation.

Reserved Lean target: `Xv6.SystemAdequacy.xv6_power_adequacy`. Source: [iris/SystemAdequacy.v:1137](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/SystemAdequacy.v#L1137).

```coq
Corollary xv6_power_adequacy_xv6Σ (g : gstate)
    (phi : gstate -> Prop)
    (Hphi : forall (Hinv : invGS xv6Σ)
                   (γgen γstart γreg γd γsw γobs : gname) (T : list mobs)
                   (g' : gstate),
       ⊢ @power_interp xv6Σ
            (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
               (P_fs_named γd XV6_DISK_BYTES γsw γreg γstart fsimg_cov
                  (FsImg.sb_logstart fsimg_sb))
               γobs T (obs_pred_at γobs)) g' -∗
         ▷ P_fs_named γd XV6_DISK_BYTES γsw γreg γstart fsimg_cov
             (FsImg.sb_logstart fsimg_sb) -∗
         ◇ ⌜phi g'⌝)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (* THE ONE HYPOTHESIS LEFT, and it is about the HARDWARE SETUP, not the
       file system: the machine is switched on with the disk mkfs wrote. *)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall t2 g2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ phi g2.
```

## 2. `xv6_fs_adequacy_xv6Σ`

Concrete filesystem and machine-safety root; only the three initial-state hypotheses remain.

Reserved Lean target: `Xv6.SystemAdequacy.xv6_fs_adequacy`. Source: [iris/SystemAdequacy.v:1190](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/SystemAdequacy.v#L1190).

```coq
Corollary xv6_fs_adequacy_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall t2 g2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\
    xv6_trace_pure fsimg_cov (FsImg.sb_logstart fsimg_sb) g2.
```

## 3. `xv6_trace_adequacy_xv6Σ`

Conditional trace-resource interface; `R`, `P`, and every listed preservation/extraction premise remain client obligations.

Reserved Lean target: `Xv6.SystemAdequacy.xv6_trace_adequacy`. Source: [iris/SystemAdequacy.v:1220](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/SystemAdequacy.v#L1220).

```coq
Corollary xv6_trace_adequacy_xv6Σ (g : gstate)
    (R : list mobs -> iProp xv6Σ) (HRt : forall h, Timeless (R h))
    (HR0 : ⊢ |==> R [])
    (Hpow : forall (h : list mobs) (on : bool) (dk : Z -> bv 8),
       trace_shape h on ->
       ⊢ R h ==∗ R (h ++ [if on then ObsPowerOff else ObsPowerOn])%list)
    (Htx : forall (HR : riscvGS xv6Σ) (γ : uart_names),
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
              ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
              ⌜trace_shape h true⌝ -∗ ⌜obs_wire (open_seg h) = u_wire u⌝ -∗
              uart_ghosts γ u' -∗ R h ={⊤ ∖ ↑uartN ∖ ↑obsN}=∗
              uart_ghosts γ u' ∗ R (h ++ [ObsUartOut b])%list))
    (Hrx : forall (HR : riscvGS xv6Σ) (γ : uart_names),
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
              ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
              uart_ghosts γ u' -∗ R h ={⊤ ∖ ↑uartN ∖ ↑obsN}=∗
              uart_ghosts γ u' ∗ R (h ++ [ObsUartIn b])%list))
    (P : list mobs -> Prop) (HR : forall h, R h ⊢ ⌜P h⌝)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ P κs.
```

## 4. `xv6_obs_wf_xv6Σ`

Concrete observable-trace well-formedness and machine-safety root; only the three initial-state hypotheses remain.

Reserved Lean target: `Xv6.SystemAdequacy.xv6_obs_wf`. Source: [iris/SystemAdequacy.v:1249](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/SystemAdequacy.v#L1249).

```coq
Corollary xv6_obs_wf_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ obs_wf κs g2.
```

## 5. `xv6_out_accepted_xv6Σ`

Concrete UART acceptance safety root; only the three initial-state hypotheses remain.

Reserved Lean target: `Xv6.SystemUartAccepted.xv6_out_accepted`. Source: [iris/SystemUartAccepted.v:61](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/SystemUartAccepted.v#L61).

```coq
Corollary xv6_out_accepted_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps (Λ := riscv_lang) n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    (* the machine never gets stuck ... *)
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2)
    (* ... its observable history alternates PowerOn / console I/O /
       PowerOff, counts the boots and ties the open cycle to the wire ... *)
    /\ obs_wf κs g2
    (* ... and EVERY BYTE THE HOST SAW IN THIS CYCLE WAS ACCEPTED BY THE
       KERNEL, IN ORDER.  [uart_acc] is exactly the list the campaign's
       receipts ([WpUart.uart_sent], [UartSentLoc.uart_sent_from]) are
       lower bounds of. *)
    /\ obs_wire (open_seg κs) `sublist_of` uart_acc (duart g2.(gdev)).
```

## 6. `xv6_out_accepted_from_xv6Σ`

Conditional located-receipt interface; the two trace prefix/sublist premises are intentionally unclosed upstream.

Reserved Lean target: `Xv6.SystemUartAccepted.xv6_out_accepted_from`. Source: [iris/SystemUartAccepted.v:108](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/SystemUartAccepted.v#L108).

```coq
Corollary xv6_out_accepted_from_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps (Λ := riscv_lang) n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    forall tr0 bs : list (bv 8),
      tr0 `prefix_of` uart_acc (duart g2.(gdev)) ->
      bs `sublist_of` drop (length tr0) (uart_acc (duart g2.(gdev))) ->
      (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2)
      /\ exists w1 w2,
           obs_wire (open_seg κs) = w1 ++ w2
           /\ w1 `sublist_of` tr0
           /\ w2 `sublist_of` drop (length tr0) (uart_acc (duart g2.(gdev)))
           /\ bs `sublist_of` drop (length tr0) (uart_acc (duart g2.(gdev))).
```

## Meaning of the concrete predicates

`SystemAdequacy.fs_boot_pure` at line 149 says that the durable disk has the
expected extent, a well-formed log header, and a recovered committed block map
`D` representing some abstract filesystem state `S` with `FsDurSnap.snap_ok S D`.
`SystemAdequacy.xv6_trace_pure` at line 245 conjoins this with
`gpow = true → resv_ok g`. Port these definitions and their dependencies; replacing
them by an opaque uninterpreted predicate, pure `True`, or an assumed invariant
would change the completion target. The accompanying reducibility conclusion is
required: a silently stuck hardware execution must not satisfy the target merely
because its reachable states have good filesystem bytes.

The UART conclusion concerns bytes emitted during the *current open power cycle*:
wire output is an order-preserving sublist of accepted bytes. It promises neither
that accepted bytes eventually appear nor retention of every completed cycle's
accepted history. `xv6_out_accepted_from_xv6Σ` repeats its assumed `bs` sublist fact
in the conclusion; it is not a closed proof that a particular program's output
has been accepted. Its source header describes the remaining era-identification
gap. Do not silently strengthen this upstream partial interface into an asserted
application theorem.

The kernel bytes are embedded in the language, not a fourth hypothesis of these
Rocq roots. At `RiscvLang.v:1018`, `boot_image` comes from the tracked kernel dump;
`boot_byte` zero-fills absent bytes. At line 1325, `boot_facts` requires **all RAM**
to contain those bytes and requires each hart's register state to result from
running `ArchReset.boot_prog` from some initial register file. At line 1379,
`boot_shape` resets devices from the *current* device state through `virtio_reset`,
which preserves its durable disk. Only the initial machine is constrained to
`FsImgDisk.fsimg_dk`.

## One machine family for the early boot-image gate

The Lean language, power transitions, state interpretation and generic adequacy
must be parameterized by a fixed **data description of the loaded boot image**.
They must not take an arbitrary caller-supplied boot transition or reset predicate.
The common definition must retain the paper's RAM domain/totality, board PMA,
reset program, register nondeterminism, eight harts, device rules, event granularity,
TSO rules, reservation rules, and disk-preserving power cycle. Image metadata used
for proof-side code/data ownership must be part of the data/certificate boundary,
not a way to change the hardware rules.

Instantiate that one definition with the four bytes `6f 00 00 00` at the real
reset PC `0x80000000` for the `jal x0, 0` gate, and with the checked loaded paper
ELF for the six targets above. In both instances RAM outside the supplied image
is zero-filled at power-on, exactly as in the source. The fixed image is reloaded
after every crash; it cannot vary per era. The initial durable-disk argument is
separate, and reboot always keeps the current durable disk.

The one-instruction gate must initialize the same eight-hart/device/power machine,
prove its initial conditions satisfiable, exhibit at least one real transition,
and establish reducibility using the common adequacy theorem. A later two-hart
interference test can use two designated active participants while accounting for
the other six harts; it must not quietly switch to a different CPU-count model.
If a generic hart-count parameter is introduced, its specialization and the
unchanged rule definitions need their own explicit correspondence evidence.

Before claiming the xv6 specialization matches the paper, prove the loaded
image equality and a definition-level correspondence for initial states and each
transition rule. An alternate simplified language proving the gate, a manually
chosen reset-state table, or a generic stutter that makes every expression
reducible does not satisfy this contract.

The common image-parametric machine and closed JAL specialization are now
implemented. `MachCSL.Logic.JalMachineSafety.safe` proves reducibility for every
thread of every actual finite reachable configuration, with the model's
observation consistency conclusion. `concrete_positive_execution` supplies all
platform/state assumptions and a real power-on/fetch/retire schedule with no
premises. The boot handler covers all eleven forked workers and all permitted
boot witnesses. The proof and independent audits are recorded in
`MachCSL/Logic/JalMachineSafetySTATUS.md` and
`docs/reviews/jal-machine-safety-review.md` (published checkpoint `d6e1c89`).
This closes the one-instruction gate only. The two-hart TSO interference gate,
complete cross-prover semantic correspondence, and all six xv6 roots remain open.

## Active dependency extraction and assumption reports

The active file list is `iris/_CoqProject`; both root modules are active there
(lines 1090 and 1696). `SystemAssumptions.v` is intentionally commented out and
run separately. The snapshot has 1,427 active and 71 explicitly parked Iris files.
`docs/upstream/inventory.json` inventories source files but is not a compiler
proof-dependency certificate. The initial comment-stripped import scan found
1,312 local files in the `SystemAdequacy` import cone, including 1,290 Iris files
and no parked files. That is an overapproximating planning graph for one module,
not the union of the six declaration-level closures.

Use an isolated checkout and opam root/switch. Pins are in `.github/coq-deps.txt`:
Rocq/Coq 9.0.1, Iris 4.4.0, stdpp and stdpp-bitvector 1.12.0, Sail stdpp 0.20.1;
upstream CI selects OCaml 5.3. Record the resolved opam package graph and compiler
versions as well as the source commit. Preserve the checked-in `.v` images and
model: replay the CI sub-builds rather than invoke a target that regenerates them
from an unverified local xv6/toolchain combination.

Concrete extraction procedure, using the snapshot's own build machinery:

1. Generate `CoqMakefile` in `model-xv6iris`, `kernel-rocq`, `user-rocq`, and `iris`
   with each directory's `_CoqProject`, through `opam exec --switch=... --
   coq_makefile -f _CoqProject -o CoqMakefile`. Compile those four directories in
   that dependency order, retaining build logs and `.glob` files. This compiles
   the tracked data without running the ELF dumper.
2. Read the generated `iris/.CoqMakefile.d` (or the filename the selected
   coq_makefile emitted) and take the transitive prerequisite closure of both
   `SystemAdequacy.vo` and `SystemUartAccepted.vo`. Resolve relative paths and
   verify that each in-tree prerequisite is active in its `_CoqProject`; record
   external library prerequisites separately. This is the compiler import graph,
   not exact declaration usage.
3. Against that built tree, create a UTF-8 audit file importing
   `xv6iris.SystemAdequacy` and `xv6iris.SystemUartAccepted`. Run Rocq
   `Print All Dependencies <fully-qualified-root>.` on each of the six source
   names above. This traverses the root proof bodies; preserve the raw reports
   before canonicalizing names using load paths and `.glob`. Include the root
   types as well when building the union of proof and statement dependencies.
4. For each root's **statement** dependencies, use the existing
   `tools/tcb/tcb-report.sh xv6iris.SystemAdequacy.xv6_fs_adequacy_xv6Σ` pattern,
   changing the target for the other five. Its generated seed is
   `Definition tcb_seed := ltac:(let T := type of (@ROOT) in exact T).` followed
   by `Print All Dependencies tcb_seed.` and `Print Assumptions tcb_seed.`.
   `tools/tcb/tcb_report.py REPORT --md --with-inductives --target ROOT` formats
   it. The script documents an overapproximation through proof-valued constants;
   the formatter adds all inductives from visited files as an upper bound because
   Rocq's printed dependency report omits inductive declarations. Keep this
   limitation in the report, and separately inspect the actual datatype fields.
5. Run `make SWITCH=... audit-only` once to replay the canonical upstream
   `Print Assumptions xv6_fs_adequacy_xv6Σ` from
   `iris/SystemAssumptions.v:71`. Audit the other five roots explicitly as well;
   the recorded FS baseline must not be assumed to apply to an unaudited sibling.
   The generic roots' displayed client hypotheses are binders, not axiom entries.
   Capture the command, complete stdout/stderr, exit code, versions and hashes.

At the time these documents were written, the shared pinned checkout had no
`SystemAdequacy.vo` or compiler-generated `.CoqMakefile.d`, and no newly replayed
Rocq assumption report had been added to the repository. The available report is
an **upstream recorded baseline**, described in `SystemAssumptions.v` and
`claude-notes/durable-notes.md:2661`: thirteen entries for the concrete FS root.
They are dependent functional extensionality, `xv6iris_extras.resv_matches`,
`xv6iris_extras.resv_is_valid`, and ten Rocq primitives (`PrimString.string`,
`PrimString.get`, `PrimString.cat`, `PrimInt63.int`, `PrimInt63.eqb`,
`PrimInt63.sub`, `PrimInt63.lsl`, `PrimInt63.lsr`, `PrimInt63.land`,
`PrimInt63.lor`). This is not a claim that the new replay has passed.

The Lean replacements must quantify over the two fixed reservation predicates
explicitly and instantiate the concrete Iris functor family; no unresolved ghost
capacity or function-correctness instance may remain at a closed root. Audit the
transitive axiom and definition cones by defining package/module, including
private declarations. Reviewed foundational Lean axioms are not permission for
`sorryAx`, model axioms, or external implementations to enter unnoticed. Axiom
checking alone does not inspect theorem strength or trusted definitions.

## Review disposition

Claude Code, model `claude-fable-5-1`, effort `max`, contributed the initial and
revised design reviews. This document implements its request for exact roots,
boot-image parametricity and auditable dependency recipes after checking the
pinned source. It corrects the loose four-root scope by listing the two active
UART interfaces as well. It does not adopt the withdrawn supervisor-only memory
writer claim: the paper's disk DMA arm legitimately writes RAM.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
