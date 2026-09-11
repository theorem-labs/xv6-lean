# Native Iris invariant capacity and allocation

`InvariantDefs/Spec/Proofs/Registry/Link` supply the native invariant
machinery required by the source `riscvF_invGS` and `riscv_pre_invGS`
(`RiscvPtsto.v:383`, `RiscvAdequacy.v:76`, paper pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). They adapt native Iris-Lean
`WSat`, `LaterCredits`, `FUpd` and `WeakestPre`; no replacement invariant
logic or soundness axiom is introduced.

| Slot | Exact native functor |
| --- | --- |
| 16 | `InvMapF`, recursive invariant-map authority |
| 17 | `constOF CoPsetDisjL`, enabled invariant masks |
| 18 | `constOF (DisjointLeibnizSet PosSet)`, disabled invariant names |
| 19 | `Auth.AuthURF (constOF Credit)`, additive later-credit authority |

The later-credit camera is distinct from the existing monotone-max-Nat
camera at slot 3. `registry_old` preserves all application slots 0–15;
`registry_unused` preserves every slot at least 20. Explicit slot witnesses
construct `registryCapacity.preS`, the native `InvGpreS`, and the existing
era/machine capacities. The heap and TSO byte capacity and shared generation
mono-nat capacity remain definitionally coherent.

`Names` contains exactly four runtime ghost names. Its `wsat`, `lc` and
`native` constructors use the supplied capacity witnesses, with
source-compatible `HasLC.hasLC`. `native_preS`, `native_world`,
`native_enabled`, `native_disabled` and `native_credit` prove this exact
retention. There is no arbitrary existential instance whose capacity is
silently assumed to agree with the registry.

`allocate capacity n` performs the same construction as native
`WSat.wsat_alloc` and `LaterCredits.lc_alloc` through native `iOwn_alloc`:
an empty invariant map, the full enabled mask, the empty disabled set, and
an additive credit authority/fragment at `n`. It returns four allocated
names and native

```text
wsat ∗ ownE ⊤ ∗ lc_supply n ∗ £ n
```

`allocated_native` proves that the named wrapper is exactly this native
proposition under the constructed `InvGS`. The empty disabled token is
discarded in the same way as native `wsat_alloc`; its allocated name is
retained in the native world instance. `allocate_frame` retains any
application-owned Iris frame. The independently importable `InvariantSpec`
states allocation; `invariantSpec` and `registryInvariantSpec` prove the
contract for explicit and registry capacities.

`machineGS` supplies the constructed invariant instance to the actual
image-parametric `MachineInterp.irisGS`, preserving its state interpretation
and zero `numLatersPerStep`. `registryMachineGS` specializes it to the
extended registry. Names and the machine-state/trace parameters remain
explicit; this adapter does not by itself prove that the corresponding
world or machine state is owned.

Zero extra laters does **not** remove the mandatory step credit.
`zeroLater_steps_sum` and `machineGS_steps_sum` prove that native adequacy's
`steps_sum` equals the number of operational steps, because its recurrence
adds `numLatersPerStep + 1`. These modules neither change that recurrence
nor assert zero total credits.

Validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.InvariantLink
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/InvariantAudit.lean
```

The 375-job build passes; the proof module takes about 1.0 seconds and the
link about 0.9 seconds. The independent namespace audit checks 180 public
and private declaration cones and rejects all axioms except `propext`,
`Classical.choice` and `Quot.sound`. Output:
`/tmp/xv6-lean-research/invariant-axioms.log`. No `sorry`, custom axiom,
`native_decide` or `bv_decide` is used.

This closes native invariant capacity/allocation for the current machine
resource registry. Auxiliary kernel cameras above slot 19, client
crash/trace invariant allocation, machine lifting WPs and final adequacy
remain separate work. No upstream or other component file was modified.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
