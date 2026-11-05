# Non-author review of the B462 57-node partial cover

Review date: 2026-11-05. Result: **PASS_SCOPED_NONAUTHOR_REVIEW**.

I independently reviewed the immutable 57-node snapshot and native packet
produced by the B462 continuation. All 57 record checks, all finite child
unions, all 31 terminal arguments and all native byte bindings passed.
The full registered original domain is retained, and the first H/I proxy
branch is completely excluded. **The original remains OPEN.** There are ten
OPEN terminal domains and no new original-cell or mask credit.

This review is by a separate agent that did not author the snapshot. It uses
an independent structural/literal-sum audit and freshly executes the existing
independent physical checker; it does not claim a new implementation of every
accepted physical premise, a whole-proof audit or a standalone cold replay.

## Exact subject and identities

The immutable snapshot is
`research/nine/.runs/b462_continue/snapshot_early/manifest.json`, SHA256
`06af1397700ec8f4a30f172ad449517b4c9943b3660cbc21be673e913a59e79a`.
Its original ID is `negative-462e78d2e2d8be05`.

The native packet is `research/nine/.runs/b462_continue/early57_native_packet/`.
These are its reviewed identities:

| File | SHA256 |
| --- | --- |
| `MANIFEST.json` | `9aeb4f07a0b950fc68ddc5646eb6b1c386ada50ac45c2d25a539c5973d3e5ace` |
| `INPUTS.json` | `fe7f19af1fba6a1a23119d1c74f445d05e5ff5ab203df4eeba82dc80340ca1aa` |
| `inputs.tar.xz` | `cd10a2ccfe76c522865a39e21e48f630cf2bf7cf92ec6e663e30662abcd2ef43` |
| `FRESH_EXACT_REPLAY.json` | `e86118fd7c24711e317de65c577992c5c4a83b72be2b6da75f80397d73a89824` |
| `FRESH_EXACT_REPLAY.log` | `6a08576cfb83125ea2c5edc9f1f3ca7c186150940d280c95996edac887ec792a` |
| `BASE_REPLAY.json` | `a7c70e502d0407df93655495864c32ad97856c8c0509a021dd6d286da38035b5` |

The archive is 1,869,000 bytes and contains 308 unique blobs for 317 indexed
native paths. The review JSON records all exact published/native source
identities, so the acceptance is tied to these bytes and does not extend to
the author's evolving `finite256` continuation. There was no README in the
native packet at the time of this review. This report reviews its manifest,
certificates and proof scope; a subsequent manuscript must describe the same
limited result.

## Original caller and preservation

The parent is
`/workspace/scratch/f9f48fcfb253/b_work/recovery_20261105/registered_B_initial_states/negative-462e78d2e2d8be05.json`,
SHA256 `24d91df8ce4a2472ebf76ac4b73c1fc07c58fbb5f9c213be8b415d1b8b2cc302`.
The original-register SHA256 is
`ea000e84c04675fe22424e5c20d3df9d735d659065349800aef2699170bff604`.

I read the registered-original and whole-domain checkers and freshly invoked
them. They check the frozen register identity, unique matching original ID
and exact registered path, derive the ID from that path, reconstruct the
physical initial state and require exact literal equality with the saved
state. The root of the 57-node tree is precisely that state. Thus the
whole-domain conclusion comes from reconstruction and equality, not merely
from the packet's `whole_original_domain_retained` flag.

The registered path is:

```text
angle(owner=3, side=0)
angle_cut(owner=0, cut=0, side=0)
position_cut(coordinate=11, cut=1/2, side=1)
f_side_escape(pair=[5,7], choice=[1])
```

All nine originals, original corners/pairs and strict weak CD remain in the
accepted physical caller. The radius scope is strict `q < 1105/256`; this
review supplies no equality conclusion.

The base one-node manifest is SHA256
`68ace75e6c238637d7a53ae151da749dd67afa9bb316a71476ba7ac1dd42acae`.
The continuation preserves its root initial state and both earlier bound
rounds literally. It adds one further root round before branching. I checked
that prefix preservation explicitly and freshly replayed all three rounds.

## Complete cover and reusable closed branch

The finite tree has 57 nodes, 31 excluded terminal domains, ten OPEN terminal
domains, twelve complete four-way proxy unions and four complete two-way
closed slope unions. My structural walk visits every indexed node exactly
once, checks each payload hash and parent/depth/choice field, reconstructs
each child directly from its parent final state and checks every alternative.
All other physical state and path information is unchanged. Both halves of
each slope cut include the shared face.

The root splits the H/I pair `[7,8]` into all four original-inset proxy cases:
axis 0 or 1 and sign -1 or +1. Their completeness is the accepted necessary
separation cover for the disjoint axis-parallel insets of the physical
squares. It does not select a physical frame owner or omit a sign.

Root child 1, with choice `[0,-1]`, is fully excluded by a freshly checked
`accepted_center_interval_terminal`: independent physical propagation gives
an empty original-center interval. This is a complete inherited root branch,
not merely an infeasible numerical relaxation status. Root children 2, 3 and
4 remain OPEN. Child 2 has further subdivisions, and all its siblings and
remaining descendants are preserved explicitly. No union is declared closed
unless every child is closed.

## Exact terminal and premise checks

Fresh replay validates every one of the 57 records and all 31 terminals:

- 12 accepted center interval contradictions;
- eight frame contradictions derived after certified bound rounds;
- eleven positive rational-reserve contradictions.

It checks 11 bound rounds, 2,085 deductions and 3,061 printed-row occurrences,
agreeing with the author's completed independent replay. For each of the
eleven weighted terminals my own Fraction calculation separately recomputes
the positive integer-over-2^40 weights, exact coefficient sum, RHS, absolute
residual bound and positive reserve. The independent physical engine then
reconstructs every printed premise and checks the certified bounds. Numerical
LP points and solver status fields are not accepted as proof.

The accepted row families and physical reconstruction are unchanged. The
checker retains the accepted center-support and corner-support bindings,
original physical geometry and relevant other previously accepted premises.
The registered-root check and the fresh record checks complete in the same
native environment; 161 adapter source pins are rehashed at the end. NumPy,
SciPy and HiGHS are not imported by the review run. Previously accepted
physical row-family derivations are reused, not re-proved from scratch.

## Native transport and remaining scope

Every outer manifest hash and every indexed current source file was checked.
Every archive member is a regular file named `sources/<sha256>` whose bytes
match the declared size and digest. There are no duplicate, missing or extra
archive members. Every source pin in the fresh full replay report was also
rehashed. The structured review includes the complete source identity map.

This certifies native byte recovery and the stated partial proof. The archive
does not itself assert a complete inventory of all files opened transitively
by the accepted ancestry loaders, and no fresh isolated installation was
performed. Published ancestral proof packages remain dependencies.

The native manifest's historical discovery `acceptance_status` still says
that fresh replay is pending; the separately hashed fresh replay and this
review supply that later evidence. The packet's explicit mathematical status
is already correct: partial, whole original retained, whole original not
proved, and zero original/mask credit. No mathematical or byte-binding defect
was found within this scope. The fixed counts remain 224/231 original cells
and 8/32 masks CLOSED. No Lean, Lake, compilation or CI was run.

## Review artifacts

The command was:

```sh
python -B -S research/nine/.runs/review_continue/review_b462_early57.py
```

Review script SHA256:
`520aae8784e9ae1ad622c5510747a4c2593eac2ba391bb7cd463681349f98d45`.
It imports the earlier independent review helper `review_b16_checkpoints.py`,
SHA256 `fb78dac04f3b9177f97a5d78e731b3d0ffb683c63f23b54ea1e2d89587d5b5c8`.
The structured result `B462_EARLY57_NONAUTHOR_REVIEW.json` is SHA256
`2fc2697b69723b248a71a716a0f48a1ad6b160210f418707ed5cf64c5ae26eb8`;
it contains all per-record audits, the eleven literal reserves, and all source
identities. The raw `b462_early57_review.log` is SHA256
`9884190ef22c3aafa81e92760b5fbbabd3defe9130e0dd697ce7f79ed2c83e6a`.
Execution took about 24 seconds. This command assumes the restored native
paths and is not a standalone cold-install command.
