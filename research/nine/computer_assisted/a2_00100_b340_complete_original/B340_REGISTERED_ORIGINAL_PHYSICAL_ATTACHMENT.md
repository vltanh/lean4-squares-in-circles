# Physical attachment for the complete B340 original tree

## Exact registered original

The original is `negative-34029ea8b047982f`, sign `negative`, baseline
frontier index 66 in the frozen 231-original definition source. Its path is

```json
[
  ["angle", 3, 0],
  ["angle_cut", [0, "0"], 0],
  ["position_cut", [11, "1/2"], 1],
  ["f_side_escape", [5, 7], [2]]
]
```

The source for that original definition is
`ea000e84c04675fe22424e5c20d3df9d735d659065349800aef2699170bff604`.
The independent initial-state record is
`registered_B_initial_states/negative-34029ea8b047982f.json`, SHA256
`d7663ff3b35a6a08062695af46494ad85e1632d94d1cc1bb25d59198c89c1019`.
The complete candidate tree points directly to this record. Its initial
state is independently reconstructed from the registered path; all proved
whole-parent bound rounds are retained inside the root record.

The historical definition source is distinct from the current status
register. The packet builder and cold replay compare all 231 tuples of
ID, sign, baseline index and path against the current register, and require
this exact original to be open before acceptance.

## Physical meaning of the path

Indices 0 through 8 are the unchanged originals A through I. The slope
coordinate of square i is `t_i=beta_i/alpha_i`, with `alpha_i>0`.
The first three path entries retain `t_D in [-1,0]`, `t_A in [-1,0]` and
`y_F >= 1/2`, together with their inherited closed bounds.

The frozen `f_side_escape_rows((5,7),2,3/5)` definition gives the following
literal center inequalities:

\[
x_H-x_F\le 0,\qquad
y_A-2y_H+y_F\le-\frac35,\qquad
y_A-y_F\le\frac35,\qquad
y_A-2y_H+y_F\le\frac35.
\]

The final two inequalities retain the closed complements of the earlier
height alternatives. The fourth inequality is redundant here, and remains
present in the literal caller. The boundary equalities are included.

The underlying `001/00` physical caller retains nine unit squares and
their 36 original corners

\[
\left(x_i+\frac{\epsilon\alpha_i-\tau\beta_i}{2},\quad
y_i+\frac{\epsilon\beta_i+\tau\alpha_i}{2}\right),
\qquad \epsilon,\tau\in\{-1,1\},
\]

with `alpha_i^2+beta_i^2=1` and every corner in the closed disk
`Q=1105/256`. All 36 original pair-disjointness predicates, the marked
actual AB/BC/EF/FG conditions, the five original center cones and strict CD
remain in the caller throughout the proof. Every numerical inset and
auxiliary product is interpreted as a consequence of these same originals.

## Finite proof and whole-domain attachment

The frozen tree is `whole_B340_adaptive_lazy_v8/manifest.json`, SHA256
`97ff1c6d4af4f92a7de377a3e3d4487f701706f3889bd29db7bda3c7652c2805`.
It contains 403 node records. After the numerical worker exited normally,
all 403 file hashes matched that manifest, and its declared cover had no
OPEN leaf. These statements describe the frozen candidate. Mathematical
acceptance requires the complete independent exact replay and the fresh
portable replay described below.

At each bound round, the checker reconstructs every weighted inequality
from its certified parent state and checks the full rational weighted sum.
Every coefficient residual is paid using the certified absolute variable
bounds. A positive exact contradiction reserve or a separately checked
physical terminal excludes that domain. The full terminal table is built
from the fresh independent report and references the unchanged literal
node records containing every coefficient and multiplier.

Each internal split retains all four Cartesian inset alternatives, all
eight physical owner/axis/sign alternatives, or both closed slope-cut
intervals, according to its recorded split kind. The independent checker
reconstructs each child from the certified parent, checks every sibling,
and verifies that the complete node list is visited exactly once. Therefore
exclusion of every leaf implies exclusion of the root domain, including
all shared cut faces. The root is the directly reconstructed registered
original above, so this is a whole-original implication.

The hand derivations of bound induction, complete covers, accepted row
families and physical row terminals are in
`REGISTERED_B_COMPLETE_TREE_HAND_PROOF.md` and the included source-bound
geometric packets. The B340 attachment introduces no new row family.

## Concrete acceptance and packaging entry points

1. `verify_b_four_corner_lazy_trees.py` replays the complete tree and proves
   the original-domain attachment. The required report status is
   `PASS_COMPLETE_ORIGINAL_PHYSICAL_TREE`, with `complete=true`,
   `whole_original_proved=true` and `open_leaves=0`.
2. `build_registered_b_four_lazy_packet.py` freezes the actual dependency
   bytes, compares the current register definitions and writes
   `COMPLETE_TERMINAL_TABLE.md` from that fresh report. It cannot build a
   final complete packet from an OPEN report.
3. `replay_registered_b_four_lazy_packet.py` reruns the entire proof using
   archive-relative input aliases, the pinned 507-input published prior,
   standard-library exact arithmetic and a guard forbidding reads from
   the old workspace. All inputs are rehashed at completion.
4. `archive_registered_b_packet.py` requires the fresh portable success,
   writes the release manifest, and checks every member and every compressed
   archive part before the package is handed to the parent for publication.

The accepted conclusion is exclusion of this one registered original.
The current mask and its other original cells retain their separate proof
obligations; ledger changes remain under the parent's publication process.
