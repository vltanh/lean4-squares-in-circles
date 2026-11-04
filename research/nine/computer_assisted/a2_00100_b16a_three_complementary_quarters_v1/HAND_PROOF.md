# Complete exclusions of B16a quarters I20, I31 and I33

## Proposition and unchanged original

This packet excludes every physical configuration of each of the three
closed original I-center rectangles listed below. The original is
`negative-16a2fc93c8d133f0`, with unchanged registered path

```json
[["angle",3,0],["angle_cut",[0,"0"],0],["position_cut",[11,"1/2"],1],["f_side_escape",[5,7],[3]]]
```

The indices 0 through 8 are the same original squares A through I. Each
unit frame satisfies alpha_i^2 + beta_i^2 = 1 and alpha_i > 0. Its four
original corners are

\[
\left(x_i+\frac{\epsilon\alpha_i-\tau\beta_i}{2},
      y_i+\frac{\epsilon\beta_i+\tau\alpha_i}{2}\right),
\qquad \epsilon,\tau\in\{-1,1\}.
\]

The caller retains all nine original squares, all 36 original corners,
all 36 physical pair predicates, the five original cone comparisons,
actual AB/BC/EF/FG and strict CD, and the exact 001/00 mask predicates.
The radius scope is q < 1105/256. Replacing corner containment at q by
necessary containment at the closed value Q = 1105/256 only enlarges the
domain used for contradiction. Contacts and orientation endpoints remain.

The registered path retains t_A and t_D in [-1,0], where t_i = beta_i/alpha_i,
and y_F >= 1/2. Its literal escape halfspaces are

\[
\begin{aligned}
x_H-x_F&\le0, & y_A-y_F&\le-3/5,\\
y_A-y_F&\le3/5, & y_A-2y_H+y_F&\le3/5,\\
-y_A+2y_H-y_F&\le3/5.
\end{aligned}
\]

The redundant complement is retained. No physical label is deleted,
renamed or interpreted as an added square.

## Entire original quarter domains

The unchanged whole-original bound certificate has SHA256
`69ddd2dcc5383c3259187588a890ddadb4a6545e8bdcc11e653bdfb8bb6b3886`.
It is freshly reconstructed and replayed by the exact ancestor checker.
Its certified I-center box is [a,b] x [c,d], with

\[
a=-1474347/1048576,\quad b=5/4,\quad c=-91/60,\quad d=91/60.
\]

Set x_k = a + k(b-a)/4 and y_k = c + k(d-c)/4 for k = 0,...,4.
The original sixteen quarters are the products
R_ij = [x_i,x_(i+1)] x [y_j,y_(j+1)]. The frozen grid has SHA256
`5f3da1873c074eeee6a3343bc2aa5406b41e6376cce8b708694f30024edfda2d`.
The three full domains proved here are:

| Original quarter | Entire x_I interval | Entire y_I interval |
|---|---|---|
| I20 | [-163627/2097152,2457813/4194304] | [-91/60,-91/120] |
| I31 | [2457813/4194304,5/4] | [-91/120,0] |
| I33 | [2457813/4194304,5/4] | [91/120,91/60] |

The partition checker calculates these intervals from the freshly certified
parent, compares the entire initial state with the literal quarter record,
and keeps every other inherited bound and physical predicate. Later narrower
boxes arise only from replayed necessary deductions. They are not substituted
for the full starting rectangles in this table. Every shared grid edge and
vertex is retained, including its occurrence in adjacent quarters.

The exact domain-preservation walk connects each tree parent to the precise
quarter anchor. It accepts replayed unconditional bound induction and
complete separating-axis unions, checks initial-state equality at each edge,
and rejects an extra restriction as a domain-preserving edge. Matching an
original ID or a scope label does not discharge this obligation.

## Rational bound induction and terminal arithmetic

For every necessary inequality c_k dot z <= b_k, the printed certificate
uses a nonnegative rational multiplier w_k. Put C = sum(w_k c_k) and
B = sum(w_k b_k). If the certified bounds give |z_j| <= M_j, then any
objective a dot z satisfies

\[
a\cdot z\le B+\sum_j M_j|C_j-a_j|.
\]

Thus every coefficient residual is paid. Upper and lower interval deductions
follow by choosing the corresponding signed coordinate objective. A terminal
with exact reserve

\[
-B-\sum_j M_j|C_j|>0
\]

is contradictory. Empty certified intervals or separately accepted physical
terminals also exclude their attached domains. Numerical infeasibility is
not used as a premise.

Every printed row is independently reconstructed from the certified caller.
The accepted unit-corner, four-product unit-corner, energy, support and Gram
rows retain their physical meanings and source-bound hand derivations. In
particular, rectangle planes for an original center/frame product are valid
throughout that certified rectangle; they introduce no new assumption.
All original physical predicates remain inherited even when only a subset
is used in a particular nonnegative sum.

The exact terminal table gives every leaf and a rational positive lower
bound on each reserve, or the reconstructed physical terminal. The unchanged
node records contain the complete coefficients, multipliers and all preceding
rounds. The three inherited seed rounds are retained in those same records.

## Complete finite covers and quarter conclusion

The tree checker requires every declared node exactly once. Four Cartesian
inset alternatives cover a physical pair because each inset lies in its
original square. Eight original-square owner/axis/sign alternatives cover
the separating-axis condition for two squares with disjoint interiors.
An angle cut retains both closed intervals [lo,cut] and [cut,hi]. Each child
inherits the certified parent state and the exact stated alternative.
Contacts and shared cut faces therefore remain covered.

At a terminal, exact arithmetic excludes the entire attached leaf. At each
internal node, all alternatives of its complete cover are excluded. Finite
induction proves that the root has no physical configuration. The checked
anchor attachment then proves exclusion of the entire original quarter,
including the portions removed by preceding necessary bound deductions.
No OPEN child is used in a complete quarter proof.

The complete-tree counts are:

| Quarter | Nodes | Terminal leaves | OPEN leaves | Complete inset / SAT / angle unions | Retained rounds | Deductions |
|---|---:|---:|---:|---|---:|---:|
| I20 | 1 | 1 | 0 | 0 / 0 / 0 | 4 | 540 |
| I31 | 1 | 1 | 0 | 0 / 0 / 0 | 5 | 699 |
| I33 | 29 | 21 | 0 | 6 / 0 / 2 | 10 | 1680 |

## Direct terminal for I20

The complete I20 proof has one node. Its last certified bounds give

| Quantity | Certified interval |
|---|---|
| x_C | [620137/1048576,664359/1048576] |
| y_C | [-405345/524288,-192999/262144] |
| x_I | [-163627/2097152,-36687/524288] |
| y_I | [-1545557/1048576,-1529179/1048576] |

The original centered Cartesian inset half-size is
gamma_i = 1/(2(alpha_i + abs(beta_i))). Both gamma_C and gamma_I have the
certified lower bound 105821/262144. Therefore a separating inset gap must
be at least 105821/131072. The four alternatives all fail:

| Signed center gap | Certified upper bound | Required gap minus upper bound |
|---|---|---|
| x_I - x_C | -693511/1048576 | 1540079/1048576 |
| x_C - x_I | 1492345/2097152 | 200791/2097152 |
| y_I - y_C | -718489/1048576 | 1565057/1048576 |
| y_C - y_I | 773561/1048576 | 73007/1048576 |

All four rightmost fractions are positive. The two contained insets must
have overlapping interiors, contradicting the disjoint interiors of the
same original C and I squares. This is a terminal consequence of the
replayed full-quarter deductions. Its displayed arithmetic is also bound
to the literal final round in `I20_CENTER_INSET_TERMINAL_TABLE.json`.

## Direct terminal for I31

The complete I31 proof also has one node. Its rational nonnegative sum has
the fully residual-corrected reserve

\[
\frac{325827841856495490638410252480171306579267001847}
{68894807179081411369800736818026780497913273384960}
\;\ge\;\frac1{256}\;>0.
\]

The original quarter is therefore contradictory by the bound-induction
argument above, without subdivision. Every multiplier and coefficient is
in its unchanged node record.

## Original assembly and reproducibility

These three complete quarter exclusions restore the three missing
complementary pieces. Together with the eleven previously reproduced
quarters, they give fourteen reproducible exclusions in the unchanged
sixteen-quarter register. The only remaining B16a region is the separately
retained merged I21/I22 rectangle

\[
[-163627/2097152,2457813/4194304]\times[-91/120,91/120].
\]

The original follows only after that entire merged domain closes and the
accepted sixteen-quarter assembler checks all pieces. This packet alone
adds zero original-cell and zero mask closures. It leaves all 231 original
IDs, 32 mask IDs, 7,915 positional roots and 15 roadmap IDs unchanged.

`code/replay_b16a_complementary_packet.py` is a location adapter for the
unchanged partition checker. The packet preserves each new tree directory,
so a manifest's relative node filenames remain exact. Absolute historical
references are mapped to hash-bound relative packet or published-prior
inputs. Reads from other workspaces are forbidden during the cold replay.
The checker imports no numerical optimizer, replays every quarter and its
complete ancestry with rational arithmetic, and rehashes all inputs at the
end. No Lean, Lake or CI is run.

Extract the published prior identified by `PUBLISHED_PRIOR.json` beside the
packet. Run from a common dedicated directory, using a fresh output path:

```text
python -B -S code/replay_b16a_complementary_packet.py --prior ../prior --output ../fresh_replay
```

The required result for this packet is
`PASS_PORTABLE_THREE_COMPLETE_ORIGINAL_B16A_QUARTERS`; it explicitly reports
`whole_original_proved=false`. The source-bound generic hand arguments and
the prior root reviews are included, together with the complete terminal
table and all literal row certificates.
