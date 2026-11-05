# Four full nine-square mask domains are nonempty at the boundary

> Retained mathematical source. Reproduction commands, checker reports and implementation notes below refer to the [archived version](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/FOUR_FULL_NINE_MASK_CLOSED_Q_BOUNDARY_HAND_PROOF.md); the current task is the [pen-and-paper roadmap](../PROOF_PLAN.md).

November 4, 2026. Exact computer-assisted discovery followed by a direct
rational hand/table verification. No Lean, Lake, or CI.

## Statement and scope

Set (Q=1105/256). The unchanged closed-radius predicates

\[
 D_{101/11}^{\le},\qquad D_{111/01}^{\le},\qquad
 D_{111/10}^{\le},\qquad D_{111/11}^{\le}
\]

are all nonempty. One explicit packing of **nine original unit squares**
supplies all four witnesses, using the four frames and full label
permutations below. Every original corner, every original physical pair,
every marked cone comparison, every strict weak bit, and both additional
originals are retained.

This classifies a boundary obstruction. It neither produces a packing
strictly below (Q) nor closes any strict-radius mask. All four strict
predicates remain OPEN. A proof of their strict-radius exclusion cannot
replace its domain by an empty closed-(Q) predicate. Equality or a
justified strict normalization must be handled explicitly.

The packing is the existing exact limit control from
`limit_frame_family_table.json`. The new result is its four literal
full-mask witnesses. Discovery used a separate all-frame inventory; that
inventory is **not a dependency** of the direct proof in this packet.

## 1. Nine unchanged physical originals

Use physical coordinates (X,Y). All nine original squares have the
explicit orthonormal frame (u=(1,0),v=(0,1)). This is an allowed
particular realization of independently framed originals; it imposes no
common-frame hypothesis on the general theorem.

The center of original (i) is ((X_i,Y_i)/240):

| Original | (X_i) | (Y_i) | Largest squared corner norm |
|---|---:|---:|---:|
| 0 | −360 | 15 | (1105/256) |
| 1 | −120 | 15 | (337/256) |
| 2 | 120 | 112 | (1741/900) |
| 3 | 360 | 15 | (1105/256) |
| 4 | −240 | −225 | (1105/256) |
| 5 | 0 | −225 | (593/256) |
| 6 | 240 | −225 | (1105/256) |
| 7 | −208 | 255 | (248209/57600) |
| 8 | 32 | 352 | (1921/450) |

Each maximum is at most (Q). In fact, for an aligned unit square it is

\[
 (|X_i|/240+1/2)^2+(|Y_i|/240+1/2)^2.
\]

The checker also evaluates all four corners separately. Originals
0, 3, 4, and 6 have a corner exactly on the (Q)-circle, so the displayed
packing is not a strict-subcritical witness.

For every pair (i<j), either (|X_j-X_i|\ge240) or
(|Y_j-Y_i|\ge240). This separates the **original physical squares**,
including permitted boundary contact. An explicit complete certificate
in lexicographic pair order

\[
 01,02,03,04,05,06,07,08,12,13,14,15,16,17,18,
 23,24,25,26,27,28,34,35,36,37,38,45,46,47,48,56,57,58,67,68,78
\]

is the axis word

```text
000300100033011023321223110010011110
```

Here 0 means the owned normal ((1,0)), 1 means ((0,1)), 2 means
((-1,0)), and 3 means ((0,-1)). For the selected normal (n), the
full original corner projections satisfy

\[
 \min_{z\in S_j} n\cdot z-\max_{z\in S_i} n\cdot z\ge0.
\]

Thus all 36 original pair conditions hold, without an inset or
center-disk replacement.

## 2. Exact frames and complete witness permutations

For the integer pair ((p,q)\ne(0,0)), put

\[
 N=p^2+q^2>0,\qquad
 e=(p,q)/\sqrt N,\qquad f=(-q,p)/\sqrt N.
\]

The Gram matrix is exactly the identity. A physical point
((X,Y)/240) has witness coordinates

\[
 x=\frac{pX+qY}{240\sqrt N},\qquad
 y=\frac{-qX+pY}{240\sqrt N}.
\]

Each original frame in witness coordinates is

\[
 u'=\frac{(p,-q)}{\sqrt N},\qquad
 v'=\frac{(q,p)}{\sqrt N};
\]

these remain exactly orthonormal. Its actual horizontal projection
halfwidth is (h=(|p|+|q|)/(2\sqrt N)). The two-square halfwidth sum,
after multiplying by the **positive** denominator (240\sqrt N), is

\[
 T=240(|p|+|q|).
\]

| Mask | ((p,q)) | (N) | Main ((A,B,C,D)) | Short ((E,F,G)) | Extras ((H,I)) | (T) |
|---|---|---:|---|---|---|---:|
| `101/11` | ((49,11)) | 2522 | ((0,7,2,3)) | ((4,5,6)) | ((1,8)) | 14400 |
| `111/01` | ((-1,1)) | 2 | ((6,5,4,0)) | ((3,1,7)) | ((8,2)) | 480 |
| `111/10` | ((1,-1)) | 2 | ((0,4,5,6)) | ((7,1,3)) | ((8,2)) | 480 |
| `111/11` | ((1,-1)) | 2 | ((7,1,5,6)) | ((8,2,3)) | ((0,4)) | 480 |

Every row is a permutation of all nine originals. No eighth or ninth
original has been dropped when changing the selected chains.

## 3. All twenty marked comparisons

For each directed edge (i\to j), the table gives

\[
 d=p(X_j-X_i)+q(Y_j-Y_i),\qquad
 v=-q(X_j-X_i)+p(Y_j-Y_i).
\]

The cone condition is (d\ge|v|), with (d>0). The unchanged mask
convention is bit 0 if (d\ge T), and bit 1 if (d<T). Cone equalities
and actual-projection equalities remain admissible; **every bit 1 is
strict**, including on those cone boundaries.

| Mask | Edge | Original pair | (d) | (v) | (T) | Bit |
|---|---|---|---:|---:|---:|---:|
| `101/11` | AB | 0→7 | 10088 | 10088 | 14400 | 1 |
| `101/11` | BC | 7→2 | 14499 | −10615 | 14400 | 0 |
| `101/11` | CD | 2→3 | 10693 | −7393 | 14400 | 1 |
| `101/11` | EF | 4→5 | 11760 | −2640 | 14400 | 1 |
| `101/11` | FG | 5→6 | 11760 | −2640 | 14400 | 1 |
| `111/01` | AB | 6→5 | 240 | 240 | 480 | 1 |
| `111/01` | BC | 5→4 | 240 | 240 | 480 | 1 |
| `111/01` | CD | 4→0 | 360 | −120 | 480 | 1 |
| `111/01` | EF | 3→1 | 480 | 480 | 480 | 0 |
| `111/01` | FG | 1→7 | 328 | −152 | 480 | 1 |
| `111/10` | AB | 0→4 | 360 | −120 | 480 | 1 |
| `111/10` | BC | 4→5 | 240 | 240 | 480 | 1 |
| `111/10` | CD | 5→6 | 240 | 240 | 480 | 1 |
| `111/10` | EF | 7→1 | 328 | −152 | 480 | 1 |
| `111/10` | FG | 1→3 | 480 | 480 | 480 | 0 |
| `111/11` | AB | 7→1 | 328 | −152 | 480 | 1 |
| `111/11` | BC | 1→5 | 360 | −120 | 480 | 1 |
| `111/11` | CD | 5→6 | 240 | 240 | 480 | 1 |
| `111/11` | EF | 8→2 | 328 | −152 | 480 | 1 |
| `111/11` | FG | 2→3 | 337 | 143 | 480 | 1 |

These entries prove all four full predicates directly. For example,
`101/11` has the strictly positive actual-middle reserve (14499-14400=99),
while its four weak reserves are 4312, 3707, 2640, 2640. The two mixed
`111` masks have an actual short edge at equality, which the original
definition expressly allows. The `111/11` weak reserves are
152, 120, 240, 152, 143, all strictly positive.

## 4. Consequence for proof discovery

These are four genuine **closed-(Q)** witnesses, with strict designated
weak bits. They are not limiting seven-square relaxations, and their
existence does not depend on dropping any physical pair. Therefore a
computer search whose declared domain is the corresponding whole
closed-(Q) predicate must retain a feasible case. A claimed exact
contradiction on that entire domain would be invalid.

The intended strict-radius task is unchanged. A complete proof can use
a sound strict-counterexample normalization, a separate equality
terminal, or another argument that applies only below (Q); it cannot
silently strengthen the desired statement to closed-(Q) emptiness.
No positive distance below (Q) is supplied or assumed here.

## 5. Portable exact replay

From this packet directory run:

```text
python verify_closed_q_boundary_witnesses.py --directory . --negative-controls
```

The checker is standard-library-only and reconstructs the original
frames, all 36 corners, all 36 printed physical separators, all four
orthonormal witness frames, all four full-nine permutations, and all
20 literal edge rows. It uses arbitrary-precision integers and exact
fractions. The positive square-root frame denominators are handled
symbolically by clearing their known positive values.

The manifest binds the table, checker, this hand proof, the original
limit control, and the unchanged physical-domain contract. All bound
files and the manifest are rehashed at replay completion. Optional
negative controls reject an omitted ninth original, an omitted
physical pair, reversal of only the main chain, a corrupted strict-bit
reserve, and a false strict-subcritical classification.

The checker proves the stated finite witness identities; it is not a
proof-kernel or human verification. The broader all-direction discovery
inventory is deliberately kept separate. The counts remain 32 original
masks, with **zero new strict-mask closures and zero new original-cell
closures** from this packet.
