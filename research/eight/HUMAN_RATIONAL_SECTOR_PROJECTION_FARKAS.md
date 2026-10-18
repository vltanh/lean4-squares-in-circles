# A stronger global SAT-owner filter: rational sector projection + exact Farkas contradiction

**2026-10-13. Two COMPLETE all-frame hand theorems and an exact
eight-square OWNER-WORD counterexample to earlier graph-only
pruning sufficiency.**

This is substantive progress on the ONE remaining global obstacle:
pruning genuine all-eight-square SAT owner choices *without
branching on their center positions*. It does **not** prove
unrestricted \(R_8\ge\widehat R\).

## Theorem 1. Every genuine SAT owner forces a fixed rational projection order

Let arbitrarily oriented true unit squares \(S_i,S_j\)
belong to any packing with pairwise disjoint open interiors
inside the disk
\[
R^2\le q_+=9789/2500.
\]
Suppose a genuine **signed true SAT-owner normal** n of this
pair is directed i→j, so
\[
n\cdot(p_j-p_i)\ge
H_i(n)+H_j(n)\ge1.                               \tag{1}
\]

Use the twelve EXACT RATIONAL cone boundary unit rays
\(r_0,\ldots,r_{11}\) from
[HUMAN_RATIONAL_TWELVE_CONE_OWNER_DAGS.md]
(HUMAN_RATIONAL_TWELVE_CONE_OWNER_DAGS.md).
If n belongs to the closed cone
\(K_k\) from \(r_k\) to \(r_{k+1}\), put the
**fixed rational vector**
\[
d_k:=r_k+r_{k+1}.
\]
Then independently of the frames and centers,
\[
\boxed{d_k\cdot(p_j-p_i)>
\varepsilon:=\frac{289}{2700}>0.}              \tag{2}
\]

This conclusion remains true if n is a cone-boundary ray,
in which case it applies to either neighboring cone
to which the owner is assigned.

### Proof

The genuine farthest-vertex formula gives every
unit-square center radius
\[
|p_i|<r_0:=283/200
\]
in the search disk; the exact strict rational margin is
\(r_0^2+r_0+1/2-q_+=13/8000>0\).

Every rational cone has angular width strictly below
\(2/3\) radians, proved *without a numerical
trigonometric approximation* in the preceding
12-cone theorem from the exact ratios
\(8/15,\ 36/77,\ 3/4\).
Its **unit** central bisector is
\[
u_k=\frac{d_k}{|d_k|}.
\]
Since n belongs to \(K_k\), its angle from u_k is
strictly less than \(1/3\). The chord between
two unit vectors is at most their angular
difference, so
\[
|u_k-n|<1/3.
\]
Also the center difference has
\(|p_j-p_i|<2r_0=283/100\).
Applying these two strict bounds to the genuine
SAT inequality (1) gives
\[
\begin{aligned}
u_k\cdot(p_j-p_i)
&=n\cdot(p_j-p_i)+(u_k-n)\cdot(p_j-p_i)\\
&>1-\frac13\frac{283}{100}
=\boxed{\frac{17}{300}>0.}                     \tag{3}
\end{aligned}
\]

If \(\vartheta_k<2/3\) is the cone's angular width,
the two unit boundary vectors have bisector sum norm
\[
|d_k|=2\cos(\vartheta_k/2).
\]
For \(0\le x\le1/3\), cosine satisfies
\(\cos x\ge1-x^2/2\), so
\[
|d_k|>2\left(1-\frac1{18}\right)
=\boxed{\frac{17}{9}}.
\]
Multiplying this strict norm bound by (3) yields
\[
d_k\cdot(p_j-p_i)
=|d_k|u_k\cdot(p_j-p_i)
>\frac{17}{9}\frac{17}{300}
=\boxed{\frac{289}{2700}},
\]
proving (2). QED.

**Consequences.** Every directed owner edge must
respect a **strict rational ordering** of its
two actual square-center projections along
one of twelve globally FIXED rational vectors.
Thus the complete true SAT word gives 28
explicit **rational linear center inequalities**,
independent of the true frame angles once
each chosen owner sector is known.
In particular each sector's directed graph
is acyclic, now with quantitative projection
margin (the earlier DAG theorem gave only
qualitative acyclicity).

This is a necessary consequence of TRUE
square-square SAT separation, not a substitute
for it: a coarse owner-sector pattern might
pass (2) while failing some actual square
disjointness test.

## Theorem 2. Positive sector-force balance rejects whole owner words

Choose any subset of true directed SAT-owner edges
\(e=(i_e,j_e)\) and sectors \(k_e\) that contain
their actual signed owner normals. Suppose there
are **strictly positive rational weights**
\(\lambda_e>0\) with exact **zero center
incidence** at every square label:
\[
\boxed{
\forall i,\quad
 \sum_{e:i_e=i}\lambda_e d_{k_e}
-\sum_{e:j_e=i}\lambda_e d_{k_e}=0.}            \tag{4}
\]

Then no genuine eight-square packing in the
search radius ceiling can realize all those
selected SAT-owner inequalities.

**Proof.** Apply (2) to every chosen directed edge,
multiply by \(\lambda_e>0\), and sum:
\[
\sum_e\lambda_e d_{k_e}\cdot(p_{j_e}-p_{i_e})
>\varepsilon\sum_e\lambda_e>0.
\]
The left side is **exactly zero** because the
coefficient of every center \(p_i\) vanishes
by (4). Contradiction. QED.

This is an entirely rational **Farkas certificate**.
It does not require an interval upper bound
on centers beyond the already globally proved
universal disk-center radius used in Theorem 1.

## An exact eight-label owner-word certificate BEYOND 60-degree triangles and 12 DAGs

To demonstrate that the new Farkas rule adds
genuine pruning strength, take eight different
true unit-square frames with rational half-angle
tangents (labels 0,...,7):
\[
(-28287/125000,\ -5849/25000,\ -203777/1000000,\
 7769/100000,\ 133/125000,\
 -60483/500000,\ -67129/1000000,\
 15249/1000000).
\]
The complete 28-pair signed TRUE owner word is
in [global_sat_balanced_sector_farkas_certificate.json]
(global_sat_balanced_sector_farkas_certificate.json).

**Important:** The exact
[verify_rational_fan_sat_owner_word.py]
(verify_rational_fan_sat_owner_word.py) checker
independently confirms this complete word passes
**every** directed 60-degree triangle test and
**every** rational-sector DAG test. Passing those
tests is NOT sufficient for feasibility.

But eight of its genuine selected owner
inequalities have this complete exact rational
positive balanced certificate:

| Directed square labels | Genuine owner side normal | Rational sector k | \(\lambda\) |
| --- | --- | ---: | ---: |
| 0→4 | +e₀ | 11 | 44 |
| 0→6 | −e₀ | 5 | 44 |
| 1→2 | +e₁ | 11 | 44 |
| 1→4 | −e₄ | 6 | 51 |
| 1→6 | +f₁ | 2 | 28 |
| 2→5 | +e₂ | 11 | 44 |
| 4→6 | −f₆ | 8 | 28 |
| 5→6 | +e₆ | 11 | 44 |

The corresponding fixed **rational sector bisector sums**
are
\[
\begin{array}{c|l}
k&d_k=r_k+r_{k+1}\\
\hline
11&(9/5,-3/5)\\
5&(-9/5,3/5)\\
6&(-32/17,-8/17)\\
2&(3/5,9/5)\\
8&(-3/5,-9/5).
\end{array}
\]
These vectors and positive integer weights
satisfy (4) **coordinate-by-coordinate
for ALL EIGHT square centers**:
the nontrivial balance at label 1 is
\[
44d_{11}+51d_6+28d_2=(0,0),
\]
while \(44(d_{11}+d_5)=0\) and
\(28(d_2+d_8)=0\) give the other
balancing identities.

The total positive edge weight is
\[
\sum_e\lambda_e
=5\cdot44+51+2\cdot28=327.
\]
If this owner word were geometrically realizable
under the disk ceiling, Theorem 1 would force
\[
\boxed{
0=\sum_e\lambda_e d_{k_e}\cdot
                  (p_{j_e}-p_{i_e})
>327\frac{289}{2700}
=\frac{31501}{900}>35,
}
\]
a strict and overwhelming rational contradiction.

The independent
[verify_rational_sector_farkas.py]
(verify_rational_sector_farkas.py)
checks the **entire true rational owner word**,
that it genuinely passes the previous triangle/DAG
screen, that all eight selected normals belong to
their specified rational sectors, the exact positive
integer multipliers and all sixteen zero incidence
coordinates. Its output is a mathematical
**INFEASIBILITY certificate for this whole signed
owner word**, not a numerical LP claim.

## Research significance and honest limitation

The new combinatorial hierarchy is:

1. Detect any directed SAT-owner triangle with all
   owner normals in one genuine 60-degree cone.
2. Detect directed cycles in any of the twelve
   rational owner sectors.
3. Apply (2) to turn each signed owner sector into
   a fixed **rational linear center-order constraint**.
   Seek a positive exact rational **Farkas balance**
   (4) across sectors, rejecting more complex owner
   words even when **every individual sector DAG passes**.
4. Only for survivors use the full exact
   [GLOBAL_SAT_ANGLE_FIBER_DUALITY.md]
   (GLOBAL_SAT_ANGLE_FIBER_DUALITY.md)
   center-eliminating nonlinear disk/SAT dual.

This is **one coherent global reduction of SAT-owner
combinatorics**, not another list of local cap
intervals or contact graph cases.

The 12-cone graphs and their cross-sector Farkas
conditions are exact necessary conditions, but
they are **not yet a complete global owner
classification**. A sound terminating cover of
all eight-angle and SAT-owner possibilities has
still not been produced.
Consequently unrestricted \(R_8\ge\widehat R\),
equality classification and Lean remain OPEN.
