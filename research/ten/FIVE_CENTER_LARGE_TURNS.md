# Five centers in the unit disk: completion of the moment inequality

Let five unit squares have pairwise disjoint interiors and centers `c_i`
satisfying `|c_i| <= 1`. Then

```text
sum_i |c_i|^2 >= 4.
```

Equality holds exactly for the plus: one center is zero, the other four
are the cardinal unit vectors of a common square frame.

The proof below completes the analytic dual argument with an explicit
finite rational table. It uses 78 cells and 1,193 vertex inequalities.
[Every cell, covering cut, and vertex inequality is printed in the
appendix](FIVE_CENTER_LARGE_TURNS_TABLE.md). The companion
[exact checker](check_five_center_large_turns.py) verifies the same
[rational data](five_center_large_turns_certificate.json), using only
Python's standard library and no floating arithmetic or optimization.
The geometric and analytic implications are proved here.

## 1. The permitted normal fans

Use the reductions in
[FIVE_CENTER_MOMENT_REDUCTIONS.md](FIVE_CENTER_MOMENT_REDUCTIONS.md).
If a center is not an extreme point of the center hull, the configuration
is the plus, which has moment four. Otherwise all centers are nonzero and
their successive ray angles `phi_i` have gaps

```text
delta_i = phi_(i+1)-phi_i >= pi/3,    sum delta_i = 2pi.
```

Choose neighboring separation normals with lifted angles `psi_i` in
`[phi_i+pi/2, phi_(i+1)+pi/2]`. Their successive turns
`gamma_i = psi_i-psi_(i-1)` satisfy

```text
0 <= gamma_i <= pi,    sum gamma_i = 2pi.                 (3)
```

We also need the following consequences of the same interlacing:

```text
pi/3 <= gamma_i+gamma_(i+1) <= 4pi/3.                    (4)
```

Indeed, `psi_(i+1)-psi_(i-1) >= phi_(i+1)-phi_i = delta_i`.
In the other direction this difference is at most
`phi_(i+2)-phi_(i-1) = delta_(i-1)+delta_i+delta_(i+1)`.
The two omitted center gaps are each at least `pi/3`, proving (4).

If every turn is at most `pi/2`,
[FIVE_CENTER_SMALL_TURNS.md](FIVE_CENTER_SMALL_TURNS.md) proves the strict
inequality `sum |c_i|^2 > 4`. It remains to handle fans with a turn larger
than `pi/2`. We prove the stronger statement that the dual inequality
already gives a uniform bound above four on every such fan satisfying
(3)--(4), without imposing any further physical realizability condition.

## 2. A concave minorant on each sign box

Fix nonnegative rational weights `lambda_i` and rational `d_i >= 1`.
For each index set

```text
p_i = lambda_(i-1),              q_i = lambda_i,
A_i = min(p_i,q_i)/2,            B_i = p_i q_i/(2d_i),
C_i = max(p_i,q_i)/2 - (p_i^2+q_i^2)/(4d_i) - d_i + 1.
```

The auxiliary dual inequality (2) of the reductions document is

```text
M = sum |c_i|^2 >= sum_i F_i(gamma_i),                    (5)
```

where

```text
F_i(gamma) = C_i + A_i sin gamma + (A_i+B_i) cos gamma
                                           if 0 <= gamma <= pi/2,
F_i(gamma) = C_i + A_i sin gamma + (B_i-A_i) cos gamma
                                           if pi/2 <= gamma <= pi.
```

To see the expansion, `t = sin gamma + |cos gamma| >= 1` implies
`min(p+qt,pt+q) = max(p,q)+min(p,q)t`. Expanding the squared force in
(2) gives exactly the displayed expressions.

In an acute coordinate interval, `F_i` is concave because both sine and
cosine are concave and their coefficients are nonnegative. In an obtuse
coordinate interval, put `K_i = B_i-A_i`. If `K_i <= 0`, the expression
is again concave: sine is concave and cosine is convex there.

If `K_i > 0`, choose a fixed angle `alpha_i` in the obtuse interval and
replace its cosine term by the tangent lower bound

```text
cos gamma >= cos alpha_i - sin alpha_i (gamma-alpha_i).
```

The resulting function `G_i` is a concave minorant of `F_i`: it is a
nonnegative multiple of sine plus an affine function and a constant.
In the other two cases let `G_i = F_i`. Thus, on a box with each coordinate
wholly in the acute or obtuse range,

```text
M >= G(gamma) := sum_i G_i(gamma_i),
```

and `G` is concave. For a bounded convex polytope inside that box, a lower
bound for `G` at every vertex is consequently a lower bound everywhere.

For each table cell, `alpha_i` is the midpoint of the actual minimum and
maximum of coordinate `i` on its polytope, computed from the printed
vertices. This is a fixed rational multiple of `pi`, not a function of the
point at which the minorant is evaluated.

## 3. The finite cover

For this section and the appendix, express angles in degrees. Rotate the
indices so that `gamma_0` is a largest turn. Reflect the cyclic order if
necessary so that a smallest turn has index `m=1` or `m=2`. Since the
average turn is 72 degrees, the minimum belongs to one of the three
closed intervals

```text
[0,45/2],    [45/2,36],    [36,72].
```

A fan of total angle 360 has at most three turns strictly larger than
90 degrees. Thus there are 42 initial root domains: choose `m` in `{1,2}`;
choose zero, one, or two additional high indices among the three indices
other than `0,m`; and choose one of the three minimum intervals. The high
coordinates, including index zero, lie in `[90,180]`. The remaining
coordinates lie in `[0,90]`, with the minimum coordinate restricted to its
chosen interval. Impose in every root

```text
sum gamma_i = 360,
gamma_i <= gamma_0,
gamma_m <= gamma_i,
60 <= gamma_i+gamma_(i+1) <= 240.                         (6)
```

Every fan under consideration belongs to at least one root. Ties and
90-degree coordinates belong to the closed intervals, so cause no loss.

Appendix Section 2 prints a binary subdivision tree for each root. Every
cut divides one current coordinate interval at its midpoint, retaining
both closed halves. Its leaves are the 78 listed table cells, except for
two singleton polytopes:

```text
(135,0,90,45,90),    (135,90,0,90,45).
```

These are already vertices of cells 38 and 9, respectively. Their singleton
status is immediate from their leaf boxes: for the first, the five lower
bounds are `(135,0,90,45,90)`, already summing to 360; for the second they
are `(135,90,0,90,45)`, again summing to 360. Their membership in the named
cells is visible from the listed boxes and the common constraints (6).
The exact checker also verifies both claims. Thus no boundary, degenerate
cell, or other part of a root is discarded.

## 4. Exact enumeration and trigonometric evaluation

For each cell, eliminate `gamma_4` by the sum constraint in (6). All
remaining constraints have integer coefficients and rational constants.
Intersect every four independent active constraint planes, solve by the
integer determinant and adjugate formulas, and retain precisely those
intersections satisfying every constraint. This lists all vertices:
every vertex of a bounded polytope in four-dimensional space has four
independent active constraints. The statement remains valid for a
lower-dimensional polytope, since its defining affine equalities provide
the additional active normals. An empty list means the bounded polytope
is empty. In particular, a list containing just one point proves that the
polytope is that singleton.

This procedure gives exactly the 1,193 vertices printed in Appendix
Section 3. All arithmetic for enumeration and feasibility is rational.

Here are explicit rational bounds for evaluating their trigonometric
expressions. Define

```text
S(q) = sum_(k=0)^23 (-1)^k / ((2k+1)q^(2k+1)),
R(q) = 1 / (49q^49).
```

The alternating arctangent series gives
`S(q) <= atan(1/q) <= S(q)+R(q)`. Machin's identity therefore gives

```text
P_- = 16S(5) - 4(S(239)+R(239)) <= pi,
P_+ = 16(S(5)+R(5)) - 4S(239)   >= pi.                  (7)
```

For completeness, if `a=atan(1/5)` and `b=atan(1/239)`, then
`tan(2a)=5/12`, `tan(4a)=120/119`, and `tan(4a-b)=1`.
The angle `4a-b` lies in `(0,pi/2)`, so equals `pi/4`, proving the identity.

For any nonnegative rational degree value `z <= 180`, put
`x_- = z P_-/180` and `x_+ = z P_+/180`. Enclose each monomial of the
following polynomials by its endpoint values on `[x_-,x_+]`, reversing
endpoints when its coefficient is negative:

```text
sin x: sum_(k=0)^12 (-1)^k x^(2k+1)/(2k+1)!,
cos x: sum_(k=0)^12 (-1)^k x^(2k)/(2k)!.
```

Enlarge the resulting intervals at each end by
`x_+^26/26!` for sine and `x_+^25/25!` for cosine. Taylor's theorem makes
these valid enclosures, because every derivative of sine or cosine has
absolute value at most one. All endpoints are rational. The tangent
expression is evaluated by the same interval addition and multiplication,
using (7) also for the possibly signed difference `gamma-alpha_i` in
radians. In particular, no decimal approximation to `pi` is assumed.

Evaluate `G` at each printed vertex this way. Round the rational lower
endpoint downward to the nearest multiple of `1/100000000`. The resulting
integers are printed individually in the appendix. The minimum over all
1,193 entries is

```text
400014266/100000000 = 200007133/50000000 > 4.             (8)
```

Each inequality in this finite table involves only the displayed rational
weights, the displayed rational vertex angles, the explicit series (7),
and the stated Taylor polynomials and remainders. The checker independently
enumerates the vertices, recomputes every bound, verifies every covering
cut and singleton cross-reference, and compares all results with the
printed rational certificate data. Its output is

```text
PASS: 78 cases, 1193 exact vertices, 42 covering roots,
      2 explicitly covered singleton leaves.
Uniform lower bound: 200007133/50000000 > 4.
```

A second independent rational evaluator also checked all 1,193 inequalities
using the original minimum-support expression from (2), a 16-term Machin
enclosure, and Taylor evaluation at a rational midpoint with a Lipschitz
bound for the argument error. It obtained the same rounded minimum.

## 5. Conclusion and the ten-square implication

For a non-plus five-square configuration, either all normal turns are at
most 90 degrees, when the small-turn proof gives `M>4`, or the finite cover
and concavity give (8). Hence every non-plus configuration has `M>4`.
The plus has `M=4`, completing both the inequality and its equality case.

This also excludes a ten-square configuration in `D_(9/2)` having exactly
five centers in the open unit disk. Write `t_i=|c_i|^2` for these five
centers. They cannot form the plus, whose outer centers have norm one.
Their moment is therefore strictly larger than four, so

```text
sum max(t_i-1/2,0) >= sum t_i-5/2 > 3/2.
```

The bound in [INNER_ARC_MOMENT.md](INNER_ARC_MOMENT.md) therefore makes the
total trace of these five squares on the test circle strictly larger than
`3pi/4`.
The other five squares, whose centers have norm at least one, each have
trace at least `pi/4` by
[CENTER_RADIUS_REDUCTION.md](CENTER_RADIUS_REDUCTION.md). Their disjoint
interior traces would have total length strictly larger than `2pi`, a
contradiction.

This closes the five-inner-center branch. It does not assert a conclusion
for the separate branches with three or four centers in the open unit disk.
