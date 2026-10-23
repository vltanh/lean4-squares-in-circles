# Full ordered-angle terminal for the fourteen-separator class

Status: the complete 242-rectangle certificate passed direct exact replay.
Its arithmetic checker uses only the Python standard library.

The class keeps the physical labels and the fourteen signed owner separator
inequalities of `FIXED_ORIENTATION_STRESS.md`. Squares 0 through 6 have the
reference orientation; squares 7 and 8 have a common angle alpha; and squares
9 and 10 have a common angle beta. The full closed angle domain is

```
0 <= alpha <= beta <= pi/2,
```

or equivalently `0<=ta<=tb<=1` in half-angle coordinates. The equal-angle
locus, axis alignments and endpoints are included. Centers can lie anywhere.
This is a conditional contact-class theorem. It does not assert that every
packing can be captured by these labels, groups or selected separators.

**Theorem.** Throughout this class, `q>=qc`; for actual packings, equality consists
precisely of the established exact slider family. Its proof joins an exact
finite cover away from the candidate angles to the quantitative neighborhood
theorem, which already has an exact proof.

## A dual family with no angular singularities

Use all four disk corners for the boundary labels
`[0,2,3,5,6,7,9,10]`. Assign rational weights lambda>=0 whose total is one;
the three other squares carry no disk weight. Let `Li` be the total at label
i and `Vi` its weighted sum of corner offsets. The separator order remains

```
01,02,0-10,14,23,34,45,48,56,67,78,79,89,9-10.
```

Choose nine nonnegative rational parameters
`A,Z,C,D,E,F,G,I,K`. Put

```
ca=cos(alpha), sa=sin(alpha), cb=cos(beta), sb=sin(beta),
cd=ca*cb+sa*sb, sd=ca*sb-sa*cb,
B=Z*cd, H=Z*cb, J=Z*sa.
```

Assign separator weights in the stated edge order:

```
[A,C,D,A,E,B,A,B,F,G,H,I,J,K].
```

Every weight is nonnegative throughout the closed first-quadrant angle
square. In particular this remains true when `cd=0`; there is no division
by cd or by any sine or cosine.

The three unloaded forces at labels 1, 4 and 8 vanish identically. The only
nonconstant identity required is

```
H*u_alpha - J*v_beta = B*ex.
```

The forces at the eight boundary labels, in their listed order, are

```
(D-C,A), (C,E), (B,-E), (F,-A), (-F+G*sa,-G*ca),
-H*u_alpha+(G-I)*v_alpha,
I*v_alpha+J*v_beta-K*u_beta,
(-D+K*cb,K*sb).
```

Any boundary label may also have zero total corner weight, provided its
force vanishes. The checker verifies the following sufficient parameter
identities for every such label:

| Label with Li=0 | Required identity |
|---|---|
| 0 | A=0, D=C |
| 2 | C=E=0 |
| 3 | Z=E=0 |
| 5 | F=A=0 |
| 6 | F=G=0 |
| 7 | Z=0, G=I |
| 9 | I=Z=K=0 |
| 10 | D=K=0 |

These conditions are deliberately sufficient throughout the whole angle
square; the checker does not infer them from numerical residuals or divide
by a trigonometric quantity. They need not exhaust every special endpoint
identity.

Write `ka=(1+ca+sa)/2`, `kb=(1+cb+sb)/2`, and
`kd=(1+cd+sd)/2`. On the ordered domain these are exactly the mixed-orientation
support widths for the selected owner axes. On a rectangle extending across
the diagonal, kd is a lower bound for the physical width
`(1+cd+|sd|)/2`. Nonnegative separator weights ensure this replacement keeps a
valid lower bound. Therefore no diagonal tie is removed or assigned to an
unjustified exclusive branch.

The weak dual from `QUANTITATIVE_GROUP_ANGLE_NEIGHBORHOOD.md` becomes

```
S = 3A+B*(1+ka)+C+D*kb+E+F+G*ka+H+(I+J)*kd+K,
Ddual = 1/2+S - sum_{Li>0} |Ki-2Vi|^2/(4Li),
q >= Ddual.
```

This formula holds for arbitrary centers satisfying the fourteen halfspaces
and the selected disk-corner inequalities. The other forty-one pair
constraints and the remaining disk corners can only strengthen it.

## A finite exact angle cover

`ANGLE_TILES.json` specifies closed rational rectangles covering the unit
square. Each rectangle is one of three checked kinds:

* It lies strictly outside the ordered triangle (`ta_lower>tb_upper`).
* It lies inside a rational rectangle contained in the previously proved
  half-angle neighborhood `max(|ta-ta*|,|tb-tb*|)<=1/2000`.
* It carries nonnegative rational dual weights proving `q>Q>qc` throughout
  the rectangle.

The checker validates the full cover independently by sweeping all rational
x endpoints. On every open x strip, the active rectangles form an exact,
gapless y partition from zero to one. Since every rectangle is closed,
neighboring strips also cover each vertical boundary and every vertex.
The strict inequality used to discard unordered rectangles ensures that
points on `ta=tb` remain in checked rectangles.

For a dual rectangle, let m be its rational midpoint, `r0,r1` its half-widths,
and D the supplied dual function. Outward rational arithmetic encloses
D(m), its two first derivatives at m, and all second derivatives throughout
the full closed rectangle. The certified lower bound is

```
D(m).lower - sum_i |D_i(m)|.upper * ri
           - (1/2)sum_ij |D_ij(rectangle)|.upper * ri*rj.
```

Taylor's theorem proves this lower bound valid on the rectangle, including
all edges. Its comparison to Q is exact rational arithmetic. The numerical
optimizer used to discover weights is not imported by the checker, and its
statuses, objective values and feasibility tolerances have no role in proof
acceptance.

## Equality and remaining global work

All dual tiles have a strict bound above qc. Therefore equality can occur
only inside the retained neighborhood. The quantitative neighborhood theorem
forces both angles to be the exact candidate angles. The established
fixed-orientation equality proof then gives precisely the slider family for
actual packings. No generic-angle assumption is used in this deduction.

This terminal closes the complete ordered-angle domain for one physical
separator class. It does not classify arbitrary independent rotations or
show that every subcritical packing can be relabeled into this class. Those
are separate unrestricted capture and finite-class exclusion gates.

The cover has 214 dual rectangles, 27 strictly unordered rectangles, and one
retained neighborhood rectangle. It uses the exact target
`Q=2450603207/500000000=4.901206414`, strictly larger than the certified upper
endpoint of qc. The least verified dual margin above Q is greater than
`383171/10^12`. The retained rectangle is
`[0.2050,0.2059] x [0.2493,0.2501]`, and every point in it has half-angle
distance strictly below 1/2000 from the exact candidate root.

Reproduction:

```
python research/eleven/check_angle_tiles.py
```

Proof files: `angle_tile_dual.py`, `check_angle_tiles.py`, `ANGLE_TILES.json`,
and the already checked root and quantitative neighborhood dependencies.
`generate_angle_tiles.py` and `angle_tile_discovery_solver.py` are optional
discovery provenance; they require NumPy/SciPy, and generated output is always
independently replayed. Their seed and optimization tolerances are never used
by the proof checker.
