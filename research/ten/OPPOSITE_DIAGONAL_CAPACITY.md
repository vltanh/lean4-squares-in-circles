# A loaded-to-loaded diagonal core cannot have opposite circle signs

**Status:** complete uniform capacity argument in the selected-certificate
radius window, checked in this single-agent session with separate 44-bit
and 60-bit integer interval arithmetic. Logical capacity predicates are
shared. No independent agent review or Lean verification is claimed.

## 1. Statement and normalization

Let an unloaded degree-two D transmitter have two loaded neighbors.
Generic normal selection makes both contacts relative interiors of
neighbor sides, so those two frames are parallel. This does not require
the neighbors themselves to have degree two.

The [universal radial-D corollary](RADIAL_DIAGONAL_THREE_BODY_CAPACITY.md)
already excludes geometric two-circle endpoints. Normalize the two
unique-circle endpoints as in
[the two sign-mode reduction](LOADED_DIAGONAL_PARAMETER_BOX.md).
If their circle vertices have opposite transverse signs, reflect and
relabel so

```text
A=[-u,1-u] x [-H_A,1-H_A],
B=[v-1,v] x [H_B-1,H_B],
u+v=K=2+sqrt(2),       H_A>=H_B>1/2,
u^2+H_A^2=v^2+H_B^2=Q=R^2,
H_B-1<h<1-H_A.
```

D has center ((v-u)/2,h) and its axes are
(1,1)/sqrt(2),(-1,1)/sqrt(2).

**Theorem.** Every packing containing these three squares in the
window 79/40<=R<=3/sqrt(2) has at most nine unit squares.
Consequently this opposite-sign class cannot occur in the selected
certificate of a strictly subcritical ten-packing.

Endpoint degrees, other contact types, circle coefficients and every
other square orientation are unrestricted.

## 2. One compact cube covers every opposite-sign core

Put d=H_A-H_B and T=H_A+H_B. The strict D-height interval gives T<2.
Since H_B>1/2, also T>d+1 and hence 0<=d<1. Define

```text
xi=(T-d-1)/(1-d),       0<xi<1,
tau=(h-H_B+1)/(2-T),    0<tau<1.
```

Thus all actual cores belong to the closed containing cube
(d,xi,tau) in [0,1]^3. On that cube set

```text
T=1+d+xi*(1-d),
H_B=1/2+xi*(1-d)/2,       H_A=H_B+d,
c=d*T/(2*K),
u=K/2-c,                 v=K/2+c,
h=-1/2+(1-d)*(xi/2+tau*(1-xi)).
```

The three core centers are

```text
c_A=(1/2-K/2+c, -d-xi*(1-d)/2),
c_B=(K/2-1/2+c, xi*(1-d)/2),
c_D=(c,h).
```

The common circle equation determines

```text
Q=(K^2+d^2)*(K^2+T^2)/(4*K^2).
```

The containing cube retains nonphysical boundary points such as T=2
and H_B=1/2. A capacity certificate on this larger closed family is valid
for every actual strict core.

Since d<=1 and T<=2, the quartic identity K^4-12*K^2+4=0 gives

```text
Q <= (K^2+1)*(K^2+4)/(4*K^2)=17/4.
```

The checker verifies the identity exactly in Q(sqrt(2)).
Every square center z in the containing circle has

```text
|z| <= sqrt(Q-1/4)-1/2 <=3/2.
```

This follows from the farthest-vertex inequality
Q>=|z|^2+|z|+1/2. The row-specific bound retains Q's dependence on the
parameter rectangle rather than replacing it everywhere by 17/4.

## 3. A complete finite parameter table

Use S=2^44=17592186044416. Every parameter endpoint in the data is a
scaled integer divided by S. Start from [0,S]^3. For a box
[d_0,d_1] x [x_0,x_1] x [t_0,t_1], compare the three integer scores

```text
(d_1-d_0)*S^2,
floor((x_1-x_0)*(S-d_0)*S/2),
(t_1-t_0)*(S-d_0)*(S-x_0).
```

Bisect the coordinate with greatest score, breaking ties in the order
d,xi,tau. Use its integer midpoint rounded downward. Path bit 0 selects
the lower closed child and bit 1 the upper closed child. The score
only chooses a useful subdivision; the proof uses exact coverage,
not an asserted derivative meaning of the score.

[The human-readable parameter table](opposite_diagonal_parameter_rows.tsv)
lists the complete frontier, all parameter endpoints, all six rational
slot centers per capacity row, and every row's center-leaf count.
The full inequalities are encoded in
[opposite_diagonal_capacity_certificate.json](opposite_diagonal_capacity_certificate.json).

| Final parameter rows | Count |
| --- | ---: |
| Uniform six-slot capacity cover | 254 |
| Entire box has Q below 6241/1600 | 26 |
| Unresolved | 0 |
| **Full binary frontier** | **280** |

Maximum parameter depth is 15. Prefix-freeness and Kraft sum one,
or equivalently a full binary trie, verify complete coverage of the
closed initial cube. No boundary neighborhood is removed.

For an excluded parameter box, outward interval evaluation gives
Q_upper<(79/40)^2=6241/1600. The imported radius window therefore
excludes every actual ten-packing in that entire box.

For every other row, exact outward interval evaluation records compact
center boxes K_A,K_B,K_D and an upper bound rho on
sqrt(Q-1/4)-1/2. T,H_A,H_B,h are multi-affine functions of their respective
parameters, so their extrema occur at parameter-box corners. The center
factor c=d*T/(2*K) and Q are then bounded by outward interval arithmetic.
The exact global bound Q<=17/4 permits a harmless upper clamp at 17/4.
It is justified by the algebra above, not by numerical plausibility.

## 4. Each capacity row admits at most six additional centers

For each row, cover [-rho,rho]^2 by longest-side binary subdivision,
with x first on ties. Its leaf paths, all closed cells, are part of the
certificate. Across all 254 rows there are exactly **50,607 center leaves**,
maximum binary depth 22. Every row has its own complete binary frontier.

Each cell is assigned to one of the following:

* Outside: its minimum squared norm is strictly above rho^2.
* Existing square A, B or D: every point of the cell is within distance
  strictly below 1/2 of that physical square, uniformly for every center
  in its recorded core box.
* One of six disks: the entire cell lies strictly inside that row's
  rational disk of radius 499/1000.

The physical-square calculation is explicit. In the square's own
orthogonal coordinates let M_x,M_y bound the absolute coordinate
differences between a candidate center and every allowed core center.
Check

```text
max(M_x-1/2,0)^2+max(M_y-1/2,0)^2 < 1/4.
```

For A,B these are the global axes. For D apply the fixed diagonal
coordinate map before taking endpoint maxima. This is the squared
distance to a closed unit square, with independent coordinate maxima
only enlarging the bound. It is strictly less than 1/4 on an assigned
cell. An additional square's open inscribed disk would meet the
existing square's interior there, so no additional center can occur.

For a slot, compute the maximum squared distance from all cell corners
to its rational center and compare strictly with 249001/1000000.
For an outside cell, compute the minimum coordinate squares, using zero
when a coordinate interval contains zero.

These finite corner inequalities are all exact integer comparisons after
clearing positive denominators. Neither an optimizer nor a numerical grid
is a premise. In particular, narrow regions missed by candidate grids
were retained during construction and are covered in this final table.

Every additional center belongs to one of the row's six disks.
Each has diameter 998/1000<1 and hence contains at most one further
unit-square center. Total capacity is therefore at most 3+6=9.
The three physical core squares and every added square keep their
actual orientations throughout.

## 5. Verification and shared consequence

```text
node research/ten/check_opposite_diagonal_capacity.mjs
node research/ten/check_opposite_diagonal_capacity_60bit.mjs
```

Both arithmetic/checking bodies were executed successfully in the
session's V8 runtime. They verify all 254 capacity rows, all 26
radius-impossible rows, all 50,607 strict center-leaf inequalities,
the core boxes, the center radii and both levels of coverage.

The backends use 44-bit direct quotient intervals and 60-bit reciprocal
intervals, with separate integer-square-root implementations. The
logical predicates are shared. Coverage uses prefix/Kraft arithmetic
and full binary tries respectively. Both reconstruct the recorded
44-bit subdivisions before lifting coordinates, so midpoint rounding
cannot change the cells represented by a path. Exact Q(sqrt(2))
arithmetic verifies the quartic identity used in the radius bound.

The execution workspace remains unavailable; the Node entry points
were not run there. No independent agent review or Lean check is claimed.

**Shared corollary.** Every D transmitter with two loaded neighbors in
the selected ten-packing has unique geometric circle vertices at both
endpoints, and those two circle vertices have the same transverse sign.
The radial class is excluded by the preceding radial-D theorem, and the
opposite unique-circle class by this theorem. This is independent of
loaded count, branching count and endpoint degree.

The remaining same-sign three-body mode still needs force/torque,
additional-body or completion arguments. No additional whole master
entry is closed solely by this feature reduction. The fixed ledger
stays **277/336 closed; 59 open**.
