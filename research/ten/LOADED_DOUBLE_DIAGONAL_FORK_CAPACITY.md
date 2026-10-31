# A loaded degree-two double-D fork has total capacity at most nine

**Status:** complete shared capacity theorem and whole-case exclusion.
Two exact arithmetic backends checked the finite tables in this
single-agent session. No independent agent review or Lean verification
is claimed. All geometric circle multiplicities are covered through the
cited universal D-endpoint exclusions.

## 1. Statement and the fixed cases it covers

Work with the jointly selected physical certificate in
79/40<=R<=3/sqrt(2). Suppose a loaded body C has degree two, both incident
paths are D transmitters, and their other endpoints A,B are loaded.

**Theorem.** The five physical squares C,A,B,D_1,D_2 admit at most four
additional unit squares. Total packing capacity is at most nine.
The theorem is independent of endpoint degrees at A,B and of the
remaining graph, loaded count, contact ownership and added orientations.

In a whole mixed simple cycle this excludes every cyclic occurrence of
DLD. In the fixed inventory it covers:

| Cycle length | Fixed signatures containing cyclic DLD |
| --- | ---: |
| 6 | 3 |
| 7 | 4 |
| 8 | 9 |
| 9 | 14 |
| 10 | 31 |
| **Total** | **61** |

Sixty were already closed by other arguments. The newly closed entry is
**C20-M06-L04-B02-T03**, canonical word **LLLDLD**. Thus the fixed
master advances to **278/336 closed, 58 open**, with cycles
**251/279 closed, 28 open**. The denominator and immutable obligations
do not change. [All 61 covered IDs](loaded_double_diagonal_fork_cycle_coverage.json) are committed alongside this
proof; alternative existing proofs are not counted twice.

## 2. The three loaded frames and circle features are fixed

[Generic normal selection](GENERIC_CONTACT_NORMAL_SELECTION.md) makes
each D contact a relative side-interior contact on its neighbor.
Consequently the frames of A,B,C are parallel.

The [radial-D capacity corollary](RADIAL_DIAGONAL_THREE_BODY_CAPACITY.md)
excludes every radial geometric endpoint of a loaded-to-loaded D path,
including a zero coefficient at one of its two circle vertices.
Thus C has a unique circle vertex. Its two positive contact forces
cannot be parallel: their sum would be along one square axis, whereas
a unique circle vertex has both frame coordinates strictly nonzero.
The two D directions are therefore perpendicular. Choose them left
and down, so

```text
Z_C=(X,Y),       X,Y>1/2,       X^2+Y^2=Q=R^2,
C=[X-1,X] x [Y-1,Y].
```

Put K=2+sqrt(2), U=K-X and V=K-Y. The neighboring squares are wholly
left and below, respectively, since X,Y<=R<K-1. The
[opposite-sign D exclusion](OPPOSITE_DIAGONAL_CAPACITY.md) forces their
unique circle vertices to have the same transverse signs as C.
Consequently

```text
a=sqrt(Q-(K-X)^2)>1/2,       b=sqrt(Q-(K-Y)^2)>1/2,
A=[X-K,X-K+1] x [a-1,a],
B=[b-1,b] x [Y-K,Y-K+1].
```

A and B are distinct. Otherwise the vertical D would put A wholly below
C by a gap sqrt(2), while the horizontal D requires A's vertical side
interval to overlap C's in its relative interior. The two transmitters
are distinct positive degree-two bodies as well.

Containment of the endpoint unit sides gives

```text
X,Y >= K-sqrt(Q-1/4) > K-33/16 > 4/3.
```

For example sqrt(17)/2<33/16 follows from 1088<1089, and
K>17/5 gives K-33/16>107/80>4/3. Since Q<=9/2, it follows that

```text
X^2,Y^2 < 9/2-16/9=49/18<25/9,
4/3<X,Y<5/3<K/2.
```

Hence a<Y and b<X, by
Y^2-a^2=K*(K-2X)>0 and X^2-b^2=K*(K-2Y)>0.
Exchange the axes and labels if needed to assume X>=Y.

## 3. Source force and torque leave only one D-height parameter

Let h_1 be the horizontal D contact height and h_2 the vertical D
contact's horizontal coordinate. Relative side-interiority gives

```text
Y-1<h_1<a,       X-1<h_2<b.
```

The two D centers are

```text
c_D1=(X-K/2,h_1),       c_D2=(h_2,Y-K/2).
```

Both have diagonal square axes (1,1)/sqrt(2),(-1,1)/sqrt(2).
Write mu_1,mu_2>0 for their magnitudes and lambda>0 for C's circle
coefficient, absorbing the common circle-normal scale. C's force
balance gives mu_1=lambda*X and mu_2=lambda*Y. Its origin torque is

```text
mu_1*h_1-mu_2*h_2=0,
h_2=(X/Y)*h_1.
```

Since X>=Y, all actual heights are therefore exactly covered by

```text
L=Y-Y/X,       H=min(a,Y*b/X),       L<H,
h_1=L+tau*(H-L),       0<tau<1.
```

Here L>=Y-1. Both transmitter contacts retain their complete allowable
intervals; no height is normalized to a midpoint.

## 4. A compact three-variable family contains every realization

Use the half-angle t for C's circle vector:

```text
c=(1-t^2)/(1+t^2),       s=2*t/(1+t^2),
X=sqrt(Q)*c,            Y=sqrt(Q)*s.
```

X/Y<5/4 gives Y/X>4/5>3/4=tan(2*atan(1/3)).
Along with X>=Y, this proves

```text
1/3<t<=sqrt(2)-1<5/12.
```

Thus every physical fork lies in the fixed containing box

```text
6241/1600<=Q<=9/2,       1/3<=t<=5/12,       0<=tau<=1.
```

The exact five center formulas are

```text
C:  (X-1/2,Y-1/2),
A:  (X-K+1/2,a-1/2),
B:  (b-1/2,Y-K+1/2),
D1: (X-K/2,h_1),
D2: ((X/Y)*h_1,Y-K/2).
```

The sign condition X>=Y, circle side constraints a,b>=1/2, and L<H
are retained as necessary conditions. Boundary points not belonging
to a strict physical certificate may remain in this containing family.

## 5. Full exact parameter and center tables

Let S=2^44=17592186044416. The outward initial integer endpoints are

```text
Q:   [68620520689500,79164837199872]/S,
t:   [5864062014805,7330077518507]/S,
tau: [0,17592186044416]/S.
```

At each binary split compare 2*width(Q),16*width(t),width(tau),
selecting the greatest and breaking ties Q,t,tau. Bisect at the integer
midpoint rounded downward. Closed children share the bisecting boundary.
The scores choose a useful finite subdivision and have no other role
in the proof.

[The complete parameter table](loaded_double_diagonal_fork_parameter_rows.tsv)
prints every path, endpoint, disk center and center-leaf count.
[The full certificate](loaded_double_diagonal_fork_certificate.json)
records all core boxes and every center-leaf assignment.

| Final parameter rows | Count |
| --- | ---: |
| Uniform four-slot capacity cover | 358 |
| Circle-side constraint impossible throughout box | 19 |
| D-height interval impossible throughout box | 60 |
| Unresolved | 0 |
| **Complete binary frontier** | **437** |

Maximum parameter depth is 14. The paths are prefix-free with Kraft
sum one, equivalently the leaves of a full binary tree, and cover the
entire closed initial box. No boundary neighborhood or pending cell
is discarded.

All functions are enclosed by outward-rounded integer intervals.
For c,s use their rational formulas, with s increasing on this t range.
To sharpen circle radicands, note that

```text
F(Q,z)=Q-(K-z*sqrt(Q))^2
```

is increasing in Q and z for this domain: its derivatives are
1-z^2+K*z/sqrt(Q)>0 and 2*sqrt(Q)*(K-z*sqrt(Q))>0.
Thus corner evaluations bound a^2=F(Q,c) and b^2=F(Q,s).

If either radicand's upper bound is below 1/4, the whole parameter box
is impossible. Otherwise intersect its lower bound with 1/4 before
taking the square root: this is a conditional enclosure for every actual
loaded endpoint, not an assertion that every point of the box is physical.
Likewise, a height row is excluded only if H_upper<=L_lower.
The upper bound for min(a,Y*b/X) is the minimum of the two upper bounds,
and its lower bound the minimum of the two lower bounds.
Enclose h_1 by evaluating its affine tau expression at both tau endpoints
and taking their interval hull.

Every capacity row records five compact center boxes and an upper radius

```text
rho >= sqrt(Q_upper-1/4)-1/2.
```

The farthest-vertex inequality Q>=|z|^2+|z|+1/2 puts every additional
unit-square center inside the disk of that radius.

For each row, a second full binary tree covers [-rho,rho]^2, splitting
the longer side, x first on ties. Across all rows it has **44,567 leaves**,
maximum depth 22. A leaf is assigned to:

* Outside the possible center disk, by a strict minimum-norm inequality.
* One of C,A,B,D1,D2, by uniform distance strictly below 1/2 from that
  existing physical square.
* One of four rational disks of radius 499/1000, by a strict maximum
  squared-distance inequality at the cell corners.

The physical-square test is the explicit truncated-square distance
formula in the radial-D and opposite-sign capacity proofs. Use the
global axes for C,A,B and diagonal axes for D1,D2, maximizing over the
candidate cell and recorded core center box. An added square's open
inscribed disk cannot meet any existing square's interior, so every
physical-square leaf is excluded.

Each of the four disks has diameter 998/1000<1. It contains at most one
further unit-square center. All additional centers lie in those disks,
so total capacity is at most 5+4=9, proving the theorem.

## 6. Verification, fixed cycle coverage and remaining work

```text
node research/ten/check_loaded_double_diagonal_fork.mjs
node research/ten/check_loaded_double_diagonal_fork_60bit.mjs
```

Both arithmetic/checking bodies ran successfully in the session's V8
runtime. They verify all parameter rows, all 44,567 strict center-leaf
inequalities, core boxes, radii and both levels of coverage. The
44-bit direct-division and 60-bit reciprocal backends have separate
integer-square-root implementations. Logical predicates are shared.
Coverage uses prefix/Kraft arithmetic and full binary tries respectively.

The second backend reconstructs the recorded 44-bit subdivision before
lifting endpoints; midpoint rounding cannot change the geometry of a
path. The unavailable execution workspace prevented running the Node
entry points. No independent agent review or Lean verification is claimed.

The theorem excludes every cyclic DLD in a whole selected simple cycle.
Therefore loaded-to-loaded D paths in every surviving cycle form a
matching on its loaded vertices. The same local fork is excluded in
branching components whenever C has degree two and both other terminals
are loaded. D paths with unloaded retained terminals remain outside this
statement.

The unrestricted lower bound is still open. The remaining fixed list is
30 branching families, 5 SS-cycle families, 9 D-cycle families without SS,
and 14 single-S-cycle families. Equality and Lean integration have their
separate unfinished gates.
