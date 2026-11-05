# A strict counterexample has one normalized boundary square and eight centers behind a sharp cap

November 1, 2026. This is a self-contained hand reduction of the unrestricted
existence problem. It also supplies the boundary-normalization source referred
to in the earlier archive-only handoff, without depending on that archive or
any mathematical program. The new cap guard uses
[TWO_SQUARE_SHARP_CAP_HAND_PROOF.md](TWO_SQUARE_SHARP_CAP_HAND_PROOF.md).

Set `Q=1105/256`, `R=sqrt(Q)`, and

    rho=(sqrt(1041)-8)/16,
    d=rho-1/2,
    k=sqrt(d^2+1/4),
    H=rho*d/k.

## 1. An exact equivalence for the global strict-radius problem

The following two assertions are equivalent:

1. Nine unit squares with pairwise disjoint open interiors fit in a disk
   of squared radius strictly below Q.
2. Nine **pairwise disjoint closed** unit squares fit in the closed Q-disk.

The second assertion may additionally require at least one corner on the
Q-circle. The stronger separation is part of the equivalent counterexample
domain; it is not a condition imposed on equality packings.

Write a square as `c_i+K_i`, where `K_i` is the centered unit square in its
own unchanged frame. For any unit vector n its support halfwidth is

    h_i(n)=(|n.u_i|+|n.v_i|)/2 >= 1/2.

The separating-axis theorem gives, for every interior-disjoint pair, an
actual axis n belonging to one of their two frames and a suitable sign with

    n.(c_j-c_i) >= h_i(n)+h_j(n) > 0.                 (1)

Keep every frame fixed and replace every center by `t*c_i`, using the SAME
positive t for all nine. For t>1 the left side of (1) is multiplied by t,
so every selected separator is strict. Thus the resulting closed squares
are pairwise disjoint; no individual contact is silently preserved.

The largest squared corner norm of the expanded i-th square is exactly

    F_i(t)=t^2|c_i|^2+t(|c_i.u_i|+|c_i.v_i|)+1/2.     (2)

It is continuous and nondecreasing for t>=0, and strictly increasing if
`c_i != 0`. At least one center is nonzero, since two squares with center
zero would overlap in their open half-unit disks. Consequently
`F(t)=max_i F_i(t)` is continuous, starts below Q at t=1, and tends to
infinity. Choose t>1 with F(t)=Q. Equations (1)--(2) prove assertion 2
and give a touching corner.

Conversely, suppose assertion 2 holds. A closed-disjoint pair has a strict
separating-axis inequality: its center difference is outside the closed
Minkowski sum of the two centered squares, which is the intersection of
its facet halfplanes, whose normals are the two squares' axes. There are
only finitely many pairs. Therefore a common t<1 sufficiently close to
one preserves one strict separator for each pair. Every nonzero center
then has `F_i(t)<F_i(1)<=Q` by (2). A zero center has `F_i(t)=1/2<Q`.
All thirty-six corners consequently lie strictly inside the Q-circle.
Their largest squared norm is a radius q<Q containing all nine squares.
This proves the reverse implication without a fixed positive epsilon.

This is a **global existence equivalence**. Common center scaling, rotation,
reflection and relabeling can change a positional hexagon root. They are
not valid gauges inside a fixed root unless the root map is retained.

## 2. Normalize one actual touching corner

Use assertion 2 with a touching corner, apply one common rotation, and
relabel its square as S0 so that the corner is `(R,0)`. A common reflection
in the x-axis and a harmless change of S0's frame representation give

    u0=(a,b), v0=(-b,a),
    a>=b>0, a^2+b^2=1,
    c0=(R-(a+b)/2, (a-b)/2),
    2R*b >= 1.                                         (3)

Here the touching corner is `c0+(u0-v0)/2`. To verify the entire parameter
range, the two unit edges from that corner point inward as `-u0` and `v0`.
Containment of their other endpoints gives `2R*a>=1` and `2R*b>=1`.
Both have negative x component and, because they are perpendicular,
opposite y components. Reflection exchanges a and b if necessary.
This proves (3) for every chosen touching square, including tied farthest
corners and a=b.

Conversely, every parameter pair in (3) places the whole square in the
Q-disk. The adjacent corners have squared norms `Q+1-2R*a` and
`Q+1-2R*b`. The opposite corner has squared norm
`Q+2-2R*(a+b)<=Q`. The touching corner has squared norm Q. Convexity of
the disk contains the entire square. Thus (3) is an exact one-parameter
description, not an orientation sample. Equivalently,

    1/(2R) <= b <= 1/sqrt(2),  a=sqrt(1-b^2).

All other square frames remain independent.

## 3. A new universal guard for all eight remaining centers

The sharp common-point theorem says that every Q-contained square whose
center has x-coordinate at least H contains `(k,0)`; if its center has
x-coordinate greater than H, that point is in its interior.

The selected boundary square satisfies

    x0=R-(a+b)/2 >= R-1/sqrt(2) > H.                    (4)

Here is a completely rational check of the last strict inequality:

    R>83/40,   1/sqrt(2)<71/100,   H<109/80,
    83/40-71/100-109/80=1/400>0.

The first two comparisons follow by squaring positive quantities; the
last upper bound on H is proved in the cap manuscript. Hence `(k,0)` is
strictly inside S0. Every other square must have

    x_j < H,                 j=1,...,8.                (5)

Indeed, if `x_j>=H`, its closed square would contain `(k,0)` by the same
common-point theorem, contradicting the closed-disjointness in Section 1.
The conclusion even holds for ordinary interior-disjoint packings: if a
closed square contains an interior point of another square, its interior
has points arbitrarily close to that point and the two interiors overlap.

The selected center is therefore separated from every other center in the
chosen boundary-corner direction by the quantitative gap

    x0-x_j > R-1/sqrt(2)-H > 1/400.                    (6)

These are necessary inequalities for the FULL normalized counterexample
domain, not extra assumptions on the other eight squares.

## 4. The remaining statement is explicit

To prove the unrestricted lower bound it now suffices, and is necessary,
to exclude nine squares satisfying all of the following at once:

* S0 has the exact one-parameter form (3).
* The other eight centers satisfy (5), with all their orientations free.
* Every original corner is in the Q-disk.
* Every pair has an actual strict separating-axis inequality.

The normalized boundary square, strict separators and cap guard are a
proved global reduction. They do not prove that this domain is empty.
The two-direction and strip theorems exclude their stated subdomains;
the complement still needs a complete argument. None of the 7,915
original positional root IDs is changed or declared excluded here.

No Lean, CI, solver, enumeration or mathematical script was used in this
proof. The original unrestricted lower bound and global equality
classification remain open.
