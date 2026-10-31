# Exact side-transmitter bound in an acute return-support cone, and its limitation

Date: October 29, 2026 UTC. Author: roofs continuation.

**Status: complete proposed general hand bound, with a complete analytic
limitation on a stronger proposed bound. No new original family is
declared closed by this source.** The theorem covers arbitrary actual
orientations, degrees, loads and support means at its two endpoint units.
It uses the complete original side-transmission equation at the actual
unloaded true2 bridge. The diagonal case has its separate accepted
acute-cone theorem; it is not treated as a side case.

## 1. A whole-unit support estimate at every original mean

Let E be an actual unit square, Q an actual minimum-support point or
full minimizing-side mean in inward unit direction f, and n a unit
direction with f.n>0. Then

    min_(x in E) x.n >= Q.n-|det(f,n)|.           (1)

At a strict minimizing vertex, let u,v be its two inward actual unit
own axes. The components f.u,f.v are positive. Since f.n>0,
at most one of u.n,v.n can be negative. If an inward edge w
has w.n=-r<0, use the orthonormal frame (n,Jn) to write

    f=A*n+B*Jn, A>0, A^2+B^2=1,
    w=-r*n+s*Jn, r^2+s^2=1.

Its actual inward support condition f.w>=0 implies

    A*r<=B*s<=|B|*sqrt(1-r^2),
    r^2<=B^2.

The only possible negative own-edge contribution therefore has
magnitude at most |B|=|det(f,n)|. The two unit side coordinates
range independently over [0,1], proving (1) for the full square.
If neither edge is negative, the estimate is immediate. If B=0,
the displayed support condition excludes a negative edge directly.

If the minimizing feature is a side, f is its actual inward own
normal. Motion into E along f cannot lower the n coordinate.
Motion in either direction along the minimizing side has n component
of magnitude |det(f,n)| and length at most one from any original
point or mean of that closed side. This proves (1) on the whole
side, including both endpoints and the zero-component support tie.

Applying (1) to inward direction -c and comparison direction -n
also gives, whenever c.n>0,

    max_(x in C) x.n <= Q_C.n+|det(c,n)|          (2)

for an actual minimum-support Q_C of C in direction -c.
No support point is replaced by a vertex or a selected midpoint.

## 2. Exact general side-transmitter theorem

Let B,C be actual unit squares with their unchanged actual support
points Q_B,Q_C in inward unit directions b,-c. Require

    b.c>0,
    Delta=Q_B-Q_C=lambda*b+eta*c,
    lambda,eta>=0, lambda+eta>0.                 (3)

Let N be the real unloaded true2 bridge. Keep both positive
original pair forces, their actual applications T in B and U in C,
and the complete N force and torque equations. Suppose their actual
transmission is the side alternative. The full original two-force
theorem then gives

    T-U=d_N, |d_N|=1,                            (4)

where d_N is an actual own side axis of N. Every actual mean
on the two opposite N sides is retained. No endpoint owner at B
or C is assumed, and no parallel frame is imposed on them.

**Side support-cone theorem.** Put D=|Delta|. Then

    D <= 1+|det(b-c,Delta/D)|
      <= 1+|b-c|
       = 1+sqrt(2-2*b.c)
       < 1+sqrt(2).                              (5)

The stronger direction-dependent first bound in (5) is part of
the theorem, not just an intermediate estimate. In homogeneous form
it is

    D^2 <= D+|det(b-c,Delta)|.                   (6)

To prove it, let n=Delta/D. It is well-defined because (3)
and b.c>0 give D>0. Also

    b.n=(lambda+eta*b.c)/D>0,
    c.n=(lambda*b.c+eta)/D>0.

The two whole-unit inequalities (1),(2) imply

    (T-U).n
      >=D-|det(b,n)|-|det(c,n)|.

Equation (4) gives (T-U).n<=1. In the closed positive cone,

    det(b,n)=eta*det(b,c)/D,
    det(c,n)=-lambda*det(b,c)/D.

Their signs are opposite or zero, including either vanishing cone
coefficient and the parallel case. Therefore

    |det(b,n)|+|det(c,n)|
      =|det(b-c,n)|<=|b-c|.

This proves all of (5),(6). The proof covers every original
support side mean, strict vertex, tangent-axis tie and side-transmitter
mean. It does not require the finite diagonal-avoidance convention.

## 3. A support separation greater than two alone is insufficient

The proposed stronger radius-free conclusion D<=2 does not follow
from (3),(4). Here is a complete analytic family showing the exact
limitation of that proposed general lemma. It is not an original
nine-square configuration, circle-packing certificate, candidate
stress for an original graph, or numerical pose search.

Fix an arbitrary angle in the whole continuous interval

    pi/6<theta<pi/4,
    s=sin(theta), c0=cos(theta).

Take an actual horizontal unit N with T=(1,0), U=(0,0)
as relative-interior points of its right and left sides. Thus
T-U=(1,0), and equal opposite original horizontal forces at
T,U satisfy its complete unloaded force and torque equations.

The actual endpoint units can have the inward own-axis descriptions

    B=T+[0,1]*(s,-c0)+[0,1]*(c0,s),
    C=U+[0,1]*(-s,-c0)+[0,1]*(-c0,s).

Each displayed pair is orthonormal. The entire B is in x>=1,
the entire C is in x<=0, and N is in 0<=x<=1. Their open
interiors are disjoint. T is B's unique leftmost vertex and U
is C's unique rightmost vertex, with the N horizontal contact
normal strict in the other endpoint's vertex cone.

Use the inward directions and actual support points

    b=(c0,s), c=(c0,-s),
    Q_B=T+(s,-c0),
    Q_C=U+(-s,-c0).

These are actual endpoints of the corresponding minimum support
sides; both remain valid original support-side means. They give

    b.c=cos(2theta)>0,
    Delta=(1+2s,0)
          =[(1+2s)/(2c0)]*(b+c),
    |Delta|=1+2s>2.                             (7)

All generic hypotheses hold, yet the stronger bound fails. Moreover
|b-c|=2s, so (7) attains the non-strict bound 1+|b-c| in (5).

If both original support means are required to be relative-interior,
replace the first own-edge length one in Q_B,Q_C by the same
xi with

    1/(2s)<xi<1.

Both means are then relative-side-interior and

    Delta=(1+2xi*s,0), |Delta|>2,

while the acute cone and the complete original side transmission
are unchanged. Thus discarding mean endpoints would not rescue
the proposed D<=2 claim.

## 4. Exact join with the diagonal theorem and current boundary

The separate complete source

    ACUTE_RETURN_SUPPORT_CONE_DIAGONAL_BRIDGE_BOUND_AND_TYPE_II_PERPENDICULAR_SIDE_ONLY_REDUCTION_2026_10_29.md
    SHA256 ae0ecc5190c6b92116c6f52ee8fccb375598e9152a5385cdc29ade149cfac528

proves D<=sqrt(3) for an original unloaded diagonal bridge,
under the same (3) and the retained initial finite diagonal
avoidance giving actual endpoint side owners. Its full tangent
sign and mean cover is not replaced here.

Consequently, after that original convention and the full true2
force/torque entry are supplied, a sufficient whole-bridge exit is

    D>sqrt(3),
    D>1+sqrt(2-2*b.c),                           (8)

or the sharper second inequality

    D^2>D+|det(b-c,Delta)|.

The first inequality removes the diagonal alternative; the second
removes the side alternative. This implication does not by itself
prove that any named original roof row satisfies both inequalities.
In particular the Type II perpendicular source's E>2 supplies
the first condition but does not automatically supply the second.
All original side alternatives remain until that separate exact
comparison or another complete argument has been proved.

The original true2 input is PHYSICAL_CONTACT_STRESS.md at
d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5,
Section 5. Its force/torque, real support and exact width-one
conclusion are retained in (4). No star at a higher-degree body
is used as a true2 star.

The general support and side bounds are fully proved above. The
analytic family establishes only the limitation of a proposed
generic strengthening. No circle, physical mask, original nine-unit
equation, selected normal, actual mean, identifier or status is
changed. No build, numerical search, CI, metadata mutation, remote
write or merge was used. Independent full review is required before
the new general bound is adopted as an operative input.
