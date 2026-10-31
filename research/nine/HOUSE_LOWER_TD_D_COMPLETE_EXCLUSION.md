# The lower-root house TD family with a genuine D leaf is excluded

Date: October 28, 2026.

**Status: complete original-family hand proof, submitted for full root
and separate independent review.** The proof also gives a local
degree-three D-root theorem with a unit channel and an actual unit
bypass. All original forces, actual support applications and physical
units remain. No equation at a loaded degree-three body is shortened.

## 1. The original graph and the exact unit channel

The positive house block has edges

    AT, DT, AD, AB, BC, CD,

and its genuine pendant edge is BL, at the lower vertex B. Exactly
T and D carry positive block circle load. The actual positive degrees
are B3, A3, D3, T2, C2 and L1. In particular C is unloaded, A is
unloaded, and the original force CD is one of the three forces at the
loaded D. The other three physical squares of the original nine are
arbitrary and remain present.

This is exactly the original family

    M6.B5L.HOUSE.LOWER.LTD.D.

The root/load labels are Section 4.3 of
FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md. Choose the existing compatible
physical certificate, including its original strict and nonradial
point-only vertex/vertex convention, before extracting positive
multipliers. No new normal selection is made in this proof.

The actual B--C--D path has its original unloaded degree-two internal
body C. The actual A physically touches both endpoint units B and D.
The full UNIT_BYPASS_NORMAL_CHANNEL.md therefore gives a side-normal
channel of reserve exactly one. Write n for its original unit normal,
P for its B--C application and h for B's maximum-n support. Then

    h=n.P=h_B(n),
    P_CD=P+n,
    B subset {X:n.X<=h},  D subset {X:n.X>=h+1}.       (1)

This includes every actual C-side mean and both endpoints. In
particular the channel mean has not been centered. Let m be the
original B-to-A unit normal and Q the actual B--A application.
Thus Q is a maximum-m support point of B and a minimum-m support
point of A. The actual contact A--D supplies some point Z in A
with n.Z>=h+1. No force equation at A, D or T is used to obtain
any of these facts.

## 2. A degree-free bypass normal restriction

The following fact needs no leaf, circle or force equation. Whenever
the physical relations in (1) hold, a unit V meeting B at an actual
minimum-m support point Q and meeting D must satisfy

                         n.m>=0.                    (2)

Indeed, if n.m<0, the complete support-span lemma of
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, Section 1, gives

                 max_{X in V} n.(X-Q)<1.

Since Q belongs to B, n.Q<=h. Hence max_V n.X<h+1, contrary to
V touching D. This proof works for a vertex, a relative-side-interior
application and every original shared-side endpoint. It retains the
nonobtuse equality n.m=0. It does not require an additional physical
contact between V and the channel body C.

For completeness, the support-span statement follows directly in a
unit square. At a minimum-m vertex Q write V=Q+[0,1]u+[0,1]v with
orthonormal inward axes and m.u,m.v>=0. If n.m<0, at least one
of n.u,n.v is negative. The sum of their positive parts is strictly
less than one: a unit component equal to one would make the other
component zero and force n.m>=0. At a minimum-m side-interior point,
the inward m component contributes negatively and only the tangential
interval can contribute; its length is at most one and its projected
unit component is strictly below one. The vertex proof includes all
side endpoints.

Now retain the full genuine-root equation at B. If e is its leaf
direction and alpha,mu,nu are the original positive magnitudes, then

                  alpha e+mu m+nu n=0.              (3)

Dotting (3) with n and m, using (2), gives

                         e.n<0,  e.m<0.             (4)

These strict signs use the two actual nonleaf forces of the genuine
degree-three root. They are not asserted for a root of higher degree.

## 3. The whole D-root radius and normal cover

Rotate the genuine D leaf East, so e=(1,0). Its complete radial
geometry and the existing nonradial point-only convention give

    r=R-sqrt(2),  s=1-r,
    B=[-s,r] times [-b,a],  a,b>0,  a+b=1,
    P_BL=(r,0).                                      (5)

The leaf has vertices (r,0), (r+1/sqrt(2),1/sqrt(2)),
(R,0), (r+1/sqrt(2),-1/sqrt(2)). The strict transverse slider in
(5) is the genuine D-leaf/root classification: its leaf vertex meets
the relative interior of a root side. Only that geometry from
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md and Sections 1--2 of
RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md is used. The latter
file's separate two-boundary-neighbor selection theorem is not used.

Throughout the original radius domain R>sqrt(2), R^2<=1105/256,
we have 0<r<1 and a,b>0. Thus O lies in int B and h_B(n)>0.
The sharp contained-unit support bound, Section 1 of
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, applies to the actual D
in (1), regardless of its degree or load mask. It gives

    h+1<=d,  d=sqrt(R^2-1/4)-1.

Consequently all lower and critical radii are excluded immediately,
and any survivor must obey

    d=1+epsilon>1,  0<epsilon<1/60,
    R>sqrt(17)/2,  0<h<=epsilon.                    (6)

The upper epsilon bound is exact since

    (121/60)^2+1/4-1105/256=31/57600>0.

In this strict-high range the following coarse D margins suffice:

                         r>1/2,  s>1/4.             (7)

For the first use R>2 and sqrt(2)<3/2. For the second use
R<25/12 and sqrt(2)>4/3, which give r<3/4. The radius comparison
is (25/12)^2-1105/256=55/2304>0. Thus both horizontal origin
margins of B are strictly greater than one quarter.

Write n=(xi,eta). The full support of (5) gives

           h>=min(r,s)|xi|,  |xi|<1/15.

Reflect the entire physical configuration vertically so eta>0.
This is possible because n is a unit vector and |xi|<1/15. Then

                         eta>14/15.                 (8)

The full vertical component of (3), with its unchanged East leaf,
gives m_y=-(nu/mu)eta<0. Equations (4) give xi<0 and m_x<0.
Thus neither actual root normal is on a bounding axis: n strictly
exposes the upper-left root vertex and m strictly exposes the
lower-left root vertex. Their real applications are exactly

                  P=(-s,a),  Q=(-s,-b).             (9)

All possible original side means have been addressed: the force
signs themselves rule out a side-axis root normal in this D case.
No endpoint was discarded by a genericity assumption.

## 4. The actual bypass is too short

Take the actual A--D point Z already retained in Section 1. Since
Z is on D, equations (1), (8)--(9) give

    n.(Z-Q)>=h+1-n.Q
             =1+n.(P-Q)
             =1+eta>29/15>sqrt(2).                 (10)

Both Z and Q belong to the same actual unit square A. Its diameter
is sqrt(2), so n.(Z-Q)<=|Z-Q|<=sqrt(2), contradicting (10).
The last numerical comparison has the exact reserve

                      (29/15)^2-2=391/225>0.

This excludes the whole original lower-house TD D family. In fact
the proof needs only a genuine degree-three D root with one true
unloaded degree-two channel to a far unit and a distinct unit bypass
touching the root and that far unit. The far unit, the bypass and
all other units may have arbitrary genuine degrees. The proof does
not replace the far loaded D3 by a two-force body, suppress AT or
DT, alter any physical circle mask or drop any of the nine squares.

## 5. Literal direct inputs and exact scope

| Complete current source | SHA-256 | Scope used |
| --- | --- | --- |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | 7ba98ef149c1faff4ef4baeaf0b0305a38cf1153f883a3fe4bfa92087d33622d | Original house graph and lower-TD load labels only |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | 6154eee2ab1114d063b0dbd1a2800c3522cbb1b46ec44a258c1c89d8ffb9e975 | Original radial bridge and genuine D-leaf geometry |
| RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md | f3a3e4c9d82e3fa0b8fef7f7d385cf08fce88c39543bf97a74cb479d995037f9 | Sections 1--2 D-root side-interior chart only |
| UNIT_BYPASS_NORMAL_CHANNEL.md | d6008ceb18b2c8921c1f3711e6babfea3a01761487352ef4dca60579a83353b8 | Entire actual width-one channel theorem |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | ee865704904a8b2a5cab7649bdfd928008c253631abf1eb346d4950411c3afac | Section 1 degree-free support span, restated here |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md | 6f3459eaf4ca425ee2001ddb27e1ba7a1b5eb0003548498f48c610776554d3bb | Section 1 contained-unit support bound only |

No numerical pose, changed mean, post-extraction normal choice,
compilation, CI, remote mutation or shared-metadata edit is used.
