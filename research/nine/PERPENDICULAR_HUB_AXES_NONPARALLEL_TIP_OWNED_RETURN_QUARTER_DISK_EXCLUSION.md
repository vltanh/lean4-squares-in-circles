# Perpendicular hub axes and a nonparallel tip-owned return force the quarter disk into the actual hub

Date: October 28, 2026 UTC. Author: house continuation.

**Status: complete proposed uniform hand exclusion, frozen for root
and separate independent full review.** The local geometric conclusion
uses the full actual loaded tip equation and no equation at either
of its other two neighbors. It retains every physical circle mask,
all original side means and their endpoints, the aligned frame of
the other boundary unit, and every original force at that unit.
The same-nine consequence follows from eight actual interior arcs.

## 1. Complete local statement and original nine-square consequence

Put Q=1105/256 and work in

    2<R<=sqrt(Q).

Let U,V,W be three distinct actual contained unit squares with
pairwise disjoint open interiors and actual physical contacts
UV,UW,VW. Their original normals U-to-V and U-to-W are two
perpendicular own side axes of U. Assume V is nonparallel to U,
positively circle-loaded, and has its entire positive pair
neighborhood exactly U,W. W physically touches the containing
circle, with arbitrary true degree, positive load, physical
circle mask, and all its other original forces retained.

Assume the actual V-to-W normal is owned by V. Keep its full
original application mean, including endpoints if VW has positive
shared length. Keep the original UV and UW applications, every
other physical contact and every completing square.

**Local theorem.** These full actual hypotheses force the closed
disk of radius 1/4 about the unchanged circle origin to lie in
the open interior of the actual U.

**Same-nine theorem.** These hypotheses are impossible inside the
original nine-square packing. Each of the other eight unchanged
units then has distance greater than 1/4 from O and contains an
actual open arc longer than pi/4 on the radius-5/4 circle. Their
eight disjoint arcs would exceed a full turn.

No force or degree premise is imposed on U. The theorem does not
require that the third neighbor of an unloaded U3 be boundary,
nor a boundary-path order, a leaf, or a guessed placement of any
extra square. The actual D02 caller is given in Section 10.

## 2. Actual perpendicular supports and the entire V-owned normal

Rotate/refelect all actual data about O so that U-to-V is North
and U-to-W is East. Write the actual U and original UV point as

    U=[L-1,L] x [H-1,H],
    P=(L-p,H), 0<=p<=1.

Because V is nonparallel to U, P is its unique bottom vertex.
Its actual inward frame is

    e_1=(c,s), e_2=(-s,c),
    c,s>0, c^2+s^2=1,
    V=P+[0,1]e_1+[0,1]e_2.                         (1)

Only the geometric direction lemma in Section 2 of
BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md is used here.
For actual neighbors of perpendicular U sides, the entire
V-to-W normal cone has Southeast signs: its x component is
nonnegative and its y component is nonpositive. That lemma
includes coincident original means and common triple contacts,
and has no force or degree premise on W.

Among V's four own axes, the only one in this quadrant is

    n_VW=-e_2=(s,-c).

Its original application therefore has the complete form

    M=P+tau*e_1, 0<=tau<=1.                         (2)

No value of this actual mean has been chosen. Write mu,nu>0
for the original UV,VW magnitudes and F for V's complete
outward circle resultant. Its full force equation gives

    F=mu*North+nu*e_2,
    F.e_1=mu*s>0, F.e_2=mu*c+nu>0,
    F_x=-nu*s<0.                                    (3)

These are the full original V2 equations, not equations
assigned to W or to a shortened higher-degree unit.

## 3. Full physical-mask cover and the coincident-mean endpoint

Put A=P.e_1, B=P.e_2. A negative own center coordinate
would make every physical circle corner have a negative
component on that axis, contrary to (3). Consequently

    A,B>=-1/2,
    (A+1)^2+(B+1)^2=R^2.                            (4)

The physical corner (A+1,B+1) is retained, including either
two-circle equality A=-1/2 or B=-1/2. At least one of A,B
is positive, because R>2.

The two original pair-force lines meet at

    q=P+(tau/s)*North,
    q.e_1=A+tau, q.e_2=B+(c/s)*tau.

The full torque about q gives det(q,F)=0. Its own coordinates
are at least those of P, one of which is positive, while
both own components of F are strictly positive. Thus q is
a positive multiple of the full F, even for a physical
two-circle mask. In particular

    P_x=q_x<0.                                      (5)

If tau=0, then q=P is a positive multiple of F, so A,B>0
and the physical V circle corner is unique. The relation
P parallel P+e_1+e_2 forces A=B>0. Hence P is V's radial
inner diagonal vertex and |P|=R-sqrt(2).
But the actual boundary W contains P. Any physical circle
corner Z_W of W would satisfy

    R=|Z_W|<=|P|+|Z_W-P|<=R-sqrt(2)+sqrt(2)=R.

Both equalities force Z_W to be V's same outer diagonal
circle corner. Two interior-disjoint unit squares cannot
share a containing-circle point: each of their right-angle
inward tangent sectors lies strictly inside the same open
radial half-plane, so the two sectors overlap. This is a
geometric fact for contained squares and does not require
a positive coefficient at the shared point. Thus tau=0
is impossible, and

    tau>0.                                         (6)

### 3.1. The physical two-circle mask B=-1/2

Here A=d=sqrt(R^2-1/4)-1>0. The actual point has

    P_x=c*d+s/2>0,

contradicting (5). Both individual zero circle coefficients
remain included; the sign was derived from the full F.

### 3.2. The physical two-circle mask A=-1/2

Here B=d and V=[-1/2,1/2]e_1+[d,d+1]e_2, with d>9/10.
The actual W lies on the inward side e_2.z<=d and contains
the unchanged point M=(-1/2+tau)e_1+d*e_2.

At any maximum-e_2 support point of a unit square, each
horizontal displacement has absolute value at most one.
For a vertex this follows because its two inward side
directions have nonpositive vertical components and opposite
horizontal signs; for a side-interior point it is the actual
length-one tangent interval. Both endpoints are included.
The total inward vertical span is at most sqrt(2). Therefore
every actual W point has own coordinates satisfying

    |x|<=3/2, d-sqrt(2)<=y<=d.

Since d>9/10>1/sqrt(2), this gives |y|<=d and hence

    |z|^2<=9/4+d^2<R^2=(d+1)^2+1/4,

with strict reserve 2d-1>0. This contradicts W's actual
physical boundary contact. The two physical V corners and
the entire original mean interval have been retained.

The only remaining physical mask is therefore the unique
opposite circle corner

    Z_V=X*e_1+Y*e_2,
    X=A+1>1/2, Y=B+1>1/2,
    X^2+Y^2=R^2.                                   (7)

## 4. The unique V2 equations force c<=s and X<Y

Write F=rho*Z_V, rho>0. Torque about the original P and
the two components of (3) are exactly

    nu*tau=rho*(B-A),
    mu*s=rho*X, mu*c+nu=rho*Y.                     (8)

Thus B>A, so X<Y and Y>sqrt(2). With q_0=c/s>0,
(8) gives

    nu/rho=Y-q_0*X>0,
    tau*(Y-q_0*X)=Y-X.

Since tau<=1, this forces q_0<=1 and hence

    0<c<=s, s>=1/sqrt(2),
    1/2<X<Y, B>sqrt(2)-1>0.                        (9)

All original mean endpoints have been used at their actual
scope; tau=1 is still retained in these enlarged inequalities.

## 5. Complete W frame and the parallel V/W exit

First suppose W is parallel to V. Its entire actual square
has the form

    W=P+[z,z+1]e_1+[-1,0]e_2,

with the full contact interval retained. Its unique minimum-x
vertex is Q=P+z*e_1. Because U-to-W is East, Q_x=L, whereas
P_x<=L gives z>=0. The actual UW point has height at most H,
but Q_y=H+z*s, so z<=0. Thus z=0.

In V-own coordinates the two whole squares are

    V=[A,A+1] x [B,B+1],
    W=[A,A+1] x [B-1,B].

Equality of their actual maximum squared radii forces B=0.
The V force sign in (3) gives A>=-1/2; R>2 then gives
A+1>sqrt(3), so its physical circle corner is unique and
A>0. But its exact torque (8) would read
nu*tau=-rho*A<0, impossible. This excludes the entire
parallel V/W shared-side branch, without replacing its mean.

Now assume W is nonparallel to V. If W is nonparallel to U,
let Q be its unique left vertex and write its inward axes

    f=(C,S), g=(S,-C), C,S>0, C^2+S^2=1.

The actual UW point Q has height at most H. The actual
VW point M from (2) has height H+tau*s>H. Therefore M
cannot be Q. Since g.e_2<0, the only possible maximum-e_2
vertex is Q+f, and necessarily f.e_2>0. Hence

    M=Q+f.

If W is aligned with U, take C=0,S=1, f=North,g=East,
M its upper-left vertex and Q=M-f its lower-left vertex.
The original UW mean is unchanged. Its existence implies
Q_y<=H; also Q_y=H+tau*s-1>H-1. Thus Q itself lies on
the actual U side, even in this aligned-frame case.

In both complete W frame cases,

    0<=C<1, S>0, C^2+S^2=1,
    Q=P+tau*e_1-f,
    L=P_x+tau*c-C,
    0<=p=tau*c-C, C<=tau*c<=c.                     (10)

Define

    gamma=c*C+s*S>0, eta=-s*C+c*S>0,
    f=gamma*e_1+eta*e_2,
    g=eta*e_1-gamma*e_2.

The complete bounds are

    gamma^2+eta^2=1,
    0<eta<=c<=s<=gamma,
    gamma>=1/sqrt(2).                               (11)

Indeed eta<=c, and gamma=sqrt(1-eta^2)>=s. No original
UW mean has been replaced in an equation; Q is used only
as an actual geometric corner contained in U.

## 6. Every W physical mask is forced to its unique right corner

The actual W is

    W=M+[-1,0]f+[0,1]g.

Both M and Q=M-f are actual physical contact points with
other squares, so neither can be a circle point by the
geometric unshareability argument in Section 3. If W's
own g-center coordinate were nonpositive, a farthest
corner would be M or Q. Since W physically touches the
circle this is impossible. Thus its g-center coordinate
is strictly positive.

Put J=A+tau. The f- and g-center coordinates of W are

    gamma*J+eta*B-1/2,
    eta*J-gamma*B+1/2>0.                            (12)

Suppose the first were nonpositive. Combining the two
inequalities in (12), with gamma^2+eta^2=1, gives

    B<(gamma+eta)/2,
    -1/2<J<=1/(2*gamma)<=1/sqrt(2).

The last lower bound uses A>-1/2 and tau>0. A farthest
W corner would be Q+g. Its V-own coordinates are

    (J+eta-gamma, B-gamma-eta).

Using B>sqrt(2)-1, gamma+eta<=sqrt(2) and (11),
its second coordinate is strictly between -1 and 0.
Its first coordinate is strictly between -3/2 and 3/2.
Consequently its squared radius is strictly below
13/4<4<R^2, a contradiction.

Both W own center coordinates are therefore positive.
The whole physical circle mask is uniquely its right
corner

    Z_W=M+g=(X-u)*e_1+(Y-v)*e_2,
    u=1-tau-eta, v=1+gamma.                         (13)

The full degree and circle equations of W were not used
or changed. This covers both original W physical masks,
either initially allowed zero individual coefficient,
and the aligned W frame C=0.

## 7. One continuous circle-ratio inequality bounds the whole domain

Let lambda=X/Y in (0,1). Equality of the two actual
circle radii in (7),(13) is

    2*Y*(lambda*u+v)=u^2+v^2.                      (14)

If u>=0, then u<=1 and 1<=v<=2. Equation (14) gives

    Y<=(1+v^2)/(2*v)<=5/4,

contrary to Y>sqrt(2). Thus u<0. Put w=-u=tau+eta-1.
Since tau<=1,

    0<w<=eta<v.

For fixed v,lambda, the function
(w^2+v^2)/(2*(v-lambda*w)) increases strictly on this
whole interval. Its derivative numerator is

    2*w*v-lambda*w^2+lambda*v^2>0.

Hence (14) and eta^2+gamma^2=1 give

    Y<=(1+gamma)/(1+gamma-lambda*eta)
      =1/(1-lambda*k),
    k=eta/(1+gamma)<=sqrt(2)-1,
    R^2<= (1+lambda^2)/(1-lambda*k)^2.              (15)

All denominators are positive. The last comparison is
strictly increasing in lambda>=0 and k>=0 throughout
the printed domain; its lambda derivative has sign
lambda+k>0.

Because sqrt(2)<99/70, one has k<29/70. If lambda<=5/6,
(15) would imply

    R^2<=11956/3025<4,
    4-11956/3025=144/3025>0.

Therefore

    lambda>5/6,
    X^2>100/61>25/16,
    Y^2<36*Q/61<64/25.                             (16)

The two last rational reserves are 75/976 and 1231/97600.
In particular

    A=X-1>1/4, B>A, Y<8/5.                         (17)

There is also a uniform lower bound for c. If c<=1/2,
then eta<=1/2 and k<=2-sqrt(3). Enlarging lambda to one
in (15) would give

    R^2<2/(sqrt(3)-1)^2=2+sqrt(3)<4,

again impossible. Thus

    1/2<c<=s,
    c+s>(1+sqrt(3))/2>4/3.                         (18)

For the sum bound, c+sqrt(1-c^2) increases on
[1/2,1/sqrt(2)]; its left endpoint is (1+sqrt(3))/2.
This is a continuous full-domain comparison, not an
orientation sample or finite pose certificate.

## 8. The actual top and right U supports both lie inside the middle half

The actual U top is the height of P:

    H=s*A+c*B=s*X+c*Y-(s+c).

Equations (17),(18) and the Cauchy inequality give

    H>(s+c)/4>1/3,
    H<=R-(s+c)<25/12-4/3=3/4.                      (19)

Here R<25/12 follows from
(25/12)^2-Q=55/2304>0.

From (10), the unchanged U right support is

    L=c*(A+tau)-s*B-C.

Since A+tau<=X<Y=B+1, B>0, c<=s and C>=0,

    L<c-(s-c)*B-C<=c<=1/sqrt(2)<3/4.              (20)

For its lower bound use the actual W circle point.
By (13), its first own coordinate X-u is positive,
whereas its second is negative: Y<8/5 and
v=1+gamma>=1+1/sqrt(2)>17/10. Therefore its actual
global x coordinate is positive. Its global coordinates
are exactly

    Z_W=(L+C+S, H+tau*s-C).

Put D=R-c-C. By (10),(18), c,C<3/4, so D>1/2.
The y coordinate obeys

    (Z_W)_y<=R-(c+s)+tau*s-C<=D.

If it is negative, (19) gives
|(Z_W)_y|<C-H<3/4-1/3=5/12<D. Thus in all cases
|(Z_W)_y|<=D. Since (Z_W)_x>0 and |Z_W|=R,

    (Z_W)_x>=sqrt(2*R*(c+C)-(c+C)^2)
       >sqrt(4*(1/2+C)-(1/2+C)^2).                (21)

The last inequality uses R>2, c>1/2, and strict
increase of 4z-z^2 for z<2; here c+C<=sqrt(2)<2.

The latter radical is strictly greater than C+S+1/4.
Indeed, using C^2+S^2=1 and S<=1, the exact difference
of the positive squares is

    4*(1/2+C)-(1/2+C)^2-(C+S+1/4)^2
      =11/16+(5/2)*C-C^2-(1/2+2*C)*S
      >=3/16+C/2-C^2
       =(3/4-C)*(C+1/4)>0.                        (22)

Therefore (21) gives L+C+S>C+S+1/4, or

    1/4<L<3/4, 1/3<H<3/4.                        (23)

The original U=[L-1,L] x [H-1,H] consequently contains
the whole closed radius-1/4 disk in its open interior.
No actual side, contact application, or force mean
has been shifted to obtain this conclusion.

## 9. All eight other physical squares give the contradiction

Because the closed quarter disk lies strictly inside
the actual U, every one of the other eight closed
units has distance strictly greater than 1/4 from O.
Compactness preserves strictness at the disk boundary.
At the nearest point of each such convex unit, its
supporting half-plane is a cap of height greater
than 1/4 about the same origin.

Section 1 of GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md
therefore supplies a connected actual open-interior
arc on |z|=5/4, of length strictly greater than pi/4,
for each of those eight unchanged squares. Their
open interiors are disjoint, so the eight arcs are
pairwise disjoint. Their total length would exceed
2*pi. This proves the same-nine theorem in Section 1.

No boundary-path routing or individual extra-square
capacity is required. All eight other physical units,
including any unloaded or physically circle-clear
completing squares, enter the contradiction together.

## 10. Literal perpendicular-axis D02 scope and remaining owners

For M6.B6.HEXAGON.D02.L01345 use the original rim
0--1--2--3--4--5--0, positive chord02 and load set
{0,1,3,4,5}, with

    U=2, V=1, W=0, T=3,
    boundary path V,W,5,4,T.

The actual degrees remain U3,V2,W3,5_2,4_2,T2, and
all three arbitrary completion units remain. In the
perpendicular U-axis branch, if V is nonparallel to
U and owns its actual VW return normal, every local
premise of Section 1 is literal. No equation at the
actual loaded W3 has been replaced by a two-force
equation. The same-nine analytic radius entry gives
R>2, and Section 9 excludes the whole stated owner
domain, including all actual UV/UW/VW means and
every original physical circle mask.

The local theorem is broader than this caller: U
may have any true degree or circle load, and W only
needs physical boundary contact. Other original
callers must retain the actual loaded V2 and the
two perpendicular U-owned normals.

The perpendicular return cases owned by W or free
in both vertex cones are not excluded by this
manuscript. Nor does it classify a V parallel to U;
the already complete both-shared adjacent chart is
a separate exit at its exact original scope. Thus
this theorem alone earns no whole D02 row, graph
parent, or coarse-cell checkbox.

## 11. Exact operative sources and proof boundary

| Source | SHA256 | Exact operative scope |
| --- | --- | --- |
| BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md | 3cd327d293d58daf2dcb8eb828dbee00efbc728171e8d17de60c3c9bc071f281 | Section 2 only: the complete geometric neighbor-normal cone at perpendicular U sides; neither two-tip force equation is used at W |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb | Section 1 only: every actual unit in a strict quarter-height cap has an actual open radius-5/4 arc longer than pi/4 |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Original D02 graph/load/degree and same-nine caller |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Original same-nine R>2 entry |

Every new corner, mean, force, and scalar comparison is printed
above. The local proof uses no generic normal change, false leaf,
artificial boundary square, or reduced force equation. Exact
rational comparisons check algebraic transcriptions only. There
is no physical pose search, mesh, computational exclusion packet,
Lean compilation, CI, workflow, ledger mutation, commit, remote
write, or original checkbox change in this manuscript.
