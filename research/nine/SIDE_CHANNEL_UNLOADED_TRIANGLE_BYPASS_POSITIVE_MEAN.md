# A side channel with an unloaded triangle bypass has a positive original transverse mean

Date: October 27, 2026.

**Status: complete new local hand implication, submitted for full
independent review.** The negative-mean observation was supplied by
rooted_blocks; the complete zero-mean endpoint below was derived
separately by triangle_bridges. No whole house family is claimed here.

## 1. Complete physical and force scope

Keep the original contained interior-disjoint unit squares and the
selected strict singleton normal convention. Suppose

    sqrt(17)/2 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<=epsilon<1/60.

There are positive edges A--B--C--D--A and A--T--D. The actual B
is an unloaded degree-two transmitter; C has exactly its two positive
pair neighbors B,D and positive circle load; D is unloaded with
exactly its three positive pair neighbors A,C,T. T physically touches
the circle. A and T may have arbitrary additional forces and loads.
Every actual side mean and every physical circle mask is retained.

The physical bypass D makes B side-normal with width one, by the
complete `UNIT_BYPASS_NORMAL_CHANNEL.md`. Choose actual orthonormal
coordinates (n,m), with the sign of m chosen so that D is below B.
The entire original chart is

    B=[h,h+1] times [b,b+1],
    P_AB=(h,q),       P_BC=(h+1,q),       b<=q<=b+1,
    A subset {x<=h},  C subset {x>=h+1},
    max_D y<=b<=q,    -epsilon<=h<=epsilon.             (1)

The displayed points are the actual unchanged aggregate applications.
In particular q is not the center height of B. The transverse
separation in (1) is the full geometric consequence of that same
bypass theorem, and does not require a positive BD contact.

**Theorem.** Under these complete hypotheses,

                            q>0.                       (2)

The proof uses the full C2 and D3 equations. It uses no A3 equation,
no equation at T of a shortened degree, no force at a zero-load
physical circle contact, and no motion or replacement certificate.

## 2. The precise conditional proper-port fact at C

We use the nonparallel portion of the proof of
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Lemma 2.1. Its hypothesis
that one neighbor is boundary is needed there to exclude parallel
pair forces; it is not needed for the following conditional statement:

If a loaded unit has two nonparallel positive pair forces, their
actual lines meet at a point c which is a positive multiple of its
full circle resultant F. Each actual outward application satisfies

                       P=c+ell*w,       ell>=0.        (3)

For clarity, the entire scope transfer is as follows. Coincident
applications give c equal to that actual point and both lengths zero;
the point has positive dot product with every circle corner, because
the circle radius exceeds the unit diameter. For distinct applications
and one physical circle corner, the complete rectangle calculation
in `C7_FORCE_POLYGON.md`, Section 4, excludes an exterior concurrence
using only distinctness, the impossibility of sharing a circle point,
and the actual unit-neighbor width. No boundary status of either
neighbor enters it. Thus c is in the actual unit and on its positive
circle ray, which proves (3).

For two physical circle corners use
`[d,d+1] times [-1/2,1/2]` and write the circle direction as
`(d+1,eta)`, `|eta|<=1/2`. The first normal-line calculation in
Section 5 of that source excludes a concurrence to the left of
x=d using only the same distinctness and width facts. A concurrence
inside the rectangle gives (3). If it lies to the right of x=d+1,
the only possible non-circle applications are on the inner face or
its endpoints; the outer face is forbidden by width. Two distinct
applications force the concurrence's transverse coordinate into
[-1/2,1/2], including both equalities. Each vector from that
concurrence to an inner application points along its outward normal.
This is exactly (3), without asserting the concurrence is inside.
Its first coordinate is positive in every retained case. This proves
the conditional fact for both physical masks and all individual weights.

Parallel forces will be handled separately below; their exclusion is
not borrowed from the boundary-neighbor premise of that lemma.

## 3. A negative q is impossible with nonparallel C forces

Let lambda>0 be the unchanged B channel magnitude, nu>0 the CD
magnitude, and g the unit normal from C to D. The full C2 force is

                         F_C=lambda*n-nu*g.            (4)

Assume its two pair normals are nonparallel. By (3), the incoming
channel point and its concurrence satisfy

    P_BC=c-ell_0*n,       ell_0>=0,
    P_CD=c+ell_1*g,       ell_1>=0,
    c=alpha*F_C,          alpha>0.                     (5)

Consequently c_y=q. If q<0, equations (4)--(5) give g_y>0.
But (1) and the actual CD point then give

             q<=q+ell_1*g_y=(P_CD)_y<=max_D y<=q.

Every comparison is equality. In particular P_CD is a maximum-y
point of D, whereas D's original outward normal there is -g and
has strictly negative y component. This is impossible for a unit
square. At a maximum-y vertex both outward side normals have
nonnegative y components, as do all normals in their cone; the
same statement holds at an entire maximum-y side and its endpoints.

If q=0 in the nonparallel alternative, (4)--(5) instead give
g_y=0. This makes the two C pair normals parallel, another
contradiction. Thus the entire nonparallel row already has q>0.

## 4. The complete parallel C row

If the two C normals are parallel, they cannot have opposite signs.
The axis is the full circle-resultant axis; a force toward its outer
end would apply at an unshareable circle corner, or at the outer
radial face whose support leaves less than unit width in the disk.
Thus both original outward normals are -n.

The full parallel-load classification in
`PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md`, Lemma N.4, applies to
their actual weighted mean, without replacing either original mean.
It gives the exact radial S or D shape. The radial D inward support
is R-sqrt(2), whereas (1) gives the actual C minimum support

                     h+1>=1-epsilon>59/60.

Since R-sqrt(2)<25/12-7/5=41/60, the D possibility is excluded.
Hence C is the actual radial S square

                  C=[d,d+1] times [-1/2,1/2],
                  h=d-1=epsilon.                      (6)

Write the actual CD application as (d,z). Its membership in D
and (1) imply z<=q. The full unchanged C torque is

                         lambda*q+nu*z=0.             (7)

If q<0 both terms are negative, impossible. At q=0, equation (7)
forces z=0. It remains to exclude this exact endpoint, rather than
discard it through a strict properness assertion.

## 5. The exact zero-mean geometry and D3 contradiction

Suppose q=0. Equations (1),(6),(7) give

    P_CD=(d,0),       max_D y=0,       b=0,
    B=[epsilon,d] times [0,1].                        (8)

The original DC normal is n, so P_CD is also a maximum-x point
of D. A unit square with a common maximum-x and maximum-y point
must be parallel to those two axes: its perpendicular inward axes
both belong to the closed Southwest quadrant, hence they are its
two boundary rays. Thus

                     D=[epsilon,d] times [-1,0].       (9)

The original AB mean is (epsilon,0), a B vertex. If A did not own
n, this would also be A's unique maximum-x vertex, giving a
singleton vertex/vertex contact carrying B's side-axis normal.
The original strict singleton convention excludes it. Therefore
A owns n and is parallel, with the complete chart

             A=[epsilon-1,epsilon] times [a-1,a],
             0<a<=1.                                 (10)

The weak membership initially gives 0<=a<=1. The endpoint a=0
would again make AB a singleton aligned vertex contact with the
axis normal n, so it is excluded independently of the original
mean's position inside a nondegenerate shared segment.

If 0<a<1, the actual AD intersection has positive side length.
Its outward normal from D is -n. Full D3, whose DC normal is n,
therefore makes its original DT normal parallel to n. It cannot
be +n: T would lie in x>=d while A lies in x<=epsilon=d-1,
contrary to the actual AT contact. Thus it is -n. Both actual
DA and DT application heights are at most zero, and the DC
height is zero. Their complete D3 origin torque, with positive
coefficients, forces the DT height to equal zero. Its actual
application is then (epsilon,0). That point cannot belong to
the physical boundary unit T, because

            epsilon<1/60<R-sqrt(2)

and the distance from any point of a boundary unit to its radius-R
corner is at most sqrt(2).

If a=1, A lies in y>=0 and its AD intersection is the singleton
(epsilon,0). The unchanged strict singleton convention makes
the outward DA normal strictly Northwest. Its y component is
positive. The original DC normal has zero y component, so full
D3 forces the original DT normal w to have w_y<0. Every actual
maximum-w feature of D is consequently on its bottom side y=-1,
including its two vertices. At the same genuine point P, T
minimizes w. The complete strict unit support-span lemma, with
direction e_y and w dot e_y<0, gives

                       max_T(y-P_y)<1.

Thus every T point has y<0, contrary to its physical contact with
A subset {y>=0}. This includes a South-owned DT mean and both
strict bottom-vertex normal sectors. All actual AD/DT means are
retained in the preceding row as well.

These two exhaustive A frames exclude q=0 and finish (2).

## 6. Literal house application and retained scope

In the house hub-TC.S or hub-TC.D domain the positive graph is
AT,DT,AD,AB,BC,CD plus the genuine leaf at A; the only loaded
block vertices are T,C. Hence B2,C2,D3 and physical T are exactly
as in Section 1, with A's full four forces untouched. The actual
genuine leaf gives a point of A at distance at most epsilon after
the low-radius channel contradiction. Sharp contained-unit support
gives h<=epsilon, and that actual point gives h>=-epsilon.
The physical bypass supplies the remaining chart (1). Therefore
the theorem applies to each literal house leaf type.

This is only a necessary sign theorem. It excludes neither the
positive-q house row nor its three-extra completion. All nine
actual units remain, no physical circle mask is discarded without
proof, and no post-extraction normal or mean is changed. The
existing strict singleton selection is the sole normal convention
used here. No ledger, frozen cover, remote state, Lean compilation,
or CI operation is modified.

## 7. Literal prerequisite pins

| Source | SHA-256 |
| --- | --- |
| `UNIT_BYPASS_NORMAL_CHANNEL.md` | `d6008ceb18b2c8921c1f3711e6babfea3a01761487352ef4dca60579a83353b8` |
| `TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md` | `0d61292a0aa57084b88b4a72754fc78e123e8b684dac09be966fb074ab58e877` |
| `C7_FORCE_POLYGON.md` | `d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089` |
| `PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md` | `6f28e0fc0631928506de027dfe5609e8d5adf42a1551eef955a6d2f1acad7b6e` |
| `UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md` | `ee865704904a8b2a5cab7649bdfd928008c253631abf1eb346d4950411c3afac` |
| `PHYSICAL_BODY_GRAPH_UNCROSSING.md` | `eb26f19b27dc7327f80a64ccfd1febb542c5915aadcf95227e35765b20d3509a` |
| `FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md` | `e90f5724065c9b65d2a3938f65a76820168d7448194cd0f716f01430588cb7d8` |
