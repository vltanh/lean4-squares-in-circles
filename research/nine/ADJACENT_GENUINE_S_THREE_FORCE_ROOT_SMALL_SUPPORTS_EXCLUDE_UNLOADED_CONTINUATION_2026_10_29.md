# Adjacent genuine three-force roots exclude an unloaded continuation

Date: October 29, 2026 UTC. Author: block_forests continuation.

**Status: complete proposed hand theorem, frozen for full independent
review.** A uniform full-star normal estimate and a force-free center
bound exclude a real unloaded two-force continuation next to two
adjacent genuine three-force roots. The theorem keeps all original
means and needs no support-normal owner choice, physical-boundary
premise at the channel's far square, or force equation there.

In the remaining five-cycle with three consecutive genuine roots,
both private vertices must therefore carry positive circle load. This
removes every other private load mask simultaneously, in both original
middle-root force branches. It is a necessary reduction of that whole
graph family, not yet its complete exclusion. No original fine or
coarse flag changes here.

## 1. Exact radius and actual-star hypotheses

Keep the original nine actual unit squares, their pairwise disjoint
open interiors, the unchanged circle origin O, and the same original
compatible selected physical-stress certificate. Work in

    sqrt(17)/2 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<=epsilon<1/60,
    M=d+1/2=3/2+epsilon<91/60.                     (1)

An actual genuine S leaf in direction e is the occupied square

    L=[d,d+1]e+[-1/2,1/2]Je.

Its genuine root contains the actual radial application d*e and
the actual inward-unit-segment endpoint epsilon*e. The latter fact
is geometric: at any supporting point of a unit, subtracting its
unit outward support normal stays in that same unit. At a vertex
the two inward coefficients are in [0,1]; at an own side the full
original mean translates to the opposite side. Thus it includes
every original mean and endpoint.

For an actual square X write h_X(n)=max_{x in X} n.x for its
support in unit direction n. A *small-support genuine three-force
root* below means precisely an actual genuine S root with true
positive degree three, its real leaf and exactly two other positive
neighbors, for which both unchanged outward nonleaf normals obey

    h_X(n_1)<=epsilon, h_X(n_2)<=epsilon.          (2)

The root is physically clear by the genuine-leaf geometry. Its full
actual equations are therefore

    alpha*e+mu*n_1+nu*n_2=0,
    mu*det(P_1,n_1)+nu*det(P_2,n_2)=0,
    alpha,mu,nu>0.                                (3)

The genuine leaf has its original zero radial origin moment. No
other original positive force or moment is omitted from (3).

**Theorem A: uniform normal cone.** Every root satisfying (2)--(3)
has both original nonleaf unit normals within Euclidean distance
strictly less than 1/10 of -e:

    |n_1+e|<1/10, |n_2+e|<1/10.                   (4)

No force equation, degree, mask, or boundary status at either other
neighbor is assumed in this statement.

**Theorem B: no unloaded continuation.** Let B be an actual
small-support genuine three-force root, with real leaf L_B and
one original positive neighbor A. Suppose A is also a genuine S
root of true positive degree three, with its own real leaf L_A
and exactly the two nonleaf neighbors B,P. Suppose P is an actual
unloaded square of true positive degree two, with its other actual
positive neighbor Q. Then the original configuration is impossible.

Q retains arbitrary true degree, circle load, physical mask and
all its other forces. It may equal B. It cannot equal L_B, because
L_B has true degree one with neighbor B and P differs from B.
The proof does not replace the A--P--Q channel by an edge or delete
the physical P.

## 2. Full support-only alignment and exhaustive root-normal cover

The complete small-nonleaf-support theorem a729b8eb applies to all
of the actual nonleaf terms in (3). It aligns this genuine S root
with its real leaf. Rotate that one whole root description so e=E:

    X=[epsilon,d] x [-b,a],
    a,b>=0, a+b=1,
    P_XL=(d,0).                                    (5)

We reproduce the complete support/force cover at true degree three;
this portion uses only (2), not near points in the other units.

East is impossible since h_X(E)=d>epsilon. Suppose an original
nonleaf normal is North, with magnitude mu and actual mean (x,a).
Its support gives a<=epsilon, so b>=1-epsilon>59/60. The other
full original force is (-alpha,-mu), strictly Southwest, at
(epsilon,-b). The entire torque gives, with k=alpha/mu>0,

    x=epsilon+b*k,
    k<=1/b<60/59.

Its actual support is consequently

    (b-epsilon*k)/sqrt(1+k^2)
       >(59/60-1/59)/(3/2)
        =3421/5310>epsilon.                       (6)

The denominator comparison has reserve
9/4-1-3600/3481=3005/13924>0. The numerator is positive, so
the comparison has the stated direction. Both ends of the original
North-side interval x in [epsilon,d] are retained. Reflection
excludes South.

Suppose next the normal strictly exposes the upper-right vertex:
n_1=(c,s), c,s>0, c^2+s^2=1, P_1=(d,a). Since d>=1>=a,
its support d*c+a*s>a: for a>0 use c+s>1, and for a=0
use d*c>0. Thus a<epsilon and b>59/60. The full
other force is (-alpha-mu*c,-mu*s), applied at (epsilon,-b).
The entire torque is

    mu*(s-c)=b*alpha.

With k=alpha/mu, this gives

    k+c=(s-a*c)/b<=s/b.

The other actual support is therefore at least

    (b-epsilon/b)/sqrt(1+b^(-2))>3421/5310>epsilon.

The positive-numerator argument is the same as (6). Reflection
excludes the lower-right strict vertex. These exclusions cover the
entire original normal circle, including its four own axes.

Every remaining normal has negative horizontal component. If one
is West, the full vertical equation in (3) makes the other West.
Otherwise they strictly expose the two left vertices. After
exchanging the labels if necessary, the exact actual data are

    P_1=(epsilon,a), n_1=(-c,s),
    P_2=(epsilon,-b), n_2=(-c',-s'),
    c,s,c',s'>0,
    mu*s=nu*s', a*mu*c=b*nu*c'.                    (7)

These full equations force a,b>0. In particular no zero transverse
extent is dropped by a generic-position assumption. They give one
common positive number

    T=a*c/s=b*c'/s'>0,

and hence the exact unchanged directions

    n_1=(-T,a)/sqrt(T^2+a^2),
    n_2=(-T,-b)/sqrt(T^2+b^2).                     (8)

This is just an identity from the original forces and moments.
No concurrency membership or normal-selection theorem is needed.

## 3. The whole nonparallel cone has a uniform small width

For either z=a or z=b, its actual support bound in (2) is

    (z^2-epsilon*T)/sqrt(T^2+z^2)<=epsilon.

It implies

    z^2<=2*epsilon*T+epsilon^2.                    (9)

If the numerator is nonpositive, this is immediate. Otherwise both
sides are nonnegative and squaring gives
z^4-2*epsilon*T*z^2<=epsilon^2*z^2; division by z^2>0
gives (9). This keeps equality and does not square an unproved sign.

If epsilon=0, (9) contradicts z>0. Thus at the critical endpoint
only the parallel West case occurs, and (4) holds directly.

For epsilon>0 put m=max(a,b)>=1/2. Applying (9) to m gives

    T >= (m^2-epsilon^2)/(2*epsilon).

The function x/(x^2-epsilon^2) strictly decreases for x>epsilon.
Therefore each original transverse normal component satisfies

    |n_i.y| <= m/T
       <=2*epsilon*m/(m^2-epsilon^2)
       <=4*epsilon/(1-4*epsilon^2)
       <60/899<4/59.                              (10)

The penultimate bound uses the full endpoint epsilon<1/60;
the last exact reserve is 56/53041. Both normal horizontal
components are strictly negative. For n=(-c,plus_or_minus_s),
with c>0, the exact identity gives

    |n+E|^2=2*(1-c)=2*s^2/(1+c)<=2*s^2.

Since sqrt(2)<10/7,

    |n+E|<40/413<1/10,                            (11)

with reserve 13/4130 in the final comparison. This proves Theorem A
over the entire normal, mean and force-ratio domain. In the parallel
case the distance is zero. No division into sampled orientations or
selection of a small force has entered the argument.

## 4. A force-free contained-center cap next to an occupied radial leaf

Every actual unit K in the original disk has center c_K satisfying

    |c_K|<=M=d+1/2.                                (12)

Indeed, with its actual orthonormal axes u,v, a farthest corner has
squared norm

    |c_K|^2+1/2+|c_K.u|+|c_K.v|
      >=|c_K|^2+|c_K|+1/2.

The positive increasing function on the right equals R^2 at
|c_K|=d+1/2, by (1). This proves (12) for every orientation.

Now suppose a unit direction n and an actual contained unit K have

    min_{x in K} n.x>=1-epsilon.                   (13)

Its directional halfwidth is at least 1/2, so

    n.c_K>=3/2-epsilon=M-2*epsilon.

Combining this with (12) gives

    |c_K-M*n|^2
       <=2*M^2-2*M*(M-2*epsilon)
        =4*M*epsilon<91/900<1/9.                 (14)

Thus |c_K-M*n|<1/3. The last squared reserve is 1/100;
epsilon=0 is included and makes the left side zero.

Let L be the actual occupied radial S leaf in direction e; its
center is exactly M*e. If also

    |n-e|<3/10,

then the two actual centers satisfy

    |c_K-c_L|
       <=|c_K-M*n|+M*|n-e|
       <1/3+(91/60)*(3/10)
        =473/600<1.                               (15)

Distinct unit squares have open incircles of radius 1/2. Equation
(15) makes those two open incircles intersect, contradicting
interior disjointness of the actual squares. Its strict reserve
is 127/600. No load, boundary contact, owner or force equation at
K is a premise of this geometric obstruction.

## 5. The real unloaded channel supplies both needed support bounds

We prove Theorem B with all the stated actual degrees. Let n be the
unchanged original unit normal from A to P. True unloaded P2 force
balance makes its other original outgoing normal to Q equal to n,
with the same positive magnitude. The two original application
means remain at the opposite actual supporting faces of P. Full
torque retains their usual common force line; no mean is moved.
If w is P's actual width in direction n, then w>=1 and the actual
support equalities are

    min_Q n = h_A(n)+w.                            (16)

This is an equality between original physical support lines, not a
contracted graph edge. P and all its actual corners remain present.

The contained-center bound gives min_Q n<=M-1/2=d, whence

    h_A(n)<=d-w<=epsilon.                         (17)

For A's other actual nonleaf edge AB, its real neighbor B contains
epsilon*e_B. The unchanged support separation therefore gives

    h_A(n_AB)<=n_AB.(epsilon*e_B)<=epsilon.        (18)

Thus A satisfies the complete small-support hypotheses, established
from the actual near point and the real channel rather than assumed
for a boundary neighbor. Apply Theorem A to the full true A3 and
the full true B3. Let m=n_AB; the original B-to-A normal is -m.
The two exact full-star cone conclusions give

    |n+e_A|<1/10, |m+e_A|<1/10,
    |m-e_B|<1/10.

Consequently

    |n-e_B|
       <=|n+e_A|+|m+e_A|+|m-e_B|<3/10.           (19)

A itself contains epsilon*e_A, so its actual support also has
h_A(n)>=n.(epsilon*e_A)>=-epsilon. Equation (16) now gives

    min_Q n>=1-epsilon.                            (20)

Apply the force-free obstruction (13)--(15) with K=Q and the
occupied genuine L_B. These are distinct actual units by their
true degrees, as stated in Section 1. Equations (19)--(20) force
their interiors to overlap. This proves Theorem B.

Nothing in this proof supposes Q is loaded or physically boundary.
No force at Q, additional root force, circle atom, chosen normal
or original shared mean has been deleted. The sole exact-degree
uses are the two genuine root3 equations and the real unloaded P2
equations, at precisely their stated true degrees.

## 6. Useful whole-star corollaries

Suppose A and B are adjacent genuine S roots, each of true degree
three, and A's other nonleaf neighbor is an actual unloaded2 P.
Then B's other original nonleaf support must be strictly greater
than epsilon. Its support toward near A is already <=epsilon;
if the other one were <=epsilon as well, Theorem B would apply.
This is a necessity for that actual selected normal, not an
assertion about a conveniently reselected support.

In particular the configuration is impossible whenever B's other
nonleaf neighbor contains a point of D_epsilon. The same holds
whenever that other neighbor is itself a true unloaded2 transmitter:
the exact same real-channel bound (16)--(17) supplies its small
support. These implications retain arbitrary true degrees and
physical masks at the far ends of either actual channel.

If B is a genuine true-3 root adjacent to two other genuine roots
A,C, both of its nonleaf supports are <=epsilon from their real
near points. Whenever A is also true degree three, its other
nonleaf neighbor cannot be unloaded true degree two. The same
statement holds at C when C has true degree three. There is no
assumption of an AC edge and no contraction of an intervening
private network.

## 7. Literal consequences for every current five-body rooted family

In the original five-body block plus three distinct genuine leaves,
the accepted arbitrary-degree high-S theorem supplies (1) with
epsilon>0, the three real near points, and clear genuine roots.
The exact graph-only and protected-network covers leave six
families after the already complete C5 spacing (2,2,1) exit.
The following table checks actual total positive degrees, including
each genuine leaf, before invoking any new theorem.

| Current family | Exact original graph and roots | Actual root/private degrees | New conclusion or precise nonapplication |
| --- | --- | --- | --- |
| C5 spacing (3,1,1) | Cycle A-B-C-Q-P-A; roots A,B,C | A3,B3,C3,P2,Q2 | B has both genuine near nonleaf neighbors. If P is unloaded, use Theorem B at roots A,B and actual channel A-P-Q. If Q is unloaded, use roots C,B and channel C-Q-P. Therefore both P and Q have positive circle load. |
| House ADT | Edges AT,DT,AD,AB,BC,CD; roots A,D,T | A4,D4,T3; private B2,C2 | T satisfies the small-support root3 premise, but both adjacent genuine roots are true degree four. Neither can be replaced by A3. This theorem does not remove a load mask here. |
| House ADB | Same house edges; roots A,D,B | A4,D4,B3; private T2,C2 | Both private vertices are already loaded as true2 units between near roots. No new unloaded endpoint is supplied; the high-degree A,D stars stay intact. |
| House ABC | Same house edges; roots A,B,C | A4,B3,C3; private D3,T2 | B is a small-support root3 and C is true3, but C's other neighbor D is true degree three, so it is not the channel P of Theorem B. The private T2 is adjacent to A4 and D3. No unloaded-D3 substitution is valid. |
| Fan H12 | H joined to every vertex of path 1-2-3-4; roots H,1,2 | H5,1_3,2_4; private 3_3,4_2 | Root 1 is small-support true3, but its genuine neighbors have true degrees five and four. Private 4 is not an unloaded2 continuation from a true3 genuine root. No new whole-family exclusion. |
| Fan H23 | Same fan; roots H,2,3 | H5,2_4,3_4; private 1_2,4_2 | Both private true2 units lie between near roots and are already loaded. There is no true3 genuine root for the new cone theorem. |

The omitted other C5 spacing (2,2,1) is already excluded by the
accepted outer-neighbor theorem. Even before that exit, each of
its two private vertices is loaded by the direct near-root channel
argument. No new credit is claimed for that earlier whole family.

For the remaining C5 spacing (3,1,1), zero circle load at either
private endpoint is now impossible regardless of whether that
unloaded unit was physically boundary with zero multipliers. The
only remaining private load mask is therefore exactly both P,Q
positively loaded. The two original middle-B parallel/nonparallel
branches and all their actual means were covered together.

## 8. Literal six-body network callers and retained limits

For an original six-body block plus the three genuine leaves, all
nine units are in that actual component. The accepted private
network theorem leaves partitions 3 and 2+1; 1+1+1 is already
excluded. No extra outside positive edge is silently removed.

In partition 3, let the single actual private component K attach
to roots A,C. The other root B has no private neighbors. Its two
direct root edges BA,BC are forced by the complete pair cover, so
its true positive degree is exactly three including L_B. Both
nonleaf supports are small. The possible direct AC edge remains
an actual original edge when present.

Consequently, whenever A has true degree three and its unique
private neighbor P has true degree two, that actual P must be
positively loaded. This statement keeps every internal edge of K.
The same holds at C. The actual true-degree premises mean that
AC is absent and the relevant root has exactly one private
neighbor; they are not imposed by deleting a chord.

In particular the complete simple-six-cycle caller

    A-B-C-Q-U-P-A, with genuine leaves at A,B,C,

has actual A3,B3,C3 and P2,U2,Q2. Both P and Q are loaded by
Theorem B, in every original private load assignment and every
force branch. The middle U may remain loaded or unloaded. More
general connected three-vertex networks receive the same literal
endpoint conclusion whenever their real degrees meet the printed
test. A private triangle or an extra attachment can raise a
degree and is not assigned a false transmitter equation.

In partition 2+1, retain the exact accepted labels: private P,Q
attach to A,B; private N attaches to B,C; AC is a direct edge.
The singleton N is loaded. Types I--III remain with the actual
neighbor sets printed in be54ef6e; Type IV is already excluded.
The new theorem does not automatically supply a small-support
second genuine root there: its remaining neighbor can be the
loaded N or another loaded private unit. In Type II the necessary
clear Q has true degree three, so it is not an unloaded2 channel.
Types I--III are therefore not declared excluded by this result.
The corollary in Section 6 supplies an additional strict support
necessity whenever its actual adjacent true3-root hypotheses hold.

Finally, both-private-loaded C5 does not yet enter the earlier
outer-neighbor exclusion directly. A and C each have only one
private boundary neighbor, while their other cycle neighbor is
the genuine clear B; B's two cycle neighbors are the clear A,C.
No root in that exact cycle has the two immediate boundary
neighbors required by that theorem. A new full physical join is
needed to exclude this remaining load mask. This limitation
prevents a false whole C1.5.b3 or C1.6.b3 closure.

## 9. Exact inputs, verification, and preservation

| Complete input | SHA256 | Literal use |
| --- | --- | --- |
| GENUINE_LEAF_ROOT_SMALL_NONLEAF_SUPPORTS.md | a729b8ebb0d0aaf2ff0fa3a8b08749faf136b18253a0dbd0c99a91f2a069b358 | Its full support-only alignment theorem at each actual true3 root; no neighbor boundary premise |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full actual force/torque equations, original support lines and the true unloaded2 channel; its geometry is reproduced |
| THREE_GENUINE_LEAF_ROOTS_HIGH_S_REDUCTION.md | 41c6686127871c7c99ab69c84292f04c995a8530eb02cde0235cdacc181ae73f | Whole earlier low/critical/D exclusion and actual high S near points, only for the graph callers |
| THREE_GENUINE_ROOTS_BLOCK_TWO_TERMINAL_NETWORK_COVER_AND_DENSE_FIVE_EXCLUSION_2026_10_29.md | 3aed6244d69913b6eecb61ff9b8985688e723da3ec4a57ffaadc8e5d92dd7b66 | Complete graph-only rooted five-body cover and the true-degree private path load fact |
| THREE_GENUINE_ROOTS_ARBITRARY_PRIVATE_NETWORK_LOAD_AND_UNIQUE_PAIR_CLASS_2026_10_29.md | be54ef6e20015c3841606d0b7779ba17fe319d2aa886ad9adfd376e985995a20 | Exact root-pair network classes and current six-body partitions and Types I--III |
| OUTER_BLOCK_GENUINE_ROOT_BOUNDARY_NEIGHBORS_CENTRAL_DISK_OR_BALANCED_ALIGNMENT_2026_10_29.md | 177ae1085ff09f3322bc68612104f238c0bad62158f05b70814fa86e2b732560 | Existing C5 (2,2,1) whole exit and the precise immediate-boundary-neighbor premise that does not yet close (3,1,1) |

The support-only source was read completely, and the whole generic
three-force support cover was reconstructed above without importing
a near-neighbor hypothesis at the channel's far square. The same
cover also appears in the previously accepted 5dba416e genuine-root
two-near source; its fixed-singleton selection result is not an
input here. No new normal-selection requirement is introduced.

All six source pins match. The seven printed strict rational
reserves were checked with exact Fraction arithmetic, including
3005/13924, 1333/2124, 56/53041, 2/49, 13/4130, 1/100 and
127/600. These checks corroborate the continuous proof; there is
no sampled pose, angle mesh or numerical packing certificate.

Every original unit, full star, physical circle corner, individual
zero coefficient, positive pair force, selected normal and actual
mean remains. The two-star comparison is a direct use of their
original equations and normal signs, not an aggregate root or a
contraction of P. No Lean/Lake compilation, CI/workflow, remote
mutation, ledger/count edit or merge was performed. A complete
independent review and root adoption are required before using
this new theorem as an accepted input.
