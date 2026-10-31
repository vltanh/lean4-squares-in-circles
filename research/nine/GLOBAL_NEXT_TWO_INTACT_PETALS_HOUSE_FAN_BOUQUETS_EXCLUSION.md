# Two intact petals exclude the complete roof-house, lower-house and endpoint-fan bouquets

Date: October 27, 2026.

**Status: complete proposed uniform geometric theorem and three whole
original bouquet exclusions, frozen for full root and separate independent
review.** No shared ledger or original cell status is changed by this file.

Keep all nine actual unit squares, their common canonical packing and
compatible selected physical certificate in

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

All physical circle masks, zero individual circle weights, true positive
degrees, original force magnitudes, unchanged normals, shared-side means
and positive chords remain. Every disk in this source is closed.

The new local theorem strengthens the axis-only obstruction in
C6_NEXT_ENDPOINT_FAN_MOMENT_ORDER_AND_ROOT_OWNER_REDUCTION.md, mathematical
SHA256 4df1bece71a9dac1f76aa25d98a4716d4bfe7a3ce1b476357b0e85e84bc985ff.
The extra input is a strict distance greater than sqrt(2) epsilon for the
unloaded unit. Two intact petals supply that input uniformly. The full
proof below covers every actual root-contact owner, including both
strict-vertex families left by that earlier obstruction.

## 1. Uniform theorem with the complete original unloaded equation

Let E and U be distinct actual units. Suppose:

* D_epsilon is contained in int E;
* dist(O,U)>sqrt(2) epsilon;
* U has zero total circle force, and all its positive forces are its
  original pair forces to its actual neighbors;
* its original force toward E has nonzero origin moment, and every
  other original U force has a nonzero origin moment of the opposite
  sign.

Then the configuration is impossible.

There is no degree restriction at U or at any neighbor. No boundary
status or force equation at another neighbor is assumed. In particular
E keeps its complete original star and arbitrary circle system. The
local proof uses the whole unchanged force equation at U and the actual
support features; it does not assume a three-force concurrence.

Reflect the whole coordinates if necessary so that the actual U-to-E
moment is positive and every other U moment is strictly negative. Such
a reflection changes every determinant sign together and changes no
physical unit, force, support or equation.

For a unit vector n, write h_U(n)=max_(x in U) n.x. Every contained
unit V on the outward side n.x>=h of an actual support satisfies

    h<=d.                                                    (1)

For completeness, if c is its actual center and u,v are its own axes,
its farthest corner gives

    R^2 >= |c|^2+1/2+|c.u|+|c.v|
        >= |c|^2+|c|+1/2.

Thus |c|<=d+1/2. Its half-width along n is at least1/2, so
c.n>=h+1/2 implies (1). This is the universal contained-unit bound,
also proved in END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md Section1,
SHA256 20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf.
It uses no load or degree of V.

## 2. An exhaustive positively oriented own frame

There is a positively oriented actual own frame of U in which

    U=[a,a+1] x [b,c],
    c=b+1, a>epsilon, c>=-epsilon.                           (2)

Indeed the squared distance from O to an own rectangle is the sum
of the squares of the distances from zero to its two own intervals.
The strict distance hypothesis means at least one interval misses zero
by more than epsilon. Use that interval for the positive x direction,
keeping a positively oriented frame; this gives a>epsilon. If the
resulting other upper endpoint c is at least -epsilon, (2) holds.
Otherwise make the positively oriented quarter turn x'=-y,y'=x.
The new first interval starts at -c>epsilon, and its second interval
is the former [a,a+1], with positive upper endpoint. This proves (2)
without a reflection that would change the already chosen moment signs.

In particular

    a>0, a+1>1+epsilon>=d.                                   (3)

Let n be the unchanged U-to-E unit normal and p its actual application.
The actual contact is a common support, and D_epsilon is strictly
inside E on the outward side. Hence

    h_U(n)=p.n=min_(x in E) n.x < -epsilon,
    det(p,n)>0.                                              (4)

These inequalities retain actual side means and support-cone endpoints.

We first prove n_x<0. If n_x=0 and n_y=1, its support is c>=-epsilon,
contrary to (4). If n_x=0 and n_y=-1, its moment is -p_x<0, also
contrary to (4). If n_x>0 and n_y>=0, its support is
(a+1)n_x+c n_y>=-epsilon. If n_x>0 and n_y=-v<0, its application is
the lower-right vertex (a+1,b), and its positive moment requires

    -(a+1)v-b n_x>0.

This forces b<0, but its support (a+1)n_x-bv is then positive,
contrary to (4). Thus every possible root contact has n_x<0.

## 3. Full exit for a nonpositive vertical root direction

Suppose n_y<=0. If n_y<0, write n=(-u,-v), u,v>0. Its actual
application is (a,b), and its positive moment is b u-a v>0.
Consequently b>0, and in particular c>0. If n_y=0, its original
left-side application has positive height, since
det((a,y),-e_x)=y>0. Again c>0. The latter argument does not assert
b>0 or replace the actual side mean by an endpoint.

When c>0, every actual negative-moment force on U has nonpositive
vertical component. Here is the full feature check:

* The right-side axis +e_x is impossible, because its required
  neighboring support a+1 exceeds d by (3).
* At the upper-right corner (a+1,c), write an outward unit normal
  as g=(s,t), s,t>=0. Negative moment requires (a+1)t<c s.
  For t>0 this implies s>0 and

      h_U(g)=(a+1)s+c t
             >(a+1)(s+t^2/s)=(a+1)/s>=a+1>d.

  For t=0, its support a+1>d is already impossible. Thus the full
  upper-right cone has no actual negative-moment contact.
* A top-side normal has moment p_x>0. An upper-left normal
  (-s,t), s,t>=0, has moment a t+c s>=0. Neither is negative.
* The left-side normal has vertical component zero. The bottom
  side and both lower corner cones have nonpositive vertical
  component, including all their endpoints.

If n_y<0, the complete force sum has strictly negative vertical
component. If n_y=0, every other force must have zero vertical
component to make that sum vanish. Each such actual normal is
horizontal. The +e_x alternative is impossible by (3), so all
positive forces, including the root force, point -e_x. Their sum
cannot vanish. Both cases contradict U's full unloaded equation.

## 4. Full exit for a positive vertical root direction

It remains that

    n=(-u,v), u,v>0, u^2+v^2=1,
    p=(a,c), h_U(n)=-a u+c v< -epsilon,
    a v+c u>0.                                              (5)

Put w=(v,u). Then w.n=0. We prove that every other original
negative-moment unit normal g has

    w.g<0.                                                  (6)

The feature cover is exhaustive:

**Right side, upper-right cone, and top side.** The right side is
impossible by (3), and the top side has positive moment. If c<=0,
an upper-right normal (s,t) has moment (a+1)t-c s>=0. If c>0,
the strict support calculation of Section3 excludes every negative
moment in that entire corner cone. Thus none of these features
contributes a negative-moment force.

**Upper-left cone.** Write g=(-s,t), s,t>=0. A negative moment
a t+c s<0 forces c<0 and s>0, and gives

    t/s < -c/a < v/u.

The second strict inequality is precisely the positive root moment
in (5). Hence w.g=-v s+u t<0. This retains t=0 and the c=-epsilon
frame endpoint whenever feasible.

**Left side, lower-left cone, and bottom side.** Their normals are
respectively -e_x, (-s,-t) with s,t>=0 and not both zero, and -e_y.
Since u,v>0, each has strictly negative w-projection. This includes
every left or bottom shared-side mean, every lower-left cone endpoint
and every original sign of b.

**Lower-right cone.** Write g=(s,-t), s,t>=0. The cases s=0 or
t=0 are already covered by the bottom or right side. Suppose s,t>0.
We claim t/s>v/u. Otherwise g is a unit normal in the closed cone
between e_x and -n=(u,-v). All these normals expose the same actual
lower-right vertex (a+1,b), including their side-axis endpoints.
Their two endpoint support values satisfy

    h_U(e_x)=a+1>d,
    h_U(-n)=u+v-h_U(n)>1+epsilon>=d.                         (7)

The identity in (7) is the exact unit-square width u+v. Express
g=lambda e_x+mu(-n), lambda,mu>=0. Since g is unit,
lambda+mu>=1 by the triangle inequality. Support is linear on
this one vertex cone, and d>0 throughout the radius window, so

    h_U(g)=lambda h_U(e_x)+mu h_U(-n)
             >d(lambda+mu)>=d.

This contradicts actual containment of its neighbor in (1).
Consequently t/s>v/u, and w.g=v s-u t<0, proving (6) also here.

The original root force has zero w-projection and every other
positive force has strictly negative w-projection. Their full
sum cannot vanish. This contradiction proves the entire uniform
theorem of Section1. No actual support point was moved, and no
normal, mean, force or circle atom was altered.

## 5. Exact two-petal and private-cycle inputs

Let E carry two distinct actual intact triangle petals. The complete
stronger disk theorem

    TWO_INTACT_PETALS_NO_UNLOADED_NEIGHBOR.md
    SHA256 be227b05fbf23fd0e4e973f9f3c4ba4fe129116fc220a4c8fe2218a4c39fec77

gives D_(1/40) subset int E with every E force retained. Every
distinct closed actual unit U therefore satisfies

    dist(O,U)>1/40>sqrt(2) epsilon.                          (8)

The exact strict comparison is

    (1/40)^2-2(1/60)^2=1/14400>0.

Thus the uniform theorem applies whenever the required complete
unloaded moment pattern occurs at an actual neighbor of this E.

We also use the complete actual geometric theorem

    GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md
    SHA256 8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49.

Its Sections2--4 show that every positive edge between two actual
units outside E is nonradial, and every directed cycle of strictly
positive original moments among such units winds about O. This
uses arbitrary true degrees; no proper concurrence at a loaded
higher-degree unit is asserted. A cycle avoiding E is impossible
by its Section5 actual exterior-path argument: the origin-to-E-center
path stays inside E, and the real positive E-to-intact-tip edge leads
to a physical circle body outside the cycle. The compatible selected
physical embedding preserves this genuine exterior access. Reversing
a cycle handles strictly negative directed moments as well.

Accordingly every private edge used below has strictly nonzero
original moment, and no actual private simple cycle can have all
its directed moments of the same strict sign. This applies to a
cycle avoiding E even when its whole block contains E. No entire
block is falsely declared outside the origin root.

For the exact original load and physical-clearance joins we use

    GLOBAL_CLOSURE_TWO_INTACT_PETALS_FIVE_BLOCK_ROOT_NEIGHBOR_REDUCTION.md
    SHA256 653e4ea3bfd6d7ee5d1552c6bda26ab0519d3a6929083fb7f16b5496b60962a3.

In particular E already has four distinct physical boundary tips;
the complete physical no-six-boundary-neighbor theorem permits at
most one additional physical boundary neighbor at E. Every statement
here is at the true original degree and includes physical boundary
contact with zero total multiplier. The sources' full common-radius
and same-nine prerequisites remain unchanged.

## 6. Whole roof-house bouquet, with every original load mask

Use house edges

    AE, DE, AD, AB, BC, CD,

where E is its roof and also the root of both intact petals. The
four private house bodies A,D,B,C are distinct from all four intact
tips. Thus the original graph has exactly nine actual bodies,
E has its true degree six, A/D true degree three and B/C true
degree two. Their possible circle loads are not narrowed in this
argument.

At least one of A,D is physically circle-clear. Otherwise the four
intact tips plus A,D would be six distinct physical boundary neighbors
of E. Fix either actual clear hub; its entire circle load is zero.

Write m(X,Y) for the moment of the original vector from X toward Y.
The full true B2 and C2 moment equations, whose circle moments are
zero, give

    l=m(A,B)=m(B,C)=m(C,D).

Put h=m(A,D). Both h and l are nonzero by Section5. The actual
private four-cycle A-D-C-B-A has directed moments

    h, -l, -l, -l.

If h and l had opposite signs, all four displayed moments would
have the same strict sign, forbidden by Section5. Hence h and l
have the same strict sign.

The complete A3 moment equation now gives

    m(A,E)=-h-l.

At A the force to E therefore has the strict opposite moment sign
to both other actual forces. Likewise the complete D3 equation
gives m(D,E)=h+l, opposite to its other moments -h,-l. Whichever
hub is clear consequently satisfies all hypotheses of Section1,
using (8). The resulting contradiction excludes the entire original
roof-house bouquet. This includes both-clear and one-clear hub
domains, every lower-body load mask, every physical radial mask,
all individual zero weights and all original means.

No root force balance was reduced, and neither a loaded hub nor the
degree-six roof was given a degree-two equation.

## 7. Whole lower-house bouquet

Use the original house labels roof Z, hubs A,D and lower vertices
B,C, with edges AZ,ZD,AD,AB,BC,CD. Put B=E, the common root of
both intact petals. All nine bodies are again the original distinct
units; E has degree six and A retains true degree three.

The true degree-two E neighbor C is positively loaded. Indeed the
complete two-petal no-unloaded-neighbor theorem applies to its
unchanged C2 equation. If A were physically boundary, the four
intact tips together with A,C would be six distinct boundary
neighbors of E. Thus A is physically clear and genuinely unloaded.
No particular load or physical mask at D is needed below.

The full Z2 moment equation gives

    k=m(A,Z)=m(Z,D).

Put h=m(A,D). Both k,h are nonzero because these are private edges.
The actual private triangle A-Z-D-A has directed moments k,k,-h.
Its forbidden same-sign alternative forces k and h to have the
same strict sign. The full true A3 equation then gives

    m(A,E)=-k-h.

Thus A's force to E has a nonzero moment opposite to both other
original moments. The uniform theorem and (8) contradict its full
unloaded equation. This excludes every original lower-root house
domain. The root reflection interchanging A,D and B,C gives the
other lower vertex without altering any original force or degree.

The earlier lower-root reduction further forced D to be loaded;
that extra conclusion is not needed for this whole exit.

## 8. Whole endpoint-fan bouquet

Write the actual fan as the boundary path E-B-C-D together with
the four original spokes KE,KB,KC,KD. E is the common root of
the intact petals. The complete original load reduction in Section5
gives B,C,D positively loaded at their true degrees 3,3,2, and K
physically clear at its true degree four. In particular K cannot
be physically boundary because the actual K-C-D triangle would
then have three physical boundary units. No K spoke is deleted.

Define the actual moments

    k1=m(E,B), k2=m(B,C), k3=m(C,D), k0=k4=0,
    h1=m(K,E), h2=m(K,B), h3=m(K,C), h4=m(K,D).

The complete B,C,D torque equations give h_i=k_i-k_(i-1) for
i=2,3,4. At E each of the two original intact petals contributes
zero aggregate moment by its two full private-tip equations, so
the full E moment equation gives h1=k1 as well. Hence

    h_i=k_i-k_(i-1), i=1,2,3,4.                              (9)

No boundary-angle assertion is needed for the following strict
sign derivation. The private CD moment is nonzero; orient the
plane so that k3>0. Equation(9) gives h4=-k3<0. The actual private
triangle K-C-D-K has moments h3,k3,-h4. Its last two are positive,
so h3 cannot be positive; it cannot be zero by Section5. Therefore
h3<0 and k2>k3>0. The next private triangle K-B-C-K has moments
h2,k2,-h3; again the last two are positive, and h2 is nonzero.
Consequently

    k1>k2>k3>0,
    h1>0, h2<0, h3<0, h4<0.                                (10)

These are exactly the whole-domain signs also derived in the earlier
C6 source, now obtained using only the private cycle and full torque
equations. The clear true-degree-four K has one positive-moment
force toward E and all its other original forces of negative moment.
Equations(8),(10) give every hypothesis of the uniform theorem.
Its contradiction excludes the whole endpoint-fan bouquet, including
both strict K-vertex owner families left by the axis-only result.

The other path endpoint is its original graph reflection. Neither
endpoint E nor the clear K was assigned a shortened star, and no
circle resultant was split into fictitious physical loads.

## 9. Exact result and limits

Sections6--8 exclude the complete three common-root bouquet domains
left by the ten-domain cover
MIXED_C3_335_COMPLETE_ATTACHMENT_REMAINDER.md, SHA256
7ee5b3b12165e9b30ad279a43fdce76720bc850c429b882d7c4a8b0a0ac2ea36.
Every full mask, original load value, normal owner and shared mean
inside those graph domains is included. No new fine labels are made.

The seven middle-triangle-chain domains have their separate complete
exit in the degree-free intact-block theorem 8def789e. The exact
whole-cell assembly is recorded separately for review; this source
does not edit any accepted gate or shared ledger.

The unrestricted nine-square lower bound and its original equality
classification are not claimed here. No numerical pose, angle sample,
finite force reweighting, physical motion, Lean compilation, CI,
workflow or remote mutation is part of this proof.
