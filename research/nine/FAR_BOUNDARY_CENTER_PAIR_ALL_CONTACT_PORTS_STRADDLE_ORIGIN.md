# A far center pair puts every pair of actual ports on opposite sides of the origin projection

Date: October 28, 2026 UTC. Author: two_circle_v_review continuation.

**Status: complete proposed force-free hand theorem, frozen for full
root and separate independent review.** This replaces the opposite-port
distance and outward-center-projection hypotheses of the older strip
argument by a direct statement about every point of both physical units.
Its literal H4 consequence is a necessary restriction; no entire
original graph/load family is declared excluded.

All units, actual contact sets, original applications and shared means,
true degrees, forces and moments, physical circle masks and individual
zero coefficients remain unchanged. No normal is selected or altered.

## 1. Whole-unit theorem, without a circle or stress premise

Let C,E be actual closed unit squares with centers c_C,c_E. Take the
unchanged origin O as zero and assume

    |c_C|>=5/4, |c_E|>=5/4,
    gamma=angle(c_C,c_E)>=acos(-3/4),

where gamma is the minor angle in [0,pi]. No degree, load, boundary,
contact-owner, support-direction, or orientation hypothesis is imposed.

**Theorem A.** For every actual P in C and Q in E,

    P.(P-Q)>0, Q.(Q-P)>0.                              (1)

Consequently P and Q are distinct, and with e=(P-Q)/|P-Q|,

    e.Q<0<e.P.                                         (2)

Thus the perpendicular projection of O onto the actual line PQ is
strictly inside the segment PQ. The assertion holds simultaneously for
all physical points, not only selected applications or square centers.

**Theorem B.** Under the stronger center-angle condition

    gamma>=acos(-4/5),

the whole-unit inequalities have the uniform margins

    P.(P-Q)>|P|/10, Q.(Q-P)>|Q|/10.                    (3)

In particular neither theorem requires |P-Q|=sqrt(2), |P-Q|>1,
external side ownership, a normal-angle bound, or an outward projection
of either center relative to the selected port.

## 2. Every actual point stays in a uniform center cone

Put sigma=1/sqrt(2). The entire actual unit is in its closed center
disk of radius sigma, and sigma<3/4. For P in C,

    |P|>=|c_C|-sigma>5/4-3/4=1/2.                    (4)

Also

    P.c_C>=|c_C|^2-sigma|c_C|>0.

Hence P is nonzero and delta=angle(P,c_C) belongs to [0,pi/2).
The distance from c_C to the line OP is at most |c_C-P|<=sigma.
Therefore

    sin(delta)<=sigma/|c_C|<3/5,
    cos(delta)>4/5.                                    (5)

This is a whole-square directional bound, valid at vertices, side
points, arbitrary interior points and every actual aggregate mean.

Let phi=angle(P,c_E). The triangle inequality for minor angles gives

    phi>=gamma-delta>0.

Both phi and gamma-delta lie in [0,pi], where cosine is decreasing.
Thus

    cos(phi)<=cos(gamma-delta)
             =cos(gamma)cos(delta)+sin(gamma)sin(delta). (6)

No sign or branch of an inverse trigonometric function is omitted.
The case gamma=pi and the case delta=0 are included.

## 3. Complete qualitative strip proof

When gamma>=acos(-3/4),

    cos(gamma)<=-3/4,
    0<=sin(gamma)<=sqrt(7)/4<2/3.

The last strict comparison is 7<64/9. Equations (5)--(6) imply

    cos(phi)<-(3/4)*(4/5)+(2/3)*(3/5)=-1/5.           (7)

Write u=P/|P|. Every Q in E has Q=c_E+(Q-c_E) with
|Q-c_E|<=sigma. Consequently

    u.Q<=|c_E|cos(phi)+sigma
       <-|c_E|/5+sigma
       <=-1/4+sigma<1/2.                              (8)

On the other hand |P|>1/2 by (4). Therefore

    P.(P-Q)=|P|[|P|-u.Q]>0.

Interchanging the two actual squares gives Q.(Q-P)>0. This proves
Theorem A and all its strict endpoints. In particular (1) itself
excludes P=Q; division by |P-Q| in (2) is legitimate.

## 4. Complete quantitative strip proof

When gamma>=acos(-4/5), the sharper elementary values are

    cos(gamma)<=-4/5, 0<=sin(gamma)<=3/5.

Equations (5)--(6) now give

    cos(phi)<-(4/5)^2+(3/5)^2=-7/25.

Hence, for every unchanged Q in E,

    u.Q<-(7/25)|c_E|+sigma
       <=-7/20+sigma<2/5.

Together with |P|>1/2, this proves

    |P|-u.Q>1/10,
    P.(P-Q)>|P|/10.

The reflected calculation proves the second inequality of (3).
All center and angle endpoints in Theorem B are retained. The strict
margin comes from the unit circumradius sigma<3/4 and the full point
cone (5), without a compactness or numerical-angle argument.

## 5. Every physical boundary unit in the original radius window qualifies

Suppose the actual unit C is contained in the original circle of radius
R and has at least one physical circle corner Z. Its actual center is
at distance sigma from that corner, so

    |c_C|>=R-sigma.

For the entire original window R>=79/40,

    sigma<29/40,
    |c_C|>=R-sigma>79/40-29/40=5/4.                  (9)

The squared reserve for sigma<29/40 is 41/1600. This argument uses
one actual physical corner; it does not require that corner to carry
positive selected weight, a unique far corner, or any pair degree.
The same conclusion holds for E, with all physical masks retained.

Thus Theorems A and B apply to every physical boundary pair in this
window having the respective center-angle bound. No upper radius is
needed for the local strip result once its center premises hold.

If the chosen P,Q also lie on the same actual unit U, then
|P-Q|<=sqrt(2). Under Theorem B write

    Q=(-L,h), P=(T,h)

in the actual chord frame with the unchanged origin zero. Equations
(2)--(3) give

    L,T>0, L+T=|P-Q|,
    L>|Q|/(10|P-Q|), T>|P|/(10|P-Q|).                 (10)

Every boundary-unit point has norm at least R-sqrt(2), by its physical
circle corner and unit diameter. Consequently, whenever R>=2,

    L,T>(R-sqrt(2))/(10sqrt(2))
       >=(sqrt(2)-1)/10>1/25.                         (11)

The last comparison uses sqrt(2)>7/5. This quantitative statement does
not assume that either application is a vertex or that the contact
intersection is a singleton.

## 6. Literal complete far-pair consequence for both H4 load families

Retain the original actual component

    HA, HB, HC, HD, AB, BC, CD, DE, EA,
    (A,B,C,D,E)=(0,1,2,3,4).

H remains the unloaded true H4. D remains the unloaded true D3 with
its complete H,C,E neighborhood. C remains true C3 and E remains
true E2. The original H--E closed-disjoint condition, every other
physical contact, all nine units and all three completing units remain.

For H4_D0.L0124, the four actual loaded boundary units form the path
E--A--B--C. The complete original component sum is

    F_E+F_A+F_B+F_C=0.

FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md proves that the minor
angle of the actual C,E centers is greater than 5*pi/6. Since
cos(5*pi/6)=-sqrt(3)/2<-4/5, Theorem B applies. Therefore every
actual pair

    P_C in D intersect C, P_E in D intersect E

has the strict strip (10), simultaneously over the entire physical
contact sets. In particular the two original positive applications
have it, including arbitrary endpoints of positive shared segments.

For H4_D0.L124, the full actual component sum is
F_B+F_C+F_E=0 and BC is an actual physical contact. Section 1 of
BALANCED_BOUNDARY_FAR_PAIR_AND_OPPOSITE_PORT_ORIGIN_STRIP.md supplies
a selected far pair CE or BE with minor center angle greater than

    alpha=pi-(1/2)*acos(9/25),
    cos(alpha)=-sqrt(17)/5<-4/5.

If necessary reflect the entire original graph by i -> 3-i modulo 5
so that the selected far pair is named CE and its intervening unloaded
end is D. This reflection preserves the complete load set and all true
degrees. Theorem B then gives (10) for every actual CD/DE pair at
this same selected far end. It does not assert a far-pair bound at
the other end when only the first alternative has been established.

The same-nine radius lower bound R>2 supplies (11) in both original
callers. No lower bound on the distance between the two ports enters
this join; its far-pair choice is the actual angular alternative just
stated, throughout the full contact-set conclusion.

This conclusion covers every D-owned, externally owned, free or shared
return feature, every HD owner, arbitrary original means, coincident
applications involving the third contact, and every physical zero-weight
refinement. The proof uses no equation at C and no proper concurrence
at E. Therefore it also applies when the other unloaded end A in L124
is physically circle-clear; it does not promote A to a boundary unit.

The strip conclusion alone does not determine the signed height h,
an endpoint normal's slope, a physical circle mask, the location of O
relative to D, or a completion capacity. Those remain separate genuine
obligations. In particular neither entire H4 load family is closed here.

## 7. Exact dependency and adoption boundary

Sections 1--5 are self-contained unit geometry, except that Section 5
names the caller's radius range. Section 6 uses exactly the following
current sources for its original graph, force balance and far-pair
premises; it does not use the older port-strip theorem in Section 2
of the second source.

| Source | SHA256 | Exact use |
| --- | --- | --- |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 164d08bb2c4dfe8510247e44298d309920cb88a780221252d833f51aa654225f | Whole four-load physical path and its strict minor endpoint center-angle bound |
| BALANCED_BOUNDARY_FAR_PAIR_AND_OPPOSITE_PORT_ORIGIN_STRIP.md | 72a915beaee37b435d993c6e77bd9833d717479b7b07ac014783d764cffa8605 | Only Section 1's complete balanced-three far-pair theorem; no old strip or normal-projection hypothesis |
| INNER_PENTAGON_FOUR_SPOKE_NO_CHORD_OCCUPIED_POCKETS_AND_LONG_PORT_REDUCTION.md | ad0a8e658d303d7527a383c4688fa4bfdae1a04f46cecfb59c424cc4028e02a6 | Complete two original load domains, all actual degrees, same selected-end reflection, and unchanged whole physical contact sets |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Only the same-nine R>2 used for the optional uniform numerical strip margins (11) |

This is a new complete uniform export requiring its own full current
source reviews. The historical opposite-vertex strip source and its
reviews remain unchanged. No sampled orientation, pose cover,
computational certificate, altered mean or normal, force deletion,
Lean/Lake run, CI, ledger mutation, commit or remote write was used.
