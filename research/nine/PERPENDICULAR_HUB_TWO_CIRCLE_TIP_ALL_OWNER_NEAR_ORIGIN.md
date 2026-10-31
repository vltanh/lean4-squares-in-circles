# Perpendicular hub contacts and any two-circle loaded tip force a uniform near-origin hub

Date: October 28, 2026 UTC. Author: pentagon continuation.

**Status: complete proposed local hand theorem, frozen for full independent
review.** This is an all-frame, all-original-owner conclusion. It uses the
complete equation only at the actual loaded degree-two tip. The hub and
the other boundary unit have arbitrary degrees and retain all their
original forces. In particular, no third hub neighbor, endpoint
concurrence, boundary-path load pattern, or extra-square placement is a
premise of the local theorem.

The new part is a positive horizontal support bound throughout the
entire nonparallel return domain. It gives a common quantitative
conclusion for that domain and the parallel physical-two-circle tip:
the actual hub is within 1/60 of the circle origin, and each of its
actual vertices has norm greater than 1/15.

## 1. Complete unchanged local statement

Put Q=1105/256 and assume

    2<R<=sqrt(Q).

Let U,V,W be distinct actual closed unit squares in the same unchanged
disk D_R, with pairwise disjoint open interiors and actual positive
contacts UV,UW,VW. The original U-to-V and U-to-W separating unit
normals are perpendicular own side axes of U.

The complete positive pair neighborhood of V is exactly U,W. Its total
circle load is positive, and V has exactly two physical circle corners.
Keep both physical corners, every original individual zero coefficient,
and the full original V force and torque equations. The actual W
physically touches the containing circle. Its degree, circle load,
other contacts and full equations are arbitrary. The degree, circle
load and other contacts of U are arbitrary as well.

Keep every original normal, magnitude, singleton application and whole
shared-side mean, including all endpoint means. In particular, no
normal selection convention is needed for the theorem: if a normal is
an axis of either actual square, that owner is retained, and if it is
an axis of neither square, its actual vertex supports are treated
directly. No unique-circle selector is used in this physical-two case.

**Local theorem.** In a global rigid frame about the unchanged circle
origin O, with U-to-V North and U-to-W East, write

    U=[L-1,L] x [H-1,H].

The full domain forces

    0<L<=1/2,
    61/100<H<61/60,                                  (1)
    dist(O,U)<1/60,
    |Z|>1/15 for every actual vertex Z of U.          (2)

In particular U is physically circle-clear; indeed U is wholly inside
the open disk of radius 3/2. These are statements about the unchanged
actual unit, not a small-center surrogate or a translated square.

**Conditional three-unit consequence.** It is impossible, in addition,
to have two distinct other actual units E,N whose distances to O are
at most 1/40 and all of whose vertices have norm greater than 19/300.
This consequence imposes no graph, force, degree, or circle-contact
condition on E,N. A caller must supply their actual proximity and
vertex bounds independently.

## 2. Actual perpendicular geometry and full tip resultant

Use the global frame in the statement. The original UV application or
mean lies on y=H, and the original UW application or mean lies on x=L.
Only the force-free direction lemma of Section 2 of
BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md is used: it gives the entire
Southeast quadrant for the actual V-to-W normal,

    m=(u,-v), u,v>=0, u^2+v^2=1.                    (3)

For clarity, its geometric argument keeps arbitrary original means.
If an actual unit lies beyond a vertical U side and another lies
beyond the perpendicular horizontal U side, every common point of
those two neighbors is in their common outer quadrant. Comparing
their original U applications with their common supporting line,
and taking the inward axis steps available at those support points,
forces the normal components to point toward that quadrant's other
neighbor. With the present order V-to-W the signs are exactly (3).
The argument has no equation or degree premise at either neighbor.

Write mu,nu>0 for the original UV,VW pair magnitudes. The complete
outward circle resultant of V is

    F_V=mu*North-nu*m,
    (F_V)_x<=0, (F_V)_y>0.                          (4)

All physical corners and the whole original weight interval remain
in this resultant. We do not replace V by a radial leaf or assume
equal corner coefficients.

Set

    d=sqrt(R^2-1/4)-1.

Throughout the exact radius window,

    187/200<d<61/60.                                 (5)

The first strict comparison follows from
15/4-(387/200)^2=231/40000>0. The squared containing radius at
d=61/60 exceeds Q by 31/57600. Both are strict at the closed upper
radius endpoint.

A containing-circle point cannot be shared by two interior-disjoint
contained units. At a circle corner each actual inward axis has
strictly negative scalar product with the radius, as follows by
comparing the adjacent vertex's squared norm with R^2. Each open
right-angle tangent sector is therefore strictly inside the same
inward radial half-plane. Two such sectors cannot have disjoint
interiors there. This geometric fact includes zero circle weights.

## 3. Entire parallel-V physical mask

First suppose the actual V frame is parallel to U. A boundary unit
with two physical circle corners at R>2 has exactly one zero own
center coordinate. The signs in (4) leave only the radial North and
radial West physical masks. Radial South would make every circle
point's y coordinate negative; radial East would make every circle
point's x coordinate positive. The centered four-corner tie has
radius sqrt(1/2), outside the domain.

### 3.1. Radial West is impossible by actual U containment

In this mask

    V=[-d-1,-d] x [-1/2,1/2], H=-1/2.

The actual W is in x>=L and meets V, so L<=-d. The actual lower-left
U vertex (L-1,-3/2) has squared norm at least

    (d+1)^2+9/4=R^2+2,

contradicting U containment. This uses no force equation at U or W.

### 3.2. Radial North and the complete original return cover

The remaining actual mask is

    V=[-1/2,1/2] x [d,d+1], H=d.                    (6)

The original normal (3) may be South, East, or strictly Southeast.
If it is South, W has maximum height d and vertical width at least
one. But the force-free radial half-strip theorem, applied to the
actual radial V and its actual boundary neighbor W, gives
min_W y>d-1. This contradicts that width. Its hypothesis holds
because d>1/sqrt(2), and the actual contact point lies on V's
inner side, including either endpoint or any original shared mean.

If m is East, the common support x=1/2 is W's minimum-x line.
The actual UW support is the same minimum-x line, hence L=1/2.

Suppose m is strictly Southeast. Its actual V support is the unique
lower-right vertex

    M=(1/2,d).

If W is parallel to U, its minimum-m vertex is its upper-left
vertex, whose first coordinate is L. Again L=1/2.

If W is nonparallel to U, its unique minimum-x vertex has the form
Q_W=(L,q), with d-1<=q<=d. Write its actual inward axes as

    f=(C,S), g=(S,-C), C,S>0, C^2+S^2=1.

Since m.g>0, every actual minimum-m point has g coordinate zero.
Therefore, without initially assuming W ownership,

    M=Q_W+beta*f, 0<=beta<=1,
    L=1/2-beta*C, q=d-beta*S.                       (7)

At beta=0 we again have L=1/2. At beta=1 the actual minimum height
of W is d-S-C<=d-1, contradicting the same radial half-strip barrier.
For 0<beta<1, M is in the relative interior of the actual f side,
so the unchanged original normal must be m=g. The complete force-free
radial inner-corner theorem applies to this literal W chart and gives

    beta*C<1/4.

Its hypothesis d>11/12 follows from (5). It retains every W physical
mask and has no force or degree premise at W. Consequently the entire
parallel-V case gives

    1/4<L<=1/2, H=d.                                (8)

The normal-axis, aligned-W and beta=0 cases have not been excluded
by an invented third hub neighbor. They are included in (8).

Since 0 lies between U's two x sides, H>0, and H<61/60,

    dist(O,U)=max(H-1,0)<1/60.

Every U vertex has absolute x coordinate at least min(L,1-L)>1/4.
Thus (1)--(2) hold throughout this entire parallel case, with a
stronger vertex margin. Its original UV side mean stays arbitrary
on the actual contact segment and has never been substituted in an
equilibrium equation.

## 4. Nonparallel V: actual frame, distinct port, and all-owner cover

Now suppose V is nonparallel to U. Its unique bottom vertex is the
unchanged original UV application P. The exact actual frame is

    P=(L-p,H), 0<=p<=1,
    e_1=(c,s), e_2=(-s,c),
    c,s>0, c^2+s^2=1,
    V=P+[0,1]e_1+[0,1]e_2.                         (9)

The complete boundary-neighbor common-point theorem applies to the
true loaded V2 and physical-boundary W, since R^2>4>13/4. It gives

    P does not belong to W.                         (10)

This retains every original side mean and does not claim that all
other contacts in the triangle are singletons.

Equation (3) gives m.e_2=-s*u-c*v<0. If m.e_1<0, its V support
would be P, contrary to (10). If m.e_1=0, m is the V-owned normal
-e_2. Otherwise m.e_1>0 and its V support is the actual vertex

    M=P+e_1.                                        (11)

Thus every original normal is covered by the following alternatives:

1. It is an own axis of V, necessarily -e_2.
2. It is an axis of neither actual V nor actual W; then it is strict
   in both physical vertex cones and both applications are singleton
   vertices.
3. It is an own axis of W and is not an own axis of V.

A normal owned by both belongs to the first alternative. A weak
vertex-cone endpoint belongs to an own-axis alternative. A
positive-length contact necessarily belongs to the first alternative.
Hence this cover does not require any normal reselection or selector.

## 5. The complete V-owned two-circle alternative is impossible

Suppose m=-e_2. The unchanged original VW mean is

    M=P+zeta*e_1, 0<=zeta<=1.

Put A=P.e_1 and B=P.e_2. The full original V equation gives

    F_V=mu*North+nu*e_2,
    F_V.e_1=mu*s>0,
    F_V.e_2=mu*c+nu>0,
    (F_V)_x=-nu*s<0.                                (12)

Consequently A,B>=-1/2. In the physical-two mask exactly one of A,B
equals -1/2, and the other is d>0. The original two pair lines meet at

    q=P+(zeta/s)*North.

Full torque gives det(q,F_V)=0. Both own coordinates of q are at
least those of P, one of which is positive, whereas both own
components of F_V are positive. Thus q is a positive multiple of
the full resultant and P_x=q_x<0.

If B=-1/2 and A=d, however, P_x=c*d+s/2>0, a contradiction.

If A=-1/2 and B=d, the entire actual W is in the half-plane
e_2.z<=d and contains the unchanged point M=(-1/2+zeta,d) in
V coordinates. At a maximum-e_2 support point of a unit, every
horizontal displacement has absolute value at most one: at a
vertex the two inward axes have nonpositive vertical components
and opposite horizontal signs, and at a side point the actual
tangent interval has length one. Both side endpoints are included.
The vertical span is at most sqrt(2). Hence the whole actual W has

    |x|<=3/2, d-sqrt(2)<=y<=d.

Because d>1/sqrt(2), this gives |y|<=d, and consequently

    |z|^2<=9/4+d^2<R^2=(d+1)^2+1/4

for every W point. The strict reserve is 2d-1>0. This contradicts
physical boundary status of W. These arguments retain the entire
original mean interval, including zeta=0, and both V circle weights.

## 6. The complete free two-circle alternative is impossible

Suppose now m is an axis of neither V nor W. Equation (11) gives
the actual singleton M=P+e_1. From the full V equation,

    F_V.e_2=mu*c+nu*(s*u+c*v)>0.

Thus B=P.e_2>=-1/2. Equality would make one of the shared actual
points P or M a physical circle corner, according to the sign of
the first own center coordinate. This contradicts the unshareable
circle-corner fact of Section 2. Therefore B>-1/2, and the entire
physical-two mask is necessarily

    A=-1/2, B=d,
    P=(-1/2,d), M=(1/2,d) in V coordinates.          (13)

If W is nonparallel to U, its unique left vertex is Q_W=(L,H-delta),
0<=delta<=1, with inward axes f=(C,S),g=(S,-C),C,S>0. The actual
M has height H+s>H, so it is neither W's left nor lower vertex.
It cannot be its rightmost vertex: the open inward tangent cones
of V at M, generated by -e_1,e_2, and of W at a rightmost vertex,
generated by -f,-g, both contain West and would overlap. Hence
M=Q_W+f, and C=c-p<=c, S=s+delta>=s. Equality C=c would force
S=s,p=delta=0 and an actual full shared V-W side, contrary to the
point-only premise. Thus C<c and S>s.

If W is aligned with U, M_x=L-p+c<L+1 forces M_x=L. Its height
exceeds H while the original UW mean has height at most H, so M
is W's upper-left vertex. Set C=0,S=1,f=North,g=East and Q_W=M-f.
This retains the original UW mean, rather than substituting Q_W.

The entire free-return domain therefore has the actual chart

    W=M+[-1,0]f+[0,1]g,
    0<=C<c, S>s,
    gamma=c*C+s*S>0,
    eta=c*S-s*C>0,
    gamma^2+eta^2=1,
    f=gamma*e_1+eta*e_2,
    g=eta*e_1-gamma*e_2.                            (14)

Its actual center has

    c_W.f=d*eta-(1-gamma)/2>0,

because eta>1-gamma and d>1/2. The two maximum-f corners are M
and M+g. Their strict deficits are

    R^2-|M|^2=2d+1>0,
    R^2-|M+g|^2=2d*(1+gamma)-eta>0.

The second follows from 2d>1 and 1+gamma>eta. Each minimum-f
corner is still closer than its corresponding maximum-f corner.
Thus all actual W vertices are strictly inside the circle, again
contradicting physical boundary status. No selector or W equation
has entered the proof.

## 7. Full remaining W-owned chart and circle-mask equation

It remains that the original normal is owned by W and not by V.
Write its actual inward normal and tangent as

    g=(S,-C), f=(C,S),
    S>0, C>=0, C^2+S^2=1.

The endpoint S=0 is impossible because m.e_1 would be -s<0.
For C>0 let Q_W be the unique left W vertex; for C=0 let it be
the lower-left W corner. The actual square and point (11) are

    W=Q_W+[0,1]f+[0,1]g,
    M=Q_W+beta*f, 0<=beta<=1.

Since M has height H+s>H and an actual UW point has height at
most H, exact coordinates give

    Q_W=(L,H-delta),
    p=c-beta*C,
    delta=beta*S-s>=0.                              (15)

In particular beta>0. Also m.e_1=eta=c*S-s*C>0, so C<c and S>s.
Consequently

    0<p<=c<1, 0<=delta<1, 0<beta<=1.                (16)

The weak inequality p<=c includes the aligned case C=0. Its
original UW mean is (L,H-delta_0), with 0<=delta_0<=delta; for
C>0 it has delta_0=delta. The existence of that original mean
has been used only geometrically, and it is not replaced in any
equation.

Define

    gamma=c*C+s*S>0,
    eta=c*S-s*C>0,
    gamma^2+eta^2=1,
    r=C/S>=0,
    alpha=s/S=gamma-r*eta,
    kappa=c/S=eta+r*gamma,
    tau=1-beta in [0,1).                            (17)

Then exactly

    alpha>0, alpha<=beta, alpha<=gamma,
    gamma*alpha+eta*kappa=1,
    f=gamma*e_1+eta*e_2,
    g=eta*e_1-gamma*e_2.                            (18)

The full V force has F_V.e_2=mu*c+nu*gamma>0. The same physical
mask proof as in Section 6 gives the complete actual mask (13),
with both physical outer corners and the full coefficient interval.
The original two force lines meet at

    q_V=P+(gamma/S)*North,
    q_V=(-1/2+gamma*alpha,d+gamma*kappa)
        in V coordinates.                          (19)

Both q_V and F_V have strictly positive second coordinate. Their
zero determinant, from full torque, thus makes q_V a positive
multiple of the full F_V. Write only its positive total circle
coefficient as

    F_V=Lambda*(xi,d+1), Lambda>0,
    -1/2<=xi<=1/2.

The lower weight endpoint xi>=-1/2 gives the exact whole-mask
necessary inequality

    gamma*[2(d+1)*alpha+kappa]>=1.                  (20)

No inside-V concurrence assumption is used in (19)--(20).

The actual W can be written

    W=M+[-beta,1-beta]f+[0,1]g.

Its center has f coordinate d*eta-(1-gamma)/2+tau>0. Its g
coordinate is (1+eta)/2-d*gamma. If the latter were nonpositive,
the actual top corner Z_top=M+tau*f would be a farthest corner,
including the zero-coordinate tie. Its deficit is

    R^2-|Z_top|^2
      =2d+1-tau*(gamma+2d*eta)-tau^2.

Since tau<1 this is strictly greater than its value at tau=1,
namely 2d(1-eta)-gamma. The assumed sign implies
2d*gamma>=1+eta, which makes that last value nonnegative.
Thus an actual farthest corner would be strictly inside the
circle, impossible. Both own center coordinates of W are positive.
Its unique actual circle corner is therefore M+tau*f+g, and its
circle equation is exactly

    d=F(gamma,tau)
      =(tau^2+tau*gamma+eta)/
        (2*(1+gamma-tau*eta)),
    eta=sqrt(1-gamma^2).                            (21)

The denominator is strictly positive throughout 0<gamma<1 and
0<=tau<=1. This entire mask calculation uses no W equation and
no guessed positive weight at a particular W corner.

## 8. Uniform side bounds, keeping every weak frame and endpoint

The function F in (21) is increasing in tau and decreasing in
gamma on the whole displayed domain. A positive multiple of its
tau derivative has numerator

    (2tau+gamma)*(1+gamma-tau*eta)
       +eta*(tau^2+tau*gamma+eta)>0.

Multiplying a numerator of its gamma derivative by eta gives

    tau*(1-tau)*eta-(1+tau^2)-(1+tau^3)*gamma<0,

because the first term is at most 1/4 and 1+tau^2>=1. For fixed
gamma,tau, enlarging eta algebraically increases F whenever the
denominator remains positive. These are comparison inequalities;
they do not change an actual W frame.

### 8.1. The entire domain has beta<2/5

Suppose beta>=2/5, so tau<=3/5. If gamma>=3/8, the monotone
comparisons and sqrt(55)/8<149/160 give

    d<=F(3/8,3/5)<1213/1306<187/200,

with final reserve 811/130600, contradicting (5).

If gamma<3/8, then eta>9/10, alpha<=gamma and (18) gives
kappa<=1/eta<10/9. With d<61/60, the left side of (20) is
strictly below

    (3/8)*[(121/30)*(3/8)+10/9]
      =5667/5760=1-31/1920.

This contradicts (20). Consequently

    beta<2/5, s=alpha*S<2/5, c>9/10.                (22)

### 8.2. The entire domain has beta*gamma<1/4

Otherwise (22) gives gamma>5/8, and gamma<1 gives beta>=1/4,
so tau<=3/4. The monotonicities and sqrt(39)/8<25/32 give

    d<F(5/8,3/4)<116/133<9/10,

with final reserve 37/1330. This is again impossible. Hence

    beta*gamma<1/4,
    beta*C=beta*(c*gamma-s*eta)<c/4.                (23)

These proofs cover beta=1, the aligned frame C=0, and every
physical V circle-weight endpoint. No side-interior restriction
has been silently introduced.

## 9. New positive support bound on the entire nonparallel domain

The actual V mask (13), the relation p=c-beta*C, and the actual
coordinates of P give

    L=c/2-d*s-beta*C,
    H=d*c-s/2.                                      (24)

We prove L>0 over the entire domain, retaining all the inequalities
already derived from the actual full star. This is stronger than
the older coarse signed bound and is the new near-origin input.

By (17)--(18),

    L/S=[1/2-beta*gamma-K*alpha]/eta,
    K=gamma/2+d*eta-beta.                           (25)

The number K is strictly positive: gamma+eta>1, d>1/2 and
beta<2/5 give K>1/2-2/5>0.

### 9.1. The entire interval gamma<=beta

Use alpha<=gamma in (25). Since K>0,

    L/S >= eta/2-d*gamma.

Here gamma<=beta<2/5, so eta>9/10. Therefore

    L/S>9/20-61/150=13/300>0.                      (26)

The equality gamma=beta is included.

### 9.2. The interval gamma>=beta with gamma<=1/2

Use alpha<=beta in (25). It gives

    L/S >= N/eta,
    N=1/2+beta^2-beta*A,
    A=3gamma/2+d*eta.                               (27)

On 0<=gamma<=1/2 the comparison function
3gamma/2+(61/60)*sqrt(1-gamma^2) is strictly increasing: its
derivative is 3/2-(61/60)*gamma/sqrt(1-gamma^2)>0, since the
ratio is at most 1/sqrt(3)<1. Hence

    A<3/4+(61/60)*(7/8)=787/480,

where sqrt(3)/2<7/8 was used at the endpoint. The polynomial
1/2+beta^2-(787/480)*beta is decreasing on [0,2/5]. Using
(22),

    N>1/2+beta^2-(787/480)*beta
      >=1/2+4/25-(787/480)*(2/5)
      =1/240>0.                                    (28)

This covers gamma=1/2 as well as the common boundary gamma=beta.

### 9.3. The interval gamma>=beta with gamma>=1/2

First the actual scalar equation sharpens (22) to beta<1/3 on
the whole interval gamma>=1/2. Indeed, beta>=1/3 would give
tau<=2/3, and therefore

    d<=F(1/2,2/3)
      <[(2/3)^2+(2/3)(1/2)+7/8]/
          [2*(1+1/2-(2/3)(7/8))]
      =119/132<187/200.                             (29)

The last strict reserve is 221/6600, contradicting (5).

Cauchy's inequality and d<61/60 give

    A<sqrt((3/2)^2+(61/60)^2)
      =sqrt(11821)/60<11/6,

the final squared reserve being 12100-11821=279>0. Since
0<beta<1/3, the decreasing polynomial
1/2+beta^2-(11/6)*beta is strictly above its value zero at 1/3.
Thus (27) yields

    N>1/2+beta^2-(11/6)*beta>0.                     (30)

Equations (26),(28),(30) exhaust the complete gamma,beta domain.
They prove the strict actual support bound L>0. From (24), s>0
and beta*C>=0 also give L<c/2<1/2.

## 10. Actual distance and all four actual vertices

Equation (22), d>187/200 and (24) give

    H>(187/200)*(9/10)-1/5
      =1283/2000>61/100,
    H<d<61/60.                                      (31)

Since 0<L<1/2 and H>0, the actual x interval of U contains 0
in its interior, and

    dist(O,U)=max(H-1,0)<1/60.                      (32)

Both left vertices have absolute x coordinate 1-L>1/2.
Both upper vertices have y coordinate H>61/100. It remains
only to check the actual lower-right vertex (L,H-1).

If H<=14/15, its vertical absolute coordinate is at least 1/15.
Since L>0, its norm is strictly greater than 1/15, including
the equality H=14/15.

If H>14/15, then (24) and d<61/60 give

    14/15<H<61/60-s/2,
    s<1/6,
    c>49/50.

For the last comparison,
1-1/36-(49/50)^2=133/11250>0. Equation (23) now sharpens
the actual first coordinate:

    L>c/4-d*s
      >49/200-61/360
      =17/225>1/15.                                (33)

The last reserve is 2/225. Thus this lower-right vertex also
has norm strictly greater than 1/15. All four vertices have
been covered on the whole domain, proving (1)--(2) for the
nonparallel frame.

Combined with Section 3, this proves the entire local theorem.
The same bounds give |x|<1 and |y|<61/60 throughout U, so

    |z|^2<1+(61/60)^2=7321/3600<9/4.

Therefore U lies wholly inside the open 3/2 disk and is
physically circle-clear at R>2. No U circle coefficient was
deleted in deriving this consequence.

## 11. Degree-free conditional proximity obstruction

Suppose there are two other actual units E,N satisfying the
additional proximity and vertex hypotheses of Section 1.
The proved actual U satisfies

    dist(O,U)<1/60<13/300,
    |Z_U|>1/15>19/300 for every U vertex.

Apply the complete unequal near-origin angular-budget theorem
to the unchanged three units U,E,N, with common test radius
19/300 and distance bounds 13/300,1/40,1/40. Its exact
three-unit reserve is

    cos(pi-acos(13/19))-cos(2acos(15/38))=3/722>0.

Thus their required actual interior angular measures exceed a
full turn, contradicting their pairwise disjoint open interiors.
This proves the conditional consequence, including both closed
1/40 distance endpoints.

No particular face allocation is inferred here. In a genuine
D02.L0134 caller, the full original central and unloaded-channel
theorems can supply E and N only after their actual occupancy
has been proved. This local result does not by itself assert that
occupancy or close any original graph/load flag.

## 12. Exact operative sources and review provenance

The new support calculation is Sections 9--10. The complete local
entry and owner cover are printed above at the strengthened scope;
none of the older all-loaded boundary-path conclusions is applied.

| Source | SHA256 | Exact use |
| --- | --- | --- |
| BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md | 3cd327d293d58daf2dcb8eb828dbee00efbc728171e8d17de60c3c9bc071f281 | Section 2 only, complete force-free Southeast normal cone with arbitrary neighbor degrees |
| LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_EXCLUSION.md | 5a95c3255a634f603a47c8311971902f2b8b699e4ebf2d076b21b01fddf941ba | Complete original P not in physical-boundary W at true loaded V2 and R^2>=13/4 |
| RADIAL_HALFSTRIP_FULL_RADIUS_BOUNDARY_SUPPORT_COROLLARIES.md | e8cb01fa67033056433ce210ae0c286700606533cae5db18fc641e8d568804f8 | Force-free radial North inner-normal and full-height barriers in Section 3 |
| RADIAL_INNER_CORNER_BOUNDARY_NEIGHBOR_QUARTER_SIDE_BOUND.md | 37f0f207a86a9d2c4ead42edcfaac01c5dbdd4f08bc66e98e41f985adedc4011 | Parallel-V actual intermediate W side, beta*C<1/4 at full original scope |
| PERPENDICULAR_HUB_AXES_NONPARALLEL_TIP_OWNED_RETURN_QUARTER_DISK_EXCLUSION.md | 8f564d6904cc8744175ec1664a88cbf84f51d74d146d4536a647662aac8a1487 | Only the complete local physical-two-mask V-owned contradictions, rederived in Section 5 |
| PERPENDICULAR_HUB_AXES_NONPARALLEL_TIP_NO_FREE_RETURN.md | e8be6a0daca1cbd50000c7167139ebb546e4dec96bdfdb889c65d2c0e04db0ef | Only Sections 2--5's physical-two free-return geometry; no unique-tip selector used |
| PERPENDICULAR_HUB_W_OWNED_TWO_CIRCLE_TIP_CLOSING_POCKET_CAPACITY_ONE.md | cef7f26f395968b9d1a68f07bb531569ba12e72500cd23839ca9d4f97bf29923 | Only full local Sections 2--5: actual chart, complete V/W masks, original weight inequality, F and side bounds |
| PERPENDICULAR_HUB_PARALLEL_TWO_CIRCLE_TIP_COMPLETE_POCKET_EXCLUSION.md | 4fc35299caf0580d9f995d4bfc253c7fad40f95c9f48ae34dc40b976108a5807 | Its local physical parallel-frame classification; all third-neighbor exits are expressly omitted and replaced by direct near-U bounds |
| UNEQUAL_NEAR_ORIGIN_UNIT_ANGULAR_BUDGET.md | 741ff2415b91fa8d490c601185994b7d947e000003c1ca702e423677eea3684e | Complete degree-free conditional three-unit consequence only |
| REVIEW_PERPENDICULAR_W_OWNED_TWO_CIRCLE_ENTRY_CYCLES_2026_10_28.md | aba5dc0f473dc2237aedfc332f4ca70b335e171985e63ba16156a106cc9f6dfe | Separate independent complete local entry audit, including p<=c and aligned W |
| REVIEW_REPAIRED_PERPENDICULAR_W_OWNED_TWO_CIRCLE_POCKET_HOUSE_2026_10_28.md | 639af1c3d57b662193a864672f78f7aaeb320123fdf67ff2957e6ab148458593 | Complete repaired source review; its shared-entry provenance is paired with the preceding independent entry record |
| REVIEW_PERPENDICULAR_PARALLEL_TWO_CIRCLE_COMPLETE_HOUSE_2026_10_28.md | d5689d5732e1d8cb375ff0f938ce63a28babc8448ce1bd926f892e345a3945e1 | Full parallel-source review, retaining original UV means and every weak owner alternative |
| REVIEW_RADIAL_INNER_CORNER_QUARTER_SIDE_BOUND_HOUSE_2026_10_28.md | c59537d7ee575437f4460b4eb525fa0a194ec1753c58c96bf5885a1c1013412d | Full independent all-beta radial scalar review |

This is a local geometric-and-full-tip theorem, not an adoption or
whole-family ledger change. It has no T properness assumption,
no silently contracted unloaded channel, and no selected unique-circle
subproblem. Every displayed scalar bound covers an entire continuous
interval with its relevant endpoints. No sampled placement, numerical
angle mesh, computational exclusion certificate, changed original
mean, shortened higher-degree equation, Lean compilation, CI,
workflow dispatch, commit, remote write, or metadata mutation is used.
