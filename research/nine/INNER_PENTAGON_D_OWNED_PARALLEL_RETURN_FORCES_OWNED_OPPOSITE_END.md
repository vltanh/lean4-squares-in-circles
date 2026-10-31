# A D-owned parallel return forces the opposite unloaded end to own its hub contact

Date: October 28, 2026 UTC. Author: pentagon_resume continuation.

**Status: complete proposed radius-free owner-interface theorem, frozen
for full independent and root review.** In the original two-unloaded-end
pentagon, the entire D-owned DH / same-axis DC feature cannot have a free
HA contact. It therefore forces genuine A-side ownership at the opposite
end after the already complete H-owned exclusion. Every original CD, DE
and HC mean and every physical contact-set endpoint remains.

The proof includes a separate force-free support lemma for an arbitrary
unit square. No circle equation or positive boundary weight is used in
the local argument. The original B3, C3 and E2 equations remain intact;
none is replaced by a smaller star. This is not yet a whole L124 closure.

## 1. Exact original scope and full parallel D3 chart

Retain the actual positive graph

    HA, HB, HC, HD, AB, BC, CD, DE, EA.

H is genuinely unloaded of degree four. A and D are genuinely unloaded
of degree three, with their full original neighborhoods H,B,E and H,C,E.
The other true degrees, circle loads, physical masks and all original
force magnitudes, normals, applications and shared means remain.
All actual unit squares have disjoint open interiors.

Use the same common selected physical certificate as the already
complete two-unloaded-end H-owned theorem. That theorem excludes both
H-owned HA and H-owned HD, including their positive-length shared sides.
Consequently the original HA application is a strict H vertex, and a
D-owned HD has a strict H vertex at a relative interior point of its
actual D side.

Assume D owns DH and its original DC normal is that same own axis.
Normalize the actual D frame to

    D=[0,1]^2,
    F_DH=(-gamma,0) at P=(0,t), 0<t<1,
    F_DC=(-mu,0) at Q_C=(0,s), 0<=s<=1,
    gamma,mu>0.

The whole H and C lie in x<=0 and have maximum x coordinate zero.
H is nonparallel to D and has P as its unique maximum-x vertex.

No third actual unit can contain P. The D tangent sector there is the
right half-plane. H's quadrant sector lies strictly inside the left
half-plane, since both of its inward axes have strictly negative x
components. The two remaining angular gaps are each strictly smaller
than pi/2. A third unit would require a connected tangent sector of at
least pi/2 in one of those gaps, which is impossible. In particular

    P is not in A, B, or C, and s!=t.                    (1)

Reflect the whole configuration vertically if necessary so that t<s.
The full D3 force and torque equations now give exactly

    F_DE=(gamma+mu,0), Q_E=(1,u),
    u=(gamma*t+mu*s)/(gamma+mu),
    0<t<u<s<=1,
    E subset {x>=1}.                                   (2)

Here s and u are the actual original means. Shared CD or DE intervals
and either endpoint remain in (2). No external unit is assigned an
axis or a frame from the D-owned normals alone.

Write the entire actual H as

    e=(-a,-b), f=(-b,a), a,b>0, a^2+b^2=1,
    H=P+[0,1]e+[0,1]f.                                 (3)

The orthonormal frame (e,f) has negative orientation. All force and
zero-torque equations below are expressed in this same frame; multiplying
every determinant by that common orientation sign does not change a zero
torque equation.

**Theorem.** The original HA contact cannot be free. Its only remaining
physical owner is A.

## 2. The complete actual HC support cover

Let N be the original unit normal from H into C, and let S be its
unchanged application or shared-side mean. Actual supporting half-planes
give

    N.P <= N.S <= N.Q_C,
    (s-t)*N_y>=0.

Thus N_y>=0. Equality is impossible. An East H-to-C support would give
min_C x=max_H x=0, contradicting C's positive width and max_C x=0.
A West support would give min_H x=max_C x=0, contradicting the positive
width of H. Therefore

    N_y>0.                                              (4)

Put L=s-t, so 0<L<1. For any unit direction N,

    N.(Q_C-P)<=L<1.

If both own H components N_e,N_f were positive, its H support would
be the opposite vertex P+e+f and have relative value N_e+N_f>1.
The actual C point Q_C could not be beyond this support. If N were
either positive own axis +e or +f, the relative H support would be
one and gives the same contradiction. Thus neither the opposite
strict vertex nor either positive own side can occur.

The strict vertex P is excluded by (1). The vertex P+e has support
components N_e>0,N_f<0, which gives world vertical component
-b*N_e+a*N_f<0, contrary to (4). The own normal -f likewise has
negative world y component. The complete remaining cover is precisely

    F_HC=(-C,D0) in the (e,f) frame,
    C>0, D0>=0,
    S=P+tau*f, 0<tau<=1,
    D0>0 implies tau=1.                                (5)

For D0=0 this keeps the entire actual side parameter tau. Its zero
endpoint would be the forbidden actual point P, so is excluded by
geometry, not by changing a mean. Every vertex, side and normal-cone
endpoint has now been considered. No equation at C was used.

## 3. Full H4 and the actual AE bridge force the lower adjacent HA vertex

The HA application V is a strict H vertex. It cannot be P by (1).
It cannot be P+e+f, whose x coordinate is -a-b<-1: every actual
AE point T lies in E and has T_x>=1, so its distance from that
vertex would exceed two, contrary to the diameter sqrt(2) of A.
Thus V is P+e or P+f.

### 3.1. The upper adjacent vertex is impossible

Suppose V=P+f. The strict original HA vector has components
(-A0,B0), with A0,B0>0. Its moment about P in the own H frame is
A0>0. The HC moment from (5) is tau*C>0. The HD force applies
at P and has zero moment there. Full H4 torque therefore requires
the original HB moment about P to be strictly negative.

We check the whole HB support cover. The strict vertex P has zero
moment and is also physically excluded. The strict vertex P+f has
positive moment. The opposite HA vertex P+e is impossible because
the actual A and B touch; two opposite strict supports of one unit
cannot have touching external neighbors. The own normals -e and
+f give nonnegative moments. The two potentially negative own
normals +e and -f have negative dot product with the original strict
HA vector, and are excluded by the actual H-A-B triangle and the
owned-axis triangle theorem. The only remaining negative-moment
feature is the opposite H vertex P+e+f, with an original HB vector
(X,Y), X,Y>0, X>Y.

The full H4 force and torque equations are then

    X=a*gamma+A0+C,
    Y=b*gamma-B0-D0,
    A0+tau*C+Y-X=0.

Consequently

    (b-a)*gamma=B0+D0+(1-tau)*C>0,
    b>a.                                               (6)

On the other hand V_x=-b. The actual AE contact and A's diameter
give 1+b<=sqrt(2), so b<=sqrt(2)-1<1/2. Thus a>b, contradicting
(6). This excludes the entire upper-vertex feature, with the
original HC side mean retained.

### 3.2. The lower vertex and a genuinely strict upper HC vertex

We must therefore have

    V=P+e=(-a,t-b),
    a<=sqrt(2)-1<1/2,
    b>a.                                               (7)

The strict HA vector has own components (A0,-B0), A0,B0>0.
We next exclude the H-owned HC axis D0=0 in (5). That actual -e
axis and the physical H-B-C triangle force the HB e component
to be nonpositive.

If HB were strict at P+f, it would be opposite strict HA and the
actual AB contact would be impossible. If HB were +f or -e, its
dot product with the original HA normal would be negative, contrary
to the actual H-A-B triangle. A strict negative/negative HB would
apply at P, impossible by (1). The remaining possible nonzero HB
vector is the own -f axis. But then the f components of HA, HB and
HD are all strictly negative, and that of HC is zero. Full H4 force
balance is impossible.

Thus D0>0 and tau=1 in (5). In particular the actual C contains
the unchanged upper adjacent H vertex

    W=P+f=(-b,t+a).                                    (8)

This conclusion came from the full H4 and physical triangle supports;
it did not move a side application to its endpoint.

## 4. A force-free support lemma for any actual unit

Let K be any actual unit square with a minimum-x support point
Q=(q,z). The point Q may be an arbitrary original side mean.
Let T be another actual boundary support point satisfying

    T_y<z, T_x<q+1.                                    (9)

If g is any inward supporting unit normal at T, so K lies in
g.(X-T)>=0, then

    g_y>=0.                                           (10)

This is a whole-unit geometric statement with no force, load,
degree, circle, or neighboring-unit premise.

For aligned K, its whole rectangle is [q,q+1] times [r,r+1],
with r<=z<=r+1. Condition (9) rules out its right side and top
side. The remaining left/bottom sides and their possible corner
have inward normal cones with nonnegative y component.

For nonparallel K, Q is its unique left vertex and

    K=Q+[0,1](c,-d)+[0,1](d,c),
    c,d>0, c^2+d^2=1.

Its upper vertex has height z+c>z and its opposite vertex has
x coordinate q+c+d>q+1. The bottom vertex's two inward normal
generators (-c,d) and (d,c) both have positive y component. The
two sides incident with that bottom vertex have the same property.
The side from Q toward the upper vertex has y>=z. The only
remaining side is

    Q+(d,c)+lambda*(c,-d), 0<=lambda<=1,

whose inward normal is (-d,-c). For a point there to have y<z,
one would need lambda>c/d. Its x coordinate would then be

    q+d+lambda*c>q+d+c^2/d=q+1/d>q+1,

contrary to (9). This covers every side, corner and closed normal
endpoint and proves (10).

## 5. The whole C lies above V, and every original AE normal points weakly up

First the whole actual C satisfies

    min_C y>t-b=V_y.                                   (11)

If C is aligned, it is [-1,0] times [r,r+1]. Its actual point W
from (8) gives r>=t+a-1>t-b, because a+b>1.

If C is not aligned, its unique maximum-x vertex is Q_C=(0,s),
and its actual inward axes may be written (-c,-d),(-d,c), with
c,d>0 and c^2+d^2=1. Its minimum and maximum heights are s-d
and s+c. Since it contains W, c>=a-L whenever a>L.

If L>=a, then L+b>=a+b>1>d, so s-d>t-b. If 0<L<a, the actual
upper-point condition gives

    d<=sqrt(1-(a-L)^2)<b+L.

The final strict comparison follows by squaring the positive sides:

    (b+L)^2-[1-(a-L)^2]=2L*(b-a+L)>0

by (7). This again gives s-d>t-b. Every aligned and nonparallel
C frame and every original maximum-x side mean has been retained.

Now take any actual point T of A intersect E. The original V from
(7) is another actual point of A. From the unit diameter and (2),

    T_x>=1,
    T_x<=-a+sqrt(2)<2,
    T_y<t<u.                                           (12)

For the last strict inequality, T_y>=t would imply

    |T-V|^2>=(1+a)^2+b^2=2+2a>2.

The support lemma in Section 4 applies to E with its actual minimum-x
point Q_E=(1,u), for every original AE support point and every shared
mean. Thus the unchanged original force satisfies

    (F_AE)_y>=0.                                       (13)

The H-to-A vector strictly exposes V=P+e, so it is a positive
combination of e and -f. Both of those actual directions have
strictly negative y component. Therefore (F_AH)_y>0. The complete
original unloaded A3 force equation gives

    F_AH+F_AB+F_AE=0,
    (F_AB)_y<0.                                        (14)

No circle equation, moment sign about the circle origin, or equation
at B, C or E has been used.

## 6. A free HA would have two rightward A axes and no shared AE

Suppose now that HA is free. V is then an actual A vertex as well
as a strict H vertex. An actual AE point has x>=1, so A's positive
horizontal reach from V_x=-a is greater than one. Both actual
inward A axes at V must have positive x component: if at most one
were positive, the total rightward reach would be at most one.
Naming the upper and lower inward axes, the full actual square is

    g=(c,d), h=(d,-c), c,d>0, c^2+d^2=1,
    A=V+[0,1]g+[0,1]h.                                (15)

Assume AE had positive length. Its normal is an own A axis. By
(13), the only possibilities are +g or -h. The -h support consists
of V+[0,1]g, whose x coordinate is at most -a+c<1; it cannot touch
E. Hence the unchanged normal would be +g and the complete actual
E pose would be

    E=V+[1,2]g+[r,r+1]h, -1<r<1.                     (16)

The actual minimum-x vertex of this nonparallel E is V+g+r*h.
Its x coordinate equals one and its y coordinate equals the
original D-contact height u. Equations (7), (15), (16) therefore
give

    c+r*d=1+a,
    u=t-b+d-r*c>t.

The first equality forces r>0, since c<1. The second implies
d>b and hence c<a. The first equality now gives

    r*d=1+a-c>1,

contradicting r<1 and d<1. Thus the entire actual AE contact is a
physical singleton. This proof preserves every possible shared
slider before excluding it; it does not infer its type from an
endpoint-valued force mean.

## 7. The selected free A3 forces AB to be a downward shared side

If AB were also a physical singleton, all three actual A ports
would be pairwise distinct. The AH and AB applications cannot
coincide by the complete two-unloaded-end coincident-free-return
theorem, applied after the legitimate graph reflection. AH and AE
are distinct because the full D3 touching-return theorem, using
the real HC contact, makes E closed-disjoint from H. AB and AE
are distinct because the full A3 touching-return theorem, using
the real HB contact, makes E closed-disjoint from B.

The uniform compatible distinct-singleton selector would then
forbid the retained free AH normal at unloaded A3. That theorem
was imposed before multipliers; no original normal is changed
here. Consequently AB must have positive-length physical
intersection.

Its original normal is one of the four own A axes in (15).
The A-to-H normal is strict at V, with both own components
negative. The actual A-H-B triangle excludes +g and +h by their
negative dot products with that original A-to-H vector. The
remaining axis -h has positive world y component, contradicting
(14). Therefore

    n_AB=-g=(-c,-d),
    B=V+[-1,0]g+[r_B,r_B+1]h, -1<r_B<1.              (17)

The entire original AB mean remains on its actual shared segment.

If r_B<0, V lies in the relative interior of B's side along h.
In the actual A frame (g,h), B occupies the half-plane g<=0 at V,
and A occupies the quadrant g>=0,h>=0. The actual H vertex sector
has angle pi/2 and must fill the remaining quadrant g>=0,h<=0.
It would have +g as an inward H axis. But the original A-to-H
normal has strictly negative g component, incompatible with V
being its actual minimum support on H. Thus

    r_B>=0.                                            (18)

For every actual point of B, (15), (17), (18) now give

    y=V_y-tau*d-lambda*c<=V_y,
    0<=tau<=1, r_B<=lambda<=r_B+1.

This contradicts the physical BC contact, because the whole C
lies strictly above V_y by (11). The entire free-HA alternative
is excluded.

## 8. Literal scope and the remaining original owner classes

The original HA cannot be H-owned by the complete two-end theorem,
and Sections 1--7 exclude free HA when DH is D-owned and DC has
the same D axis. The only remaining HA feature is A-owned, with
the actual H vertex in the relative interior of an actual A side.

This conclusion is radius-free at the common selected physical
premises. It retains every CD, DE and HC application and shared
mean, all their endpoints, the genuine A3/D3/H4 systems, all true
degrees and physical masks at B,C,E, and every actual completing
unit. In original H4_D0.L124, both end stars are genuinely
unloaded, so the theorem applies to the entire stated mixed owner
row. The allowed graph reflection gives its opposite-end image.

It does not exclude the same-axis row when HA is A-owned, nor the
nonaxis or perpendicular DC rows under D-owned DH. Other mixed
and both-externally-owned interfaces therefore remain. No whole
original fine family or coarse parent is credited by this source.
The loaded A of L0124 cannot use the unloaded A3 equation here;
that family has its separate complete four-boundary proof.

## 9. Exact direct inputs

| Source | SHA256 | Exact use |
| --- | --- | --- |
| INNER_PENTAGON_TWO_UNLOADED_ENDS_EAST_RETURN_AND_WHOLE_H_OWNER_EXCLUSION.md | fcd6217a246b06e39ed34eb4bbd94c8e12ab47dd958cbf8de04859b2815f5d96 | Complete original H-owned HA/HD exclusion, including shared hub sides, with both ends genuinely unloaded |
| INNER_PENTAGON_TWO_UNLOADED_ENDS_COINCIDENT_FREE_RETURN_COMPLETE_EXCLUSION.md | aa8efe6f8dd6d9da5fbd1c0dcb8955255b0c9ace6bb71c8d1f4c57eaae5e9422 | Reflected complete free-AH/coincident-AB feature, before the distinct-singleton selector is used |
| GENERAL_UNLOADED_THREE_DISTINCT_SINGLETON_PORTS_HAVE_NO_FREE_NORMAL_SELECTION.md | 7700a4547542af9fc25b0e0b3d14f2113529069df0b007443c18d690da1137bb | Existing compatible pre-extraction selector, only after all three actual A singleton points are proved distinct |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 | Full genuine D3 and A3 give the necessary closed disjointness of E from H and B |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Full actual support span, opposite strict corner obstruction, and owned-axis triangle implication |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Strict singleton convention and actual tangent-sector compatibility |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original force, torque, application and shared-mean conventions |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a | Exact original graph, true unloaded ends and permitted reflection |

No existing frozen source, roadmap, ledger, metadata or flag is edited.
No normal is selected after extraction, no mean moved, and no false
smaller star is used. There is no sampled pose, angular mesh, numerical
geometric exclusion certificate, Lean compilation, CI, workflow, commit
or remote operation in this manuscript.
