# An aligned nonparallel decorated triangle excludes every second private genuine-leaf root

Date: October 27, 2026.

**Status: complete proposed uniform geometric theorem and complete
aligned-nonparallel interface exit in all three remaining C2.34.b2 AP
domains, frozen for full root and independent review.** No whole AP
domain, coarse cell or shared ledger is changed.

Keep all nine actual units and the common compatible selected physical
certificate in 79/40<=R<=sqrt(1105)/16. Every original force, circle
weight, zero individual weight and actual side mean remains. The new
geometric kernel in Sections1--3 is independent of all forces.

## 1. An angular lower bound for any actual unit near the origin

Let 0<epsilon<1/60 and set r=3*epsilon<1/20. Let E be any actual
unit square meeting the closed disk D_epsilon. On the circle |z|=r,
measure the angular length of points in int E. We prove that this
length is strictly greater than pi/3.

If O belongs to E closed, choose in each own coordinate the endpoint
at distance at least1/2 from O. The corresponding quadrant of the
radius-r circle lies in E, with its open quadrant in int E, because
r<1/2. Its angular length is pi/2>pi/3. This includes an origin on
a side or a vertex.

Suppose O is outside E and its nearest point is in a relative side
interior. In an own orthonormal frame write

    E=[a,a+1] times [t,t+1],
    0<a<=epsilon, t<0<t+1.

Since1>2r, at least one of t+1>r or t<-r holds. In the first case
the whole open arc with x>a and y>0 is in int E; in the second use
the reflected lower arc. Its angular length is at least

    arccos(a/r)>=arccos(1/3)>pi/3.

Endpoints of the nearest side may instead be assigned to the following
vertex case; no endpoint is omitted.

If the nearest point is a vertex, reflect its inward axes to write

    E=[a,a+1] times [b,b+1],
    a,b>=0, 0<a^2+b^2<=epsilon^2.

The far sides lie outside the radius-r disk, so the actual interior
arc has angular length

    pi/2-alpha-beta,
    alpha=arcsin(a/r), beta=arcsin(b/r).

Put z^2=(a^2+b^2)/r^2<=1/9 and t_0=ab/r^2 in[0,z^2/2]. Then

    cos(alpha+beta)=sqrt(1-z^2+t_0^2)-t_0
       >=sqrt(1-z^2+z^4/4)-z^2/2
       =1-z^2>=8/9>sqrt(3)/2.

The middle inequality uses the strictly decreasing function
sqrt(1-z^2+t^2)-t; 1-z^2>0. Also alpha+beta lies in[0,pi/2),
because a^2+b^2<r^2. Therefore alpha+beta<pi/6 and the actual
arc length exceeds pi/3. The strict final comparison has squared
reserve64/81-3/4=13/324>0. This includes a=0 or b=0.

These cases prove the bound for every actual near unit, with no
condition on its vertices, orientation, circle status or true degree.

## 2. Two larger arcs when vertices stay away

Let H contain O openly and suppose every actual H vertex has norm
greater than r. We prove that H occupies angular length greater
than pi on the same circle.

As r<1/2, at most two H faces can cut this circle; two such faces
must be adjacent. A single face at positive distance a from O
removes an arc of length2 arccos(a/r)<pi. With two cutting faces
at distances a,b in(0,r), their common actual vertex has squared
norm a^2+b^2>r^2. Hence

    arccos(a/r)+arccos(b/r)<pi/2.

The union of their two removed arcs has angular length at most twice
that sum, strictly less than pi. A tangent removes no angular length,
and a noncutting face removes none. Thus in every full own-frame case
the interior H arc has length greater than pi.

Now let A be a distinct actual unit meeting D_epsilon, and suppose
every actual A vertex likewise has norm greater than r. Since H
contains O openly, the closed A avoids O. Its nearest point cannot
be a vertex. In its nearest-face frame A=[a,a+1] times [t,t+1],
0<a<=epsilon and t<0<t+1, both actual near-face vertex norms exceed r.
Consequently

    -t>sqrt(r^2-a^2), t+1>sqrt(r^2-a^2).

The entire circular cap x>a lies in int A. Its angular length is
2 arccos(a/r)>=2 arccos(1/3)>2pi/3. This covers every actual side
slider, including limiting positions by the strict vertex hypothesis.

## 3. Complete three-unit consequence

Suppose, in addition, a third distinct actual unit P meets D_epsilon.
Sections1--2 give disjoint open-interior portions of the same circle
with total angular length strictly greater than

    pi+2pi/3+pi/3=2pi,

which is impossible. Thus:

**Geometric theorem.** If H contains O openly, A and P are two
distinct other actual units meeting D_epsilon, and every H vertex
has norm greater than3*epsilon, then at least one actual A vertex
has norm at most3*epsilon.

All three squares are retained. No contact, leaf, force, mask or
relative orientation is a premise of this geometric theorem. Its
contrapositive does not infer that a nearby point is an actual vertex.

## 4. Exact genuine-triangle and second-leaf scope

Let H-A-B-H be an actual positive triangle with O in int H. A has
exactly its two triangle edges and a genuine leaf L_A. B has its
true positive degree two, hence positive circle load by the physical
touching-neighbor transmitter obstruction. H keeps arbitrary further
forces. Suppose A is aligned with its own leaf and its two original
triangle force lines are nonparallel.

Let P be another actual genuine-leaf root, distinct from H and A,
with its true degree and all other forces arbitrary. Its real leaf
is L_P. The two genuine leaves are distinct because a genuine leaf
has only one positive parent. Both roots and leaves remain in the
same original nine-square packing.

**Uniform theorem.** This complete configuration is impossible.

Since every other closed unit avoids O, the actual leaf alternatives
make both leaves S, with

    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60, R>sqrt(17)/2.

Each genuine root contains its actual inward radial point epsilon*e
in the direction e of its own leaf, and is physically circle-clear.
These are degree-free physical genuine-leaf consequences. In particular
A and P meet D_epsilon. If P had been B, physical clearance would
already contradict B's positive circle load; that case is also excluded.

## 5. The entire origin-only aligned triangle chart

Use Sections1,3--6 of

    GLOBAL_CLOSURE_TWO_S_LEAF_ROOTS_ALIGNED_NONPARALLEL_EXCLUSION.md
    SHA256 d9bcc857fd2fe91c65079567a0bd6f0df4c1b09f6b5d3a6bb3ebc916ed99738e.

Its Section2, which uses a genuine leaf at H, is not used. The full
origin-only extraction is written in Section2 of

    GLOBAL_CLOSURE_TWO_DECORATED_TRIANGLES_ALIGNED_NONPARALLEL_EXCLUSION.md
    SHA256 c32ae32488a5ccc577e08235990ea82c07fc6e18c742d16ce3a66f6ce0a77e61.

The B-owned transverse alternative is entirely excluded there by the
true A3/B2 equations and H origin-interiority, before using any second
triangle or H leaf. Its full remaining H-owned alternative gives the
following original chart, with all means and physical B masks retained.

In the actual A own frame, its leaf points along the positive first
axis and

    A=[epsilon,d] times [-w,h], h+w=1,
    h>16/25, 0<w<9/25.

The original normal coefficients a,b,c,t are positive unit-pair
coordinates, a^2+b^2=c^2+t^2=1. Here t is a coefficient, not the
radius or a mean. Put

    K=a*t+b*c>0, L=b*t-a*c>K,
    h=a*t/K, w=b*c/K.

In the resulting actual H own frame m,k,

    H=[-eta,1-eta]m+[p-1,p]k,
    eta=epsilon*t-w*c in(0,epsilon),
    3/10<p<367/600,
    e_A=-t*m+c*k.                                   (2)

All facts in (2) precede any equation comparing two branch resultants.
The lower p bound is the complete actual B-corner rearrangement
inequality p>1+sqrt(2)-R>3/10. The upper bound and L>K belong to
the same full original B owner/mask calculation. Consequently

    1-eta>59/60, p>3/10, 1-p>233/600.                (3)

In particular every actual H vertex has norm greater than3/10,
which is greater than3*epsilon. No equation or feature at P was used.

## 6. The third near unit forces the actual A slider to be small

Apply the geometric theorem in Section3 to the actual H,A,P.
It supplies an actual A vertex of norm at most3*epsilon.
In A's own rectangle, both far-side vertices have first coordinate
d>1, and the upper near vertex has height h>16/25. Therefore the
vertex must be the actual lower near vertex (epsilon,-w). Thus

    epsilon^2+w^2<=(3*epsilon)^2,
    w<=sqrt(8)*epsilon<3*epsilon.                    (4)

The complete B calculation L>K also gives b>a: otherwise
t*(b-a)>c*(a+b) could not hold. The unchanged true A identities
therefore give

    c/t=(w/(1-w))*(a/b)<w/(1-w).

Using (4) and epsilon<1/60 yields

    0<c<3*epsilon/(1-3*epsilon)<1/19,
    t>sqrt(360/361)>99/100.                          (5)

This is a consequence of the whole near-unit geometry and the actual
original mean; no slider was assigned to zero or to a chosen endpoint.

## 7. H leaves only a narrow direction range for any other genuine leaf

From (2),(4),(5), the actual shallow H side obeys

    eta/epsilon=t-(w/epsilon)*c
       >99/100-3/19=1581/1900>41/50.                 (6)

Every other H side has distance from O greater than epsilon by (3).
Thus every point of D_epsilon outside int H must satisfy

    z.m<=-eta.

Apply this to the actual point epsilon*e_P belonging to P. It cannot
lie in int H, since the two actual closed units have disjoint open
interiors. The degree-free genuine leaf direction therefore satisfies

    e_P.m<=-eta/epsilon<-41/50,
    |e_P-(-m)|^2=2*(1+e_P.m)<9/25,
    |e_P-(-m)|<3/5.                                 (7)

This uses no contact between P and H, no equation at P, and no
replacement of P by a triangle tip or lower-degree body.

For the actual A leaf, (2),(5) give e_A.m=-t and

    t>sqrt(360/361)>647/648,
    |e_A-(-m)|^2=2*(1-t)<1/324,
    |e_A-(-m)|<1/18.                                (8)

The exact squared comparison in (8) has reserve
360/361-(647/648)^2=47591/151585344>0. Both sides before squaring
are positive. The side-margin reserve in (6) is23/1900>0.

## 8. The two distinct actual leaf centers contradict unit separation

Equations (7)--(8) give

    |e_A-e_P|<3/5+1/18=59/90.

Their actual radial-S centers in the same radius-R circle are
(d+1/2)e_A and (d+1/2)e_P. Since d+1/2<91/60, their distance is
strictly less than

    (91/60)*(59/90)=5369/5400<1.                     (9)

The exact final reserve is31/5400. Distinct interior-disjoint unit
squares have disjoint open radius-one-half incircles, hence centers
at distance at least one. Equation (9) is the contradiction.

The uniform theorem has retained all H forces, the real A3/B2 stars,
the arbitrary true degree of P, every physical leaf mask and the
original side means. Only the original finite A-star/fixed-tip
restrictions of the common selected certificate are used in Section5;
none is chosen again after extracting a stress.

## 9. Complete stated interfaces in the three original b2 AP domains

The complete original three-domain cover is
ROOTED_C2_34_TWO_BRIDGES_THREE_DOMAIN_REDUCTION.md, SHA256
8918c0e3e77cbc9f90899a29ebd2233c87858a00ecf1e0ffca2a684ccdd5cb0a.
Its full origin input e77c19d2 gives the common H open, with the
actual triangle H-A-B-H, genuine A leaf and true loaded B2. Each
remaining Q has its distinct real private leaf root P:

| Original Q edges | True degrees at H,A,P,B | Other private true degrees |
| --- | --- | --- |
| HP,PK,KQ,QH | H4,A3,P3,B2 | K2,Q2 |
| HK,HP,HQ,KP,KQ | H5,A3,P3,B2 | K3,Q2 |
| HP,HQ,KP,KQ,PQ | H4,A3,P4,B2 | K2,Q3 |

All eight positive bodies and the arbitrary ninth actual unit remain.
The uniform theorem uses neither the P3 equation in the first two
rows nor a fabricated P3 equation in the last: its second-leaf
geometry is degree-free. It excludes the entire aligned-nonparallel
A interface in each original row, for every private load mask,
circle-weight endpoint, actual leaf slider and contact owner.

The parallel-aligned A and tilted A-owned interfaces remain separate
original obligations. No whole one of the three AP domains, no
C2.34.b2 cell and no original equality family is claimed closed by
this source alone. No Lean build, numerical pose, CI, workflow,
remote write or shared-ledger mutation is used.
