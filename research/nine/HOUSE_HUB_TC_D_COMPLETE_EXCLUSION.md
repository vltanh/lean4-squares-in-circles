# The complete house hub-TC attachment with a genuine D leaf is excluded

Date: October 27, 2026.

**Status: complete original-family hand proof, submitted for full
independent and root review.** This is the exact house-hub load family
TC with a genuine D leaf. All A4/D3/T2/B2/C2/L1 equations, original
application means, physical masks and nine actual squares are retained.
The secondary minimizer is chosen before normal selection and stress
extraction. No positive force is added at a later physical contact.

## 1. Original graph, leaf, channel and radius

The positive block edges are

    AT, DT, AD, AB, BC, CD,

and AL is the genuine pendant edge at hub A. Exactly T and C have
positive block circle load. Thus A has its three original block forces
and the genuine leaf force; D is an unloaded body of degree three;
B is the unloaded degree-two body on A--B--C. The actual T and C
are loaded degree-two bodies. The three other physical units remain
arbitrary. An unloaded unit may have physical zero-weight circle
contacts.

Choose a minimum-radius nine-unit packing which minimizes the sum of
all nine squared center norms among radius minimizers. The compactness
argument is Section 1 of FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md.
Make the existing compatible finite normal selections and extract the
positive certificate only after this choice. In particular a point-only
vertex/vertex contact has its original normal strictly exposing both
vertices.

Write Q=1105/256. The same-nine radius theorem gives R>2, and the
examined counterexample has R²<=Q. Rotate the real D leaf East.
Its genuine radial geometry and the original strict/nonradial point
convention give

    r=R−sqrt(2), s=1−r,
    A=[−s,r] × [−b,a], a,b>0, a+b=1,
    P_AL=(r,0), n_AL=East.                            (1)

The actual leaf L has vertices

    (r,0), (r+1/sqrt(2),1/sqrt(2)), (R,0),
    (r+1/sqrt(2),−1/sqrt(2)).

In particular O is in the open interior of A. Only the genuine
radial-D chart in Sections 1–2 of
RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md is used here;
its separate true-degree-three selection theorem is not applied to A.

The full UNIT_BYPASS_NORMAL_CHANNEL.md applies to A--B--C with
the actual unit D as its physical bypass. It uses the unchanged
equations of B alone. There is an original unit direction n, a port
p in A intersect B, and a unit channel reserve such that

    p_BC=p+n, A subset {n·X<=h}, C subset {n·X>=h+1},
    h=n·p=h_A(n)>0.                                  (2)

B is a side-normal unit in this direction. The projection of D on n
contains [h,h+1], and D and B are separated along the other B axis.
No projection mean is centered.

The sharp contained-unit support theorem in Section 1 of
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md gives h+1<=d, where

    d=sqrt(R²−1/4)−1, epsilon=d−1.

For clarity, that local theorem needs only the actual containment:
every unit center has norm at most d+1/2, and every directional
halfwidth is at least 1/2. Hence a contained unit beyond support k
has k<=d. No end-triangle equation is used.

By (2) we have

    R>sqrt(17)/2, 0<epsilon<1/60, 0<h<=epsilon.         (3)

This already excludes all lower and critical radii. The resulting
strict D margins are

    16/25<r<2/3, 1/3<s<9/25.                         (4)

Write n=(xi,eta). Since the smallest horizontal margin of A is s,
h>=s|xi|, so |xi|<1/20. Reflect the entire original packing vertically
if necessary to have eta>0. Then

    eta>59/60, 0<a<1/59, b>58/59.                    (5)

Indeed h>=a eta. Put m=(eta,−xi), the right transverse B axis.
In the (m,n) coordinates B has the exact rectangle

    B=[z,z+1] × [h,h+1], q=p·m in [z,z+1].           (6)

All these are the original actual coordinates.

Since T is a physical boundary unit touching A and a<1/4, the
complete force-free D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md applies
to its actual AT port and normal. It gives

    (n_AT)_Y<=0.                                    (7)

That theorem permits arbitrary neighbor degrees, every owner, every
side mean and every physical circle mask.

## 2. A force-free horizontal reach bound above height one

**Lemma 2.1.** If a unit E is contained in the disk of radius sqrt(Q)
and lies in Y>=1, then every point of E has |X|<3/5.

Write a lowest vertex as P=(p,v), v>=1. After horizontal reflection,
its inward axes can be written

    (c,k), (−k,c), c>=k>=0, c²+k²=1.

The case k=0 includes an entire lowest side. The vertical span gives
c+k<=sqrt(Q)−v<=sqrt(Q)−1<27/25. If k>=9/100, monotonicity of
k+sqrt(1−k²) on [0,1/sqrt(2)] would give
c+k>=9/100+sqrt(9919)/100>27/25. Consequently

    k<9/100, c>99/100.                              (8)

The leftmost vertex has X_-=p−k and height v+c>199/100. Hence

    X_-²<Q−(199/100)²<9/25,                         (9)

where the last reserve is 591/160000. In particular X_->−3/5.

The rightmost vertex has X_+=p+c and height v+k>=1. If X_+<=0
its required upper bound is immediate. Otherwise containment gives
X_+<11/6, since Q−1<121/36. Its upper adjacent vertex is
(X_+−k,v+c+k), so

    Q >= (X_+−k)²+(1+c+k)²
       = X_+²+(1+c)²+2k(1+c+k−X_+)
      >= X_+²+(1+c)².

Here X_+<11/6<199/100<1+c. Equation (9) therefore gives
X_+<3/5 as well. Reflection covers the other ordering of the two
axes. Every point lies between the two actual extreme coordinates.
This proves the lemma, including all axis endpoints.

Apply it in the actual (m,n) frame to C, whose minimum n coordinate
is h+1>1. If xi>0, the actual A port in (2) is p=(r,a), so

    q=r eta−a xi
      >(16/25)(59/60)−(1/59)(1/20)
       =3/5+2521/88500.

But p+n belongs to C and has transverse coordinate q, contrary
to the lemma. We have proved

    xi<=0.                                         (10)

## 3. The bypass D cannot be to the right of B

The complete transverse bypass theorem gives precisely the two
possibilities

    max_D(m·X)<=z, or min_D(m·X)>=z+1.               (11)

Suppose the latter holds.

First D cannot contact A's bottom side. It has an actual C contact
at n-height at least h+1>1, and a unit's width is at most sqrt(2).
Thus min_D(n·X)>−1/2. On the entire A bottom side, (4)–(5) give

    n·(X,−b)<(2/3)(1/20)−(58/59)(59/60)
             =−14/15.                             (12)

D cannot contact A's West side either. If xi<0, put e=−xi>0;
the actual A channel port is its unique upper-left vertex
p=(−s,a), with q=−s eta+a e. Every A West-side point has
m-coordinate at most q. The same p is in the relative interior
of B's channel side: if it were a B vertex, the original side-axis
normal at a point-only vertex/vertex contact would fail the strict
point convention. The nonparallel frames cannot have a shared
positive side. Thus z+1>q, and the right-hand alternative in
(11) excludes the whole West side.

If xi=0, A and B are parallel. Their actual AB side intersection
has positive length, since a point-only axis-normal contact again
violates the strict convention. Hence z+1>−s, excluding the
West side in this case too.

The only remaining actual AD support features at A are North,
East and strict northeast.

We record a restriction useful again below: **AD North is impossible
throughout this whole proof, independently of the side in (11).**
The actual physical triangle A-D-T and the owned-axis triangle
theorem give (n_AT)_Y>=0. By (7) it is zero. The full A4 vertical
equation would then have strictly positive terms from AB and AD,
and zero from AL and AT, a contradiction.

Suppose AD is East. The same physical triangle makes (n_AT)_X>=0.
Together with (7), this leaves East, strict southeast or South.
South is impossible: T would lie wholly in Y<=−b, whereas for D,
using Y=eta(n·X)−xi(m·X),

    min_D Y>−1/2−R/20>−1/2−(52/25)/20>−b.           (13)

The final comparison has reserve at least 5591/14750 using (5).
It contradicts the actual DT contact.

If AD is strict northeast, an AT West or South axis violates the
physical owned-axis triangle theorem. A strict southwest AT is
at the opposite A vertex and is impossible by the physical
opposite-vertex triangle argument. That argument is degree-free:
the support-span lemma gives the opposite neighbor n-span strictly
less than one, while the diagonal A support difference is at least
one. Together with (7), only East or strict southeast AT remains.

Let the unchanged A4 magnitudes of AL, AB, AD, AT be respectively
lambda,mu,alpha,gamma>0, and let the original AD and AT unit
normals be v,w. In the surviving right-hand cases v_X,w_X>=0.
Their actual moments about P_AL=(r,0) are at most b v_X and
b w_X respectively. An East mean has moment −Y<=b; the
northeast vertex has moment −a v_X; the southeast vertex has
moment b w_X. No side mean is replaced.

If xi=0, the full horizontal force equation is already strictly
positive. If xi=−e<0, the actual AB moment about P_AL is
−eta+a e, and the full horizontal equation gives

    alpha v_X+gamma w_X=mu e−lambda.

Consequently the complete original A torque is at most

    mu(−eta+a e)+b(mu e−lambda)
       =mu(e−eta)−b lambda<0,                       (14)

contrary to equilibrium. This uses all four A forces. The
right-hand alternative in (11) is excluded, leaving

    max_D(m·X)<=z<=q.                               (15)

## 4. The full loaded C2 equations force the vertical channel

Suppose first that C's two actual pair normals are nonparallel.
Let v be its original outward normal toward D. The other is −n,
at p+n. The complete local proper-concurrence lemma
FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md, Lemma 1.1, gives a point Q_C
which is a positive multiple of the original nonzero circle
resultant F_C, and every actual application is Q_C plus a
nonnegative multiple of its outward normal. Thus

    Q_C·m=q, F_C=mu_C n−nu_C v,
    P_CD=Q_C+ell v, ell>=0.                         (16)

This lemma permits both physical circle masks and zero individual
weights. We do not assume Q_C is in C in the two-corner mask.

If q<0, (16) gives v·m>0. Equations (15)–(16) then require

    q<=P_CD·m<=max_D(m·X)<=z<=q.

All comparisons would be equalities and ell=0. But P_CD would
be a rightmost point of D whose actual outward D-to-C normal
−v has negative m-component. This is impossible for a square:
at a unique rightmost vertex its two outward own-axis normals
have nonnegative m-components, and the same is true at the
endpoints or interior of a rightmost side. Every actual normal
at such a point belongs to that cone.

If C's two actual pair normals are parallel, its circle resultant
has positive n-component since all its circle points have n>1.
The complete local parallel-load classification in Section 1 of
SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md makes both pair normals
−n. Only this local classification is used, not that source's
whole-simple-cycle theorem. Keeping the two original applications,
the complete C origin moment says that their positive weighted
transverse mean is zero. The first coordinate is q and the second
is at most max_D(m·X)<=q. This is impossible if q<0.

We have proved q>=0 for every C mask and either force-line case.
If xi<0, however, (4)–(5) give

    q=−s eta+a e<−(1/3)(59/60)+(1/59)(1/20)<0.

Thus the actual channel is exactly North. In the original frame,

    n=(0,1), h=a<=epsilon<1/60, p_AB=(q,a), q>=0,
    B=[z,z+1] × [a,a+1], max_D X<=z<=q.              (17)

## 5. The full zero-mean endpoint q=0 is impossible

If q=0 in the nonparallel C2 case, (16) gives v·m=0, contradicting
nonparallelism. Therefore C is in the local parallel classification.
Its two original transverse means have positive weighted sum zero.
The first is zero and the second is at most z<=0, so

    p_CD=(0,a+1), max_D X=z=0.                       (18)

The local radial-terminal classification has two alternatives.
The D terminal has inner radius r<2/3 and cannot have its actual
minimum support a+1>1. Thus the entire actual C is the radial S unit

    C=[−1/2,1/2] × [d,d+1], a+1=d.                 (19)

At D the point (0,d) is simultaneously its rightmost point and
its support for the original D-to-C North normal. A genuinely
tilted square has different rightmost and uppermost vertices;
the own-axis signs at two perpendicular supports prove this
directly. Hence D is aligned, and (18) fixes the full unit as

    D=[−1,0] × [a,d].

The actual DA intersection is its positive-length bottom segment
with A, so the original D-to-A normal is South. Retain the full
original D3 equation. With its D-to-C North normal, that equation
forces the third normal, D-to-T, to be vertical. North would put T
in Y>=d, disjoint from A whose maximum height is a=d−1.
It must therefore be South.

Now take the full D origin moment. Its North CD application has
X=0. Both South applications have X<=0, so both nonnegative
moment terms must be zero separately. In particular the actual
DT point is (0,a). Its norm a<1/60 is below r, whereas every point
of a physical circle-touching unit has norm at least R−sqrt(2)=r.
This contradicts the actual T boundary contact.

This endpoint proof uses D3 without deleting DT and retains the
whole parallel C mask and both original side means. Hence

    q>0.                                           (20)

## 6. The real D leaf and the canonical choice force B--D contact

The actual leaf L imposes

    z+1<=r+a.                                      (21)

Indeed, if z+1>r+a, choose y=a+delta with delta>0 sufficiently
small and y<1/sqrt(2). The actual open horizontal L interval is
(r+y,R−y). Since z<=q<=r and z+1>r+y, it overlaps B's open
horizontal interval. This is an interior overlap of the same
two actual units.

D physically touches A, so its largest horizontal coordinate is
at least −s. Combining this with (17) and (21) gives

    −s<=max_D X<=z<=r+a−1=−s+a.                     (22)

In particular B's center has X=z+1/2>=1/2−s>0.

We now justify the literal physical C4 canonical transfer. The
positive subcycle is A--B--C--D--A. The winding/area argument
in Sections 1–2 of FOUR_CYCLE_LEAF_HOLE_EMPTY.md uses only the
four actual ring units and original aggregate applications.
It permits all shared-junction limits. A whole further unit
could be inside its bounded face only at the aligned-cross
equality. The actual unloaded B2 then has two opposite pair
forces and a common actual line. In that equality its two
applications are the endpoints of its inward side, so the
required point normals would be side axes. The original strict
vertex/vertex convention excludes that equality, exactly as
in Section 3 of the hole source.

This part of the argument uses neither an A3 nor a D2 equation.
It applies with the actual extra AT and DT edges still present.
Each of T, L and the other three units has connected open interior
avoiding the ring loop; if it entered its bounded face, that
whole unit would contradict the same area argument.

Suppose max_D X<z. At each height y strictly between a and a+1,
the A and C strands of the actual center/contact loop are absent.
The B strand crosses once, and the D strand crosses once: D's
vertical projection contains [a,a+1], its vertical width is at
most sqrt(2)<2, and its center is strictly inside that height
interval. Its two actual applications toward A and C are below
and above the interval respectively. These give precisely the
monotone-slice argument of Sections 3–4 of
FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md. Thus

    (max_D X,z) × (a,a+1)                           (23)

is in the empty bounded C4 face. Coincident applications are
impossible while the transverse gap is positive.

Translate only B a sufficiently small distance to the left.
Every newly occupied open point is in (23). A remains below
y=a, C above y=a+1, and D to the left; every other square
avoids (23). Therefore all nine nonoverlaps persist. Both the
old and new B center coordinates remain positive, by (22).
For this aligned square, reducing that coordinate strictly
reduces its maximum corner radius and its squared center norm.
This contradicts the initial secondary minimum.

No translation is made in the retained configuration. The
original canonical packing consequently has

    max_D X=z, B intersect D nonempty.              (24)

There is no new positive BD force or post-extraction normal choice.

## 7. A force-free height screen for the actual roof unit

The following local statement uses only the actual root chart (1),
the strict bounds (4)–(5), and R>sqrt(17)/2.

**Lemma 7.1.** Suppose a physical boundary unit T touches A with an
actual A-to-T normal West or strict southwest. Then

    max_T Y<−1/25.                                 (25)

Put gamma=1/25. First consider any unit having a rightmost vertex

    P=(−j,−v), 0<j<9/25, v>0,

and inward axes

    (−c,k), (−k,−c), c,k>=0, c²+k²=1.

Axis endpoints are allowed. Suppose its maximum height k−v is
at least −gamma. Then v<=k+gamma. All four actual vertices
have squared norm strictly below 17/4:

* At P, |X|<9/25 and |Y|<=26/25.
* At P+(−c,k), |X|<34/25 and −gamma<=Y<=1.
* At P+(−k,−c), |X|<34/25 and
  |Y|<=sqrt(2)+gamma<99/70+1/25.
* At the opposite vertex, |X|<9/25+99/70 and |Y|<=26/25.

The two closest reserves are exactly

    17/4−(34/25)²−(99/70+1/25)²=8742/30625,
    17/4−(9/25+99/70)²−(26/25)²=622/30625.          (26)

The first two comparisons have larger reserves. Thus such a unit
cannot physically touch the circle. We call this the rightmost-point
screen; it uses no force or mask assumption.

For an actual West AT normal, T has maximum X=−s. If T is tilted,
its actual unique rightmost port is (−s,y), −b<=y<=a. The
boundary-unit annulus says s²+y²>=r². Since r²−s²>1/16
and a<1/59, necessarily y<0. The rightmost-point screen applies
with j=s and proves (25). If T is aligned, it is

    [−s−1,−s] × [t,t+1].

Contact with A gives t<=a. If its top were at least −gamma,
then t>=−1−gamma. Thus all its corner coordinates satisfy
|X|<34/25 and |Y|<=26/25, putting every corner strictly inside
R. This excludes the aligned case too and retains every West
application mean.

For a strict southwest AT normal the original A port is
P_0=(−s,−b). If P_0 is a vertex of T and
max_T Y>=−gamma>P_0,Y, at least one inward side direction has positive
Y component. Its right-angle interior sector must avoid A's
open northeast quadrant at P_0. Orthogonality then forces the
two inward axes to point up-left and down-left. Thus P_0 is
a rightmost point and the same screen applies. Weak axis
endpoints are included in the preceding calculation.

If T owns this southwest contact normal, write that original unit
normal as (−k,−l), k,l>0, and retain its actual mean:

    T=P_0+[0,1](−k,−l)+[−rho,1−rho](l,−k),
    k²+l²=1, 0<=rho<=1.                            (27)

Its top is −b+rho k. If that is at least −gamma, then
rho k>=b−gamma. Its rightmost vertex is

    P_R=(−s+(1−rho)l,−b−(1−rho)k)=(−j,−v).

Since (1−rho)l<=1−rho k<=a+gamma,

    0<s−a−gamma<=j<=s<9/25, v>0;
    s−a−gamma>1223/4425.                           (28)

Its inward axes are (−l,k),(−k,−l). Again the rightmost-point
screen applies. Formula (27) includes every side endpoint.
The vertex and owned-side cases exhaust the physical support
of T, proving the complete lemma.

## 8. The actual D frame cannot contact the roof

The projection of D contains [a,a+1], and (24) fixes its actual
rightmost coordinate z.

If D is parallel to A and B, it is

    D=[z−1,z] × [a,a+1].

If z>−s, its original AD intersection has positive length on
A's top side, so AD is North, already excluded in Section 3.
If z=−s, AD is a point-only contact at A's upper-left vertex;
the original strict convention makes n_AD strictly northwest.
In the physical triangle A-D-T, an AT East or South axis has
negative dot product with n_AD, and a strict southeast AT is
at A's opposite vertex. These are impossible by the full
owned-axis and opposite-vertex triangle facts. Equation (7)
excludes every positive-Y alternative. Thus AT is West or
strict southwest. Lemma 7.1 puts T strictly below Y=−1/25,
whereas D lies above Y=a>0. The actual DT contact is impossible.

It remains that D is tilted. Its unique rightmost point and
the exact inward axes can be written

    R_D=(z,a+rho),
    D=R_D+[0,1](−c,−k)+[0,1](−k,c),
    c,k>0, c²+k²=1.

Projection containment gives

    1−c<=rho<=k, hence 0<rho<1.                     (29)

Set delta=z+s, so 0<=delta<=a by (22).
The real AD contact and disjoint interiors imply

    delta=c rho/k.                                (30)

Here is the complete endpoint justification. At height Y=a,
D's rightmost point is on R_D+[0,1](−c,−k), with coordinate
z−c rho/k. If rho<k, D extends below a. A value greater than
−s produces interior overlap immediately below a; a value
less than −s leaves every D point of height at most a strictly
left of A, hence prevents the AD contact. Its bottom is above
−b, since a+rho−k>=a+1−c−k>a−1=−b. Thus equality is forced.
If rho=k, the minimum D height is exactly a. A value greater
than −s would put the unique D bottom vertex in the relative
interior of A's top side: the original AD normal would be
North, already excluded. A value less than −s again prevents
contact. Equality is therefore forced at this endpoint as
well. The bound z<=−s+a<r ensures no right-hand A endpoint
is lost in these comparisons.

Consequently the actual AD application is A's upper-left
P=(−s,a). If rho<k, D owns the oblique supporting side and
the original A-to-D normal is (−k,c). If rho=k, the point-only
strict convention again gives a strictly northwest normal.
The complete physical ADT cover from the parallel case applies
unchanged, so AT is West or strict southwest and

    max_T Y<−1/25.                                 (31)

On the other hand, (29)–(30) give

    delta>=c(1−c)/k=ck/(1+c),
    ck<(1+c)/60<1/30,                              (32)

because delta<=a<1/60. If both c,k were at least 1/25, then
c² would lie in [1/625,624/625], and concavity of x(1−x)
would give

    c²k²>=624/390625>1/900.

The last strict reserve is 6839/14062500, contradicting (32).
Thus min(c,k)<1/25. The entire D unit satisfies

    min_D Y=a+rho−k>=a+1−c−k
            >a−min(c,k)>−1/25,                    (33)

where max(c,k)<1 supplies the strict inequality. Equations
(31) and (33) make T and D physically disjoint. This contradicts
their original positive DT edge and finishes the tilted frame.

## 9. Whole original-family conclusion and exact import scopes

Sections 1–8 exclude every actual radius, channel direction,
bypass side, original C2 force-line/mask alternative, zero mean,
and D frame in the original house-hub TC family with a genuine
D leaf. The contradiction is at the admissible original canonical
counterexample. It does not classify noncanonical equality packings.
The original fine family is M6.B5L.HOUSE.HUB.LTC.D.

The three completion squares have not been discarded. They are
kept throughout the local geometry, and the only putative motion
is justified on all nine units by the complete original C4
winding/empty-hole argument. No actual force is changed, no
original shared mean is reselected, and no physical two-corner
mask is changed into a unique-corner mask.

The literal imports read for this proof are:

| Source | Scope used | SHA256 |
| --- | --- | --- |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | Original house graph and hub-TC load row | 7ba98ef149c1faff4ef4baeaf0b0305a38cf1153f883a3fe4bfa92087d33622d |
| NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md | Same-nine R>2 | 6e2279b627754fe6ba3c7d9a9779308ee8133223b09f5374803797cb41f3d96c |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | Genuine radial D leaf and clear root | 6154eee2ab1114d063b0dbd1a2800c3522cbb1b46ec44a258c1c89d8ffb9e975 |
| RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md | Sections 1–2 only: D root side-interior chart | f3a3e4c9d82e3fa0b8fef7f7d385cf08fce88c39543bf97a74cb479d995037f9 |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md | Section 1 contained-unit bound and Section 2 physical opposite-vertex fact only | 6f3459eaf4ca425ee2001ddb27e1ba7a1b5eb0003548498f48c610776554d3bb |
| UNIT_BYPASS_NORMAL_CHANNEL.md | Entire width-one and transverse-separation theorem | d6008ceb18b2c8921c1f3711e6babfea3a01761487352ef4dca60579a83353b8 |
| D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md | Entire force-free roof screen | 79ddc3bc94613ba34b30ea3b1e4176a14d644b08887020cbc38f9ef9d785d8a8 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | Full physical owned-axis and support-span facts | ee865704904a8b2a5cab7649bdfd928008c253631abf1eb346d4950411c3afac |
| FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md | Lemma 1.1 local proper C2 only | 7d0c4092ba133a832cf963f329b1c3a6442a3260576f16319293835b39e6d282 |
| SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md | Section 1 local parallel loaded2 radial classification only | cd2a8c765c181ac803d8ee1c8672d1a8ceea3591248cbca449ef3653b4be6ebe |
| FOUR_CYCLE_LEAF_HOLE_EMPTY.md | Sections 1–3 physical winding, area and true unloaded2 equality exit only | c22f793bcffc3465328baeaa2db53e88c213d3353da225f57e774b593a7fc655 |
| FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md | Sections 1–4 compactness and actual slice/translation only | 9faa9327d6b6d75f43d0b62b8e83294b2e5a08ac45f85edc835aa72fd59c0c89 |

In particular no whole isolated C4, simple-cycle, true-A3 root
or true-D2 tip theorem is applied to the original house hubs.
The new strip bound and roof height screen are complete physical
proofs within this source. All remaining algebra is hand-rational.
No pose search, numerical premise, coefficient certificate, Lean
compilation, CI, workflow, remote write or shared metadata change
is used. Full independent and root reviews are requested.
