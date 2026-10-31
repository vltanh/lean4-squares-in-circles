# Every occupied one-proper diagonal channel contains the origin strictly

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed hand theorem and joint injection corollaries, frozen for full independent review.** The conclusion concerns the actual original transmitting square, not an auxiliary comparison square. The opposite endpoint may have arbitrary genuine degree.

Put

    Q=1105/256, sigma=1/sqrt(2), A=2+sqrt(2).

Use the full actual one-proper setting of ONE_PROPER_DIAGONAL_CHANNEL_OUTER_POCKET_CAPACITY_ONE.md at83f60e7c. Thus 2<=R<=sqrt(Q); H is the original unloaded degree-two diagonal transmitter between physically boundary endpoints X,Y; both actual endpoint applications are relative-side-interior points; and only Y has the stated genuine proper concurrence on its original channel-force line. All other original forces, torques, means, physical circle corners and individual coefficients remain.

After the common reflection making the unchanged channel height h positive, use the complete chart of that source. Its actual original upper exterior pocket is defined by the same fixed physical spokes and winding convention, with no choice of a new stress.

**Theorem.** If that whole actual pocket contains at least one additional actual unit square, then

    O belongs to int(H),

and every actual vertex of H has norm strictly greater than3/35, hence strictly greater than7/100.

In particular dist(O,H)=0 exactly. This is stronger than a small positive distance estimate and is retained with its exact interior meaning in the corollaries below.

The theorem covers both possible signs of the X center, every physical endpoint circle mask, all individual zero circle weights, the closed radius R=2, and every original mean in the declared relative-side-interior diagonal interface. It imposes no degree-two or proper-concurrence hypothesis at X.

## 1. Exact complete one-proper chart and the two whole geometric exits

The complete entry83f60 gives

    a+c=A, a^2+b^2=c^2+d^2=R^2,
    11/8<a,c<81/40, b,d>=1/2,

    P_X=(1-a,h), P_Y=(c-1,h),
    c_H=(delta,h), delta=(c-a)/2=A/2-a,

    H={ (x,y): |x-delta|+|y-h|<=sigma }, h>0.           (1)

Y always has the nonnegative-center chart

    Y=[c-1,c] times [d-1,d],
    d-1<h<d.

If d>1/2, its exact original unique-corner properness gives

    h>=d(1-1/c).                                       (2)

At d=1/2 all original physical circle coefficients are retained; no fixed-corner inequality is inferred from a radial concurrence.

The two actual X alternatives are exhaustive:

    nonnegative center:
        X=[-a,1-a] times [b-1,b], b-1<h<b;

    negative center:
        X=[-a,1-a] times [-b,1-b], 1/2<b<1,
        0<h<1-b.

The full negative-center alternative has an empty actual pocket by ONE_PROPER_DIAGONAL_NEGATIVE_ENDPOINT_POCKET_EMPTY.md atff5ac694. That result uses only the genuine proper Y; it retains arbitrary degree at X and the actual original spokes. It does not assume a whole extra lies above h.

In the nonnegative-center alternative, the entire domain a>=c has an empty actual pocket by ONE_PROPER_DIAGONAL_NONNEGATIVE_ENDPOINT_ORDERED_COORDINATES_POCKET_EMPTY.md atf10e14e9. Its radial-spoke section proves winding agreement at every extra-interior point before transferring any whole-cap inclusion, and its reflected vertical-row proof never assigns properness to X.

Therefore an occupied pocket must satisfy

    X=[-a,1-a] times [b-1,b],
    b-1<h<b,
    a<c, delta>0.                                     (3)

These are deductions about the same original bodies. They are not a relabeling which might change which endpoint is genuinely proper.

## 2. A geometric empty-pocket lemma with two numerical height inequalities

We need one further exact consequence of the older full geometric proof. The lemma is stated explicitly to avoid importing its original simple-cycle force assumptions.

### 2.1. Pure geometric statement

Suppose the actual contained endpoint squares have

    X=[-a,1-a] times [b-1,b],
    Y=[c-1,c] times [d-1,d],

    a+c=A, a^2+b^2=c^2+d^2=R^2,
    2<=R<=sqrt(Q),
    11/8<a,c<81/40, b,d>=1/2,

    b-1<h<b, d-1<h<d, h>0,

with H the same actual diamond(1). Suppose additionally that the two scalar inequalities

    h>=b(1-1/a), h>=d(1-1/c)                          (4)

hold. They are numerical hypotheses; the lemma does not assert how either was obtained from forces.

Then the whole actual upper exterior pocket is empty, for either original physical endpoint-circle choice.

### 2.2. Height and physical endpoints

Let x=min(a,c), and let y denote the corresponding vertical farthest-corner magnitude. Since x<=A/2 and R>=2,

    y^2>=4-A^2/4=5/2-sqrt(2)>1.

The relevant inequality in(4) thus supplies

    h>=y(1-1/x).

The complete two-interval scalar proof in Section2 of DIAGONAL_CHANNEL_EXTERIOR_CAPACITY_ONE.md applies. It uses only this scalar inequality, the exact circle equalities, the weak other height>=1/2, and 2<=R<=sqrt(Q). It yields

    h>43/100.                                         (5)

For specificity, on 11/8<=x<=3/2 its lower square is

    (A^2-2Ax+1/4)(x-1)^2/x^2,

whose derivative sign changes at most from positive to negative. Its two endpoint reserves above(43/100)^2 are1271/1210000 and41/8910000. On 3/2<=x<=A/2 use

    (4-x^2)(x-1)^2/x^2;

again its only possible interior critical point is a maximum. The two endpoint lower reserves are859/90000 and57/70000. These are complete continuous inequalities, not endpoint tests without a monotonicity argument.

If one physical endpoint is radial, its vertical magnitude is1/2. The inequalities(4) remain scalar statements and do not place its full concurrence inside the unit. Neither any circle corner nor any individual zero coefficient is discarded.

### 2.3. Whole-extra winding and whole-cap inclusions for both possible radial sides

When both endpoints are unique, their actual circle corners(-a,b),(c,d) lie strictly above h. The original occupied crosscut through the two channel applications and its upper circle arc therefore have their entire boundary in

    y>=h, -a<=x<=c.

Original center/contact paths can be replaced inside the actual X,H,Y union with no change of winding at any extra-interior point, as proved in83f60. Every whole extra thus satisfies those same two closed inclusions.

If X is physically radial and the unchanged original circle choice is its lower corner, apply the complete chord argument of Section2 of f10e14e9. Here are the parts of that argument which matter independently of endpoint ordering.

Its outer side is the chord x=-a, -1/2<=y<=1/2, with a=sqrt(R^2-1/4). The outer circular segment has horizontal width

    R-a=1/[4(R+a)]<1.

The open interior of any contained unit disjoint from X avoids closed X. If it had one point strictly beyond that chord and another strictly on its inner side, their open-interior segment would meet the actual chord in closed X, impossible. A point directly on the chord is likewise forbidden. Thus even one extra-interior point in the outer circular segment would force the entire extra into its closure; its width<1 then contradicts the minimum horizontal width of a unit square.

Consequently every point of the extra's open interior avoids that entire circular segment. The exact difference between the lower-corner original loop and the upper-corner auxiliary loop is the sum of the triangle inside X and that outer circular segment, with the chord cancelling as an oriented chain. Every extra-interior point has zero winding about both difference regions. Its winding about the original and auxiliary upper loops is therefore identical.

The auxiliary upper loop lies in the two stated halfplanes, so every point of the unchanged extra, after taking closure, satisfies the whole-cap inclusions. No original spoke or force is changed; the auxiliary loop is used only to locate the original extra.

If Y is the radial endpoint, reflect this entire geometric chord argument horizontally. Its actual outer side is x=c, -1/2<=y<=1/2. The circular segment is on x>=c, with the same width<1. The same open-interior segment argument, not an assertion about extras already wholly in that segment, proves avoidance by every extra-interior point. The exact triangle-plus-segment winding identity gives the identical whole-cap conclusion.

Both endpoints cannot be radial in this domain, since that would give

    a+c=2sqrt(R^2-1/4)>=sqrt(15)>A,

contrary to a+c=A. The final strict comparison follows from A^2=6+4sqrt(2)<12<15. Thus the unique/radial alternatives just listed exhaust all physical masks.

### 2.4. Exact scope of the complete older geometric proof

The entire geometric proof of FOUR_C6_DIAGONAL_CHANNEL_CAP_EMPTY.md now applies to the displayed geometry, scalar inequalities(4), height(5), and the whole-cap inclusions proved in Section2.3.

Its original simple-cycle hypotheses are used only to establish that starting geometry. After its Section1, there is no reference to an original third body, force polygon, degree, load value or endpoint concurrence beyond the two numerical inequalities already supplied.

More explicitly:

* In the balanced family a>b,c>d, Section2 imports the complete SAT proof of SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md. That proof uses the common-radius equalities, both strict original mean intervals, the two numerical inequalities(4), h>2/5 and the actual whole cap/slab. Its four exact polynomial identities cover complete closed parameter rectangles, including every weak height endpoint1/2. They are geometric inequalities, not finite poses.
* In the asymmetric family, exactly one endpoint is tall. Sections3--8 derive the short/tall bounds, cover every H/E and endpoint/E separating side axis, and exclude every horizontal, northeast and vertical row. Their input height is(5), and their stronger high-radius height follows from the strict actual mean at the tall endpoint. The short vertical-row estimate uses h greater than the tall endpoint's vertical magnitude minus one. No force equation is used.
* The physical radial endpoints are checked directly in Section2 of FOUR_C6. In the balanced scalar comparisons, the factor b^2-1/4 is allowed to vanish and is never divided by. Every original mean remains strict where required. The asymmetric proof already uses weak vertical lower bound1/2.

All complete mathematical sections of both sources have been read, including the four whole-domain identities. Thus this is a direct application of their geometric arguments at their full actual premises, not an appeal to a simple-cycle theorem after silently removing a hypothesis.

They exclude every possible separator for a whole extra. This proves the geometric lemma of Section2.1.

## 3. Occupancy forces the exact failure of the unavailable X numerical inequality

Return to the actual occupied one-proper channel(3). Suppose, for contradiction, that

    h>=b(1-1/a).                                       (6)

Because a<c, we have a<A/2 and

    b^2=R^2-a^2>4-A^2/4=5/2-sqrt(2)>1.               (7)

The same pure height proof used in Section2.2 applies directly to(6) at a. It gives h>43/100 before any numerical inequality is assigned to a physical radial Y.

If d>1/2, the genuine proper Y already supplies the second inequality(2). If d=1/2, its numerical right side instead satisfies

    d(1-1/c)
      <(1/2)(1-40/81)
       =41/162<43/100<h.                              (8)

This uses c<81/40 and no fixed-corner statement about the original radial resultant. The strict rational gap is

    43/100-41/162=1433/8100>0.

Thus both scalar hypotheses(4) hold in every physical Y mask. The geometric empty-pocket lemma now contradicts occupancy. Therefore every occupied survivor obeys

    h<b(1-1/a).                                       (9)

In particular X cannot be tall. If b>=a, its actual original mean would give

    h>b-1>=b(1-1/a),

since the difference between the latter two quantities is b/a-1>=0. This contradicts(9), including the equality b=a.

Consequently the actual occupied channel satisfies the full strict residual geometry

    a<c, a>b, c>d,                                    (10)
    0<h<b(a-1)/a<a-1.

The inequality c>d follows directly from a<c and the common-radius equality b>d: c>a>b>d. Every force, mask and actual application is still the original one.

This is an exhaustive geometric deduction. Neither b=a, a=c nor h=b(1-1/a) is omitted: each equality belongs to an already excluded alternative.

## 4. The actual transmitting square contains O strictly

Equation(10) and delta=A/2-a=1+sigma-a give

    delta>0, h>0,

    delta+h
      <1+sigma-a+(a-1)
       =sigma.                                        (11)

By the exact diamond equation(1), the origin therefore satisfies its strict interior inequality:

    |0-delta|+|0-h|=delta+h<sigma.

Thus O belongs to int(H). This proves the exact zero-distance conclusion

    dist(O,H)=0.                                      (12)

The comparison uses only unchanged coordinates of the actual H. It does not produce or insert an auxiliary origin-centered square.

## 5. Every actual H vertex stays more than3/35 from O

The two actual horizontal vertices are the original ports

    P_X=(1-a,h), P_Y=(c-1,h).

Their norms exceed a-1 and c-1, respectively, and both exceed3/8 by11/8<a,c.

The actual upper vertex is(delta,h+sigma). Its vertical coordinate alone is greater than sigma>7/10>3/35.

For the lower vertex(delta,h-sigma), use the complete balanced residual(10). Since a>b and a^2+b^2=R^2,

    b<R/sqrt(2)<=sqrt(Q/2)<3/2.                       (13)

The final squared reserve is

    9/4-Q/2=47/512>0.

Also a<A/2 implies

    (a-1)/a < ((A/2)-1)/(A/2)=sqrt(2)-1.              (14)

All quantities multiplied here are positive. Equations(9), (13), and(14) give

    h<(3/2)(sqrt(2)-1).

Consequently

    sigma-h
      >sigma-(3/2)(sqrt(2)-1)
       =3/2-sqrt(2)
       >3/35.                                         (15)

The last strict comparison uses sqrt(2)<99/70. In particular h<sigma, so the lower vertex actually has negative height; its norm is at least sigma-h and is strictly greater than3/35.

All four actual vertices therefore have norm>3/35. The useful comparison to the prior side-channel margin is strict:

    3/35-7/100=11/700>0.                              (16)

This proves the full theorem.

## 6. A broad mixed-distance three-unit obstruction, with exact interior semantics

Here is a radius-free consequence useful for actual completion allocations.

Let three unit squares H,F,E have pairwise disjoint open interiors. Suppose

    O belongs to int(H),
    dist(O,F)<=1/20,
    dist(O,E)<=1/40,

and every vertex of all three units has norm strictly greater than3/50. Then such three units cannot exist.

This differs from the earlier equal-distance near-three lemma: the threshold for F is1/20, and H has exact interior origin containment. We prove the complete claim rather than applying that earlier lemma outside its stated delta<d/2 scope.

Put d_*=3/50 and inspect the same circle |z|=d_*.

### 6.1. A unit at distance at most delta<d_* occupies angular measure at least2acos(delta/d_*)

The complete own-frame argument of Section4 of SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md gives the following stronger per-unit statement.

If O is outside a unit S with distance a<=delta<d_* and all vertices outside D_(d_*), its nearest point cannot be a vertex. In an actual orthonormal own frame,

    S=[a,a+1] times [b,b+1],
    0<a<=delta, b<0<b+1.

The two actual nearest-face vertices have norm>d_*, so

    -b>sqrt(d_*^2-a^2),
    b+1>sqrt(d_*^2-a^2).

Every circle point with first coordinate>a lies strictly in S. The far side is irrelevant because d_*<a+1. This is an open arc of angular length

    2acos(a/d_*)>=2acos(delta/d_*).

If O lies on the boundary, it lies in a relative side interior, and the same argument with a=0 gives an open semicircle. That length is larger than2acos(delta/d_*) for positive delta.

If O lies inside, the next subsection gives occupied angular measure greater than pi, also larger than2acos(delta/d_*) for positive delta.

Thus the asserted lower bound holds for all origin locations and for closed distance thresholds. The lower bound need not be strict in the outside case, and no false strictness is used below.

### 6.2. Exact origin containment gives occupied angular measure greater than pi

For the actual H containing O strictly, every supporting-face distance from O is positive. Since2d_*<1, at most two of its four face lines can cut the test circle; if two do, they are adjacent.

A single cutting face at positive distance t removes angular length2acos(t/d_*)<pi. If two adjacent cutting faces have positive distances t,u<d_*, their common actual vertex lies outside D_(d_*), so

    t^2+u^2>d_*^2.

It follows that

    acos(t/d_*)+acos(u/d_*)<pi/2.

The two outward halfplanes remove angular measure at most twice that sum, hence strictly less than pi. Faces not cutting the circle remove nothing, and tangent faces remove zero angular measure. Therefore

    angular measure of int(H) on |z|=d_* is >pi.      (17)

This is an angular-measure assertion, which is all the disjointness proof needs. It does not silently identify an outside nearest-face arc with an inside-origin arc or assume a particular connected component.

### 6.3. The exact sum exceeds the full circle

Apply Section6.1 with delta_F=1/20 and delta_E=1/40. Their ratios to d_* are5/6 and5/12. Thus F and E occupy angular measures at least

    2acos(5/6), 2acos(5/12),

respectively.

The two acute half-angles satisfy

    acos(5/6)+acos(5/12)>pi/2,

because

    (5/6)^2+(5/12)^2=125/144<1,
    1-125/144=19/144>0.                              (18)

Indeed sin(acos(5/12))>5/6 follows directly from(18), with both sides positive. Hence acos(5/12)>pi/2-acos(5/6).

Together with(17), the three occupied angular measures sum to strictly more than2pi. Pairwise disjoint open interiors give pairwise disjoint measurable portions of this same circle, whose total angular measure cannot exceed2pi. This contradiction proves the mixed-distance obstruction.

No assumption about a common containing radius or a contact graph is required for this radius-free lemma.

## 7. Complete conditional injection consequences for actual channels

### 7.1. At most one occupied one-proper diagonal transmitter can occur

Suppose two different actual unloaded diagonal transmitters both satisfy the displayed one-proper endpoint premises and both have occupied original outer pockets. The theorem puts O in the open interior of each actual transmitter. This contradicts pairwise interior disjointness immediately.

Thus in any packing there is at most one such occupied diagonal channel. No distance threshold or completion graph is needed for this consequence.

### 7.2. An occupied diagonal channel and an actual near central extra leave no additional near unit

Let H be an occupied one-proper diagonal transmitter from this theorem. Let E be any actual distinct unit with

    dist(O,E)<=1/40

and all vertices of E outside D_(3/50). If another actual distinct unit F has distance at most1/20 from O and all vertices outside D_(3/50), then Section6 contradicts their actual pairwise disjointness.

In particular an actual occupied side-channel transmitter, with the independently proved distance<1/40 and vertex margin>7/100, may be used as F. The side-channel theorem's genuine hypotheses must still be checked in its caller; this corollary does not create a missing properness, load or center-sign premise for that other channel.

This result strengthens the usual common1/40 near-three injection: the extra unit F is permitted distance1/20 because H contains O strictly.

### 7.3. Actual enclosed central units have the required separate bounds

For an actual unit E lying in a bounded complementary region enclosed by a finite collection of actual contained units, the full degree-free geometric part of C7_INNER_SIDE_CORNER_RESTRICTIONS.md, with its CENTER_COVER_PIERCING.md predecessor, supplies

    every absolute own center coordinate of E
        <1/2+121/7200,

    every vertex norm of E>19/300>3/50.

The first bound gives

    dist(O,E)<sqrt(2)*121/7200
              <(10/7)*121/7200
               =121/5040<1/40.                       (19)

The exact final reserve is

    1/40-121/5040=1/1008>0.

These are geometric conclusions for the actual finitely enclosed unit. Their proof does not require a C7 force polygon. It must still be true in the caller that the unit is in the bounded enclosed region; no exterior extra is reclassified as central here.

Therefore the preceding injection applies directly whenever such a genuine central E and another genuine near unit F occur alongside the occupied diagonal H. This is a conditional complete obstruction to those actual allocations, not an assertion that every original completion has already been assigned to them.

## 8. Literal original D02 interfaces and remaining scope

For the original positive rim01,12,23,34,45,50 plus chord02, with physical loaded set0134, the channel is

    X=0 -- H=5 -- Y=4.

The endpoint degrees are genuinely three and two. Y's other original neighbor3 is physically boundary, which supplies the genuine proper Y premise as fully checked in83f60. X retains all three original forces and its full torque and circle system.

For the physical loaded set0135, the channel is

    X=3 -- H=4 -- Y=5.

Y's other original neighbor0 is physically boundary. X's other neighbor2 is not assumed physically boundary and no proper concurrence is imposed at X. Again83f60 gives the exact original upper-pocket join.

In either interface, every occupied diagonal channel now gives actual O in int(H) and all H vertices>3/35. If an actual central extra E and a genuine near hub or other channel F satisfy Section7, their original three-unit allocation is impossible.

All original positive edges, the chord, every original side mean, all six core units and all three completion squares remain. No whole original D02 load row is claimed closed until its entire original allocation and every other local interface have been joined.

## 9. Exact complete input manifest

| Complete source | SHA256 | Operative scope |
| --- | --- | --- |
| ONE_PROPER_DIAGONAL_CHANNEL_OUTER_POCKET_CAPACITY_ONE.md | 83f60e7c35fdd4c517d27db4d2755ea5e14a4bab2b876c52cdfce7a85d286889 | Complete actual one-proper chart, physical masks, original-spoke upper-pocket join and literal genuine degrees |
| ONE_PROPER_DIAGONAL_NEGATIVE_ENDPOINT_POCKET_EMPTY.md | ff5ac694d57a78a64b77f0cfe40e1ac5c5d544a96d9e086d190319ce992db08a | Whole negative-center X exit with arbitrary genuine X degree |
| ONE_PROPER_DIAGONAL_NONNEGATIVE_ENDPOINT_ORDERED_COORDINATES_POCKET_EMPTY.md | f10e14e9906d0d3b13c7f679141ec74bacc99ce7ee7cf30f827e264ca096c629 | Whole a>=c positive-center exit and exact radial-chord winding argument at every extra-interior point |
| DIAGONAL_CHANNEL_EXTERIOR_CAPACITY_ONE.md | 46f8be67b5c447a78f12cefb3f96474973ead5d48d4e65b346a1c77bdd8fee02 | Pure one-coordinate height comparison at a stated numerical inequality, not its simple-cycle force entry |
| FOUR_C6_DIAGONAL_CHANNEL_CAP_EMPTY.md | 454b1c9cabb614d8c2a16a2ca297d6bbbadcd94340423ac5c93b72e05a092b5d | Complete geometric empty-pocket proof after its displayed endpoint, numerical-height and whole-cap premises |
| SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md | c5dec5c8cb78f83715624b59a1401748f07616acf44f9c567ab88da778c3ebbe | Full balanced geometric proof and all four exact continuous identities imported by FOUR_C6 |
| SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md | 0fa62f59c2b228d235a3e1539f9bbf8c3e53f7f128052064b8157819dcf06b4c | Complete radius-free per-unit circle-measure proof, explicitly extended here to mixed closed distance thresholds |
| C7_INNER_SIDE_CORNER_RESTRICTIONS.md | b9329b7a81b57cd0fef4b62c69c26388face02b8b985c79624aa285416284733 | Actual finite-enclosure own-center and vertex bounds for a separately established central unit |
| CENTER_COVER_PIERCING.md | 029d7142b140e8ffe10e5beebf54223b04f7e0722605b9a6b9098a914ce41a29 | Complete geometric finite-enclosure predecessor for the central-unit bound |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Unchanged original degree, force, torque, actual mean and physical-mask conventions |

All complete mathematical sources have been read. The two newly written empty-pocket sources have their own independent-review requirements; this manuscript does not assign itself independent review credit for those authored inputs. The broad origin-containment theorem and its mixed-distance corollary also require a separate full review before adoption.

The proof's new content is the exhaustive actual occupied-channel deduction(9)--(12), the uniform actual vertex margin(15), and the radius-free mixed-distance circle-measure obstruction. Its comparisons retain every strict or closed endpoint of their declared domains.

Exact rational arithmetic checks all displayed reserves. There is no numerical pose, parameter grid or angle enumeration. No actual unit, normal, mean, force or physical circle coefficient is modified. No Lean compilation, CI/workflow run, remote write or shared-ledger change is used.

