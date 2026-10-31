# One proper diagonal endpoint suffices when it has the smaller horizontal coordinate

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed geometric hand theorem, frozen for full independent review.** This proves empty exterior pocket for the entire nonnegative-center opposite-endpoint alternative with a>=c in the actual one-proper diagonal chart. The endpoint X may have arbitrary genuine degree. No proper concurrence is asserted at X.

Put

    Q=1105/256, sigma=1/sqrt(2), A=2+sqrt(2).

Retain the complete actual setting, original applications, full force and torque equations, individual physical circle coefficients, and fixed physical exterior spokes of ONE_PROPER_DIAGONAL_CHANNEL_OUTER_POCKET_CAPACITY_ONE.md at83f60e7c.

The actual unloaded degree-two diagonal transmitter is H. Only Y is assumed to have the genuine proper positive-ray concurrence stated there. Reflect the entire actual configuration once, as in that source, to make the unchanged port height positive.

In the nonnegative-center X alternative, the chart is

    X=[-a,1-a] times [b-1,b],
    Y=[c-1,c] times [d-1,d],

    a+c=A, a^2+b^2=c^2+d^2=R^2,
    2<=R<=sqrt(Q),
    11/8<a,c<81/40, b,d>=1/2,

    P_X=(1-a,h), P_Y=(c-1,h),
    b-1<h<b, d-1<h<d, h>0,

    c_H=(delta,h), delta=(c-a)/2,
    H={ (x,y): |x-delta|+|y-h|<=sigma }.               (1)

Assume

    a>=c.                                             (2)

Thus the actual proper endpoint Y has the smaller or equal horizontal farthest-corner coordinate.

Let Omega be the upper original occupied channel region defined in83f60 using the unchanged chosen physical circle corners and original exterior spokes.

**Theorem.** No whole additional actual unit square can occupy Omega with open interior disjoint from X,H,Y.

The theorem includes a=c, the closed radius R=2, a physical radial X with either originally selected physical circle corner, every individual zero circle coefficient, all original side-interior applications and their complete allowed means. Section2 proves the needed winding statement for the full original-spoke choice; it does not merely assert that an extra cannot be wholly inside a small cap.

## 1. All required height bounds use only the actual proper Y

Because c<=A/2, the exact circle equality gives

    d^2=R^2-c^2>=4-A^2/4=5/2-sqrt(2)>1.               (3)

In particular Y is physically unique, and the unchanged genuine proper concurrence at Y gives exactly

    h>=d(1-1/c).                                       (4)

This is the original Y port inequality. No X concurrence or force polygon is introduced.

The pure height argument in Section2 of DIAGONAL_CHANNEL_EXTERIOR_CAPACITY_ONE.md now applies at c, rather than requiring both endpoints to be proper. For clarity, the complete two-interval proof is printed here.

For 11/8<=c<=3/2, the actual b>=1/2 gives

    d^2=R^2-c^2>=A^2-2Ac+1/4,

and hence

    h^2>=G(c)=(A^2-2Ac+1/4)(c-1)^2/c^2.

The exact derivative is

    G'(c)=2(c-1)/c^3 [A^2+1/4-Ac(c+1)].

The bracket strictly decreases, so a derivative sign change can only be from positive to negative. The minimum on the whole closed interval is therefore at an endpoint. Their strict lower estimates are

    G(11/8)>45/242
               =(43/100)^2+1271/1210000,

    G(3/2)>659/3564
               =(43/100)^2+41/8910000.

These use sqrt(2)>7/5 and sqrt(2)>140/99, respectively. The exact second squared reserve is2/9801.

For 3/2<=c<=A/2, R>=2 gives

    h^2>=F(c)=(4-c^2)(c-1)^2/c^2,

    F'(c)=2(c-1)(4-c^3)/c^3.

Again the only possible interior critical point is a maximum. At the endpoints,

    F(3/2)=7/36=(43/100)^2+859/90000,

    F(A/2)=23/2-8sqrt(2)
             >13/70
              =(43/100)^2+57/70000,

where the last strict comparison uses sqrt(2)<99/70. Thus

    h>43/100>2/5.                                     (5)

The original Y height is always too large to support a whole extra above it. More precisely, set

    T=sqrt(R^2-1/4), D=T-1, M=T-1/2.                  (6)

Every contained unit center has norm at most M, and M<91/60. From c<=A/2,

    d^2-D^2
      >=2T-3/4-A^2/4
       =2T-9/4-sqrt(2)
      >=sqrt(15)-9/4-sqrt(2)>0.                      (7)

The final strict inequality follows from sqrt(15)>15/4 and sqrt(2)<3/2. Since d,D are positive, d>D. Therefore a unit whose whole lower support is at least d would have center height at least d+1/2>M, impossible. This fact will replace every unavailable reflected use of X properness.

## 2. The unchanged physical spokes give whole-cap inclusions, including radial X

We prove, for every whole extra E in the actual original Omega,

    E subset { y>=h },
    E subset { -a<=x<=c }.                             (8)

This argument is about every point of the unchanged whole extra. It keeps all physical masks and the original spoke choice.

### 2.1. A unique X needs no change of geometric crosscut

If b>1/2, X has its unique actual circle corner z_X=(-a,b). Equation(3) makes Y unique with z_Y=(c,d). Both circle heights exceed the original h by the strict mean intervals.

The piecewise-linear occupied crosscut

    z_X -- P_X -- P_Y -- z_Y

and the upper containing-circle arc form the same upper region as the original exterior spokes: replacing the original center/contact paths inside the actual X,H,Y union changes no winding at an extra-interior point. This exact original-spoke fact is already proved in83f60.

The entire displayed boundary lies in y>=h and in the horizontal slab [-a,c]. For the upper circle arc, both endpoint heights are positive, and that arc has no horizontal excursion beyond either endpoint. Its minimum height is at an endpoint. The straight strands lie in the same closed convex halfplanes.

The bounded Jordan region is consequently in those halfplanes as well. For example any point outside one has a ray to infinity in its strict outside halfplane, disjoint from the whole loop. Taking the closure includes every boundary-contact limit of E. This proves(8).

### 2.2. Every whole extra avoids the small radial outer-face cap

Now b=1/2. Then

    a=T=sqrt(R^2-1/4),
    z_+=(-a,1/2), z_-=(-a,-1/2)

are the two actual physical circle corners of X. Their individual original weights may be arbitrary nonnegative values. Y is still unique.

The chord

    C_X={(-a,t): -1/2<=t<=1/2}

is the entire actual outer side of X. Put

    K_X=D_R intersection {x<=-a}.

Its horizontal width is R-a, and

    0<R-a=1/[4(R+a)]<1.                              (9)

We claim that the open interior of any actual unit E contained in D_R and interior-disjoint from X cannot meet the open cap x<-a.

First, int(E) is disjoint from the closed square X: an open neighborhood of any closed X point contains points of int(X), so an intersection with int(E) would produce interior overlap. Every point of int(E) also belongs to int(D_R), since an open disk centered at a boundary point of the strictly convex containing disk cannot lie in D_R.

If int(E) had a point with x<-a and another point with x>-a, their segment would lie in int(E) by convexity. It crosses the line x=-a at an interior-disk point of the chord C_X. That point lies in closed X, contradicting the preceding observation. An int(E) point on the line x=-a is itself forbidden for exactly the same reason.

Thus the existence of even one int(E) point in x<-a forces every int(E) point to have x<-a. Taking closures would put the entire E in K_X. But every unit square has horizontal width at least one, whereas K_X has width R-a<1 by(9). This is impossible.

We have proved the stronger whole-unit conclusion

    E subset {x>=-a}, int(E) subset {x>-a}             (10)

for every actual unit E disjoint from radial X, independently of which original physical circle corner was chosen. In particular no whole extra can straddle the chord or pass around its endpoint inside the disk. The convex segment argument above rules out straddling before the width argument is used.

### 2.3. The exact winding comparison for the lower original physical spoke

If the unchanged original X circle choice is z_+, the geometric crosscut in Section2.1 applies directly. Its endpoint height1/2 is strictly above h.

Suppose the original choice is instead z_-. Compare its actual upper loop with the auxiliary upper loop using z_+ and the same P_X,P_Y,z_Y. This is only a geometric comparison for the same fixed E. No original force, circle weight or actual certificate spoke is replaced.

The difference of the two closed chains consists of:

1. the triangle with vertices P_X,z_-,z_+, which lies wholly in the actual closed X; and
2. the small circular segment K_X bounded by C_X and the left containing-circle arc from z_+ to z_-.

This follows by inserting the chord C_X: the two P_X-to-corner strands and that chord form exactly the triangle, and the difference of the two upper outer arcs is exactly the left arc bounding K_X. It is an equality of oriented closed chains, with opposite chord orientations cancelling.

Every point of int(E) avoids both closed X and K_X by Section2.2. Its winding number about each difference chain is therefore zero: both bounded difference regions lie in those explicitly avoided closed sets. The original and auxiliary upper loops have identical winding at every point of int(E).

By the original occupancy premise, those winding numbers select the bounded upper region. Therefore every point of int(E) lies in the auxiliary upper region as well. The auxiliary loop has its entire boundary in the two halfplanes of(8), exactly as in Section2.1, so all of int(E), and then its closure E, satisfies(8).

This completes the proof for both physical X corner choices, including a zero original coefficient at either corner. It does not infer winding from the fact that E cannot be wholly contained in a narrow segment; it proves that no extra-interior point enters the segment and then compares the two exact closed chains.

## 3. The geometric separating-axis cover requires no endpoint force equation

Suppose E is a whole extra satisfying(8). The full separating-axis cover in Section4 of FOUR_C6_DIAGONAL_CHANNEL_CAP_EMPTY.md applies to the unchanged H and E.

Here are its complete premise joins.

Any H-to-E separator with nonpositive vertical component and negative horizontal component puts all of E to the left of P_X=(1-a,h). By(8) and minimum unit horizontal width, that would force E to be axis-aligned with horizontal interval[-a,1-a]. The unchanged h>b-1 and avoidance of X then put its bottom at least at b. Its upper-left corner has squared norm at least a^2+(b+1)^2>R^2. Reflection proves the corresponding right-hand case; a purely downward normal already contradicts the lower H vertex and y>=h.

A purely upward separator puts the whole E above h+sigma. Its center height would then be at least h+sigma+1/2>91/60 by(5), contradicting(6).

Hence a remaining separating side axis is strictly northwest or strictly northeast. Reflect the geometric proof horizontally in the northeast case, keeping track of which original endpoint occupies the left position. This reflection is a proof coordinate change on all the actual bodies, not a reassignment of force or properness.

For a northwest H-to-E separator, write E's geometric axes as

    n=(u,v), m=(-v,u),
    u,v>=0, u^2+v^2=1,
    w=u+v, mu=max(u,v).                               (11)

An E-owned strict northwest separator uses m and u,v>0. An H-owned separator is(-1,1)/sqrt(2), allowing the closed orientation endpoints in(11).

Let X_left denote whichever actual endpoint is on the left after the common proof reflection, and write its actual corner magnitudes as a_left,b_left. The complete X_left/E cover is

    horizontal:          min_E x>=1-a_left;
    vertical:            min_E y>=b_left;
    E-owned northeast:   min_E n.p>=u(1-a_left)+v b_left. (12)

The slab(8) and the true mean h>b_left-1 reduce a northwest X_left/E separator to the vertical row and a southeast separator to the horizontal row. The southwest possibility is excluded by the same two whole inclusions. The only remaining strict northeast side direction is E's n. Thus this is a full geometric face/vertex/owner cover, with no assumed contact between E and an obstacle.

The horizontal row is always impossible. In the H-owned case the top actual E vertex has height at least h+w+mu>=h+2>R. In the E-owned case its height is at least

    h+v+[1+sigma(mu-v)]/u >=h+sigma+1>R.

The division occurs only for u,v>0. The closed H-owned endpoints are handled separately. These are precisely the complete comparisons in Section4.1 of FOUR_C6, or Section3 of SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md.

The remaining northeast and vertical rows are treated next. Their exact proof scope matters: neither geometric separator may be inserted into an original stress.

## 4. The balanced endpoint family: each vertical row has its correct available premise

Assume

    a>b, c>d.                                         (13)

The elementary common-radius geometry gives

    10/7<a,c<2, 1/2<=b,d<3/2.                         (14)

These strict horizontal bounds are derived in Section1 of SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md without properness: a>=2 would force c<=sqrt(2) and simultaneously R^2>=17/4 and R^2<2c^2<=4; a<=10/7 contradicts the other endpoint's height>=1/2 and a>b. Reflection covers c. The argument includes a physical radial height1/2. Our independently proved(5) supplies the needed h>2/5.

### 4.1. Every balanced northeast row is already force-free at this exact geometry

The whole proof in Section4 of SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md, including all its orientation sectors and Certificates I--III in Section7, uses only:

    a_left>b_left>=1/2, a_right>b_right>=1/2,
    a_left+a_right=A, both actual circle equalities,
    10/7<a_left,a_right<2,
    h>2/5, b_left-1<h<b_left,
    the actual H center and the two whole-cap inclusions(8).

No endpoint proper inequality is used in that Section4 or in any of its three polynomial identities.

More explicitly, the two E-owned center projections give positive actual farthest-coordinate lower bounds. Their squared excess is affine nonincreasing in a_left, so the complete containing-circle inequality permits the comparison

    a_left <= (Q+4-b_left^2)/4.

The exact identities I and II then prove the strict excess throughout both full closed orientation/height rectangles. For H-owned northwest and u>=v, the owner-comparison excess is

    ((u-v)/w)[1+v(b_left-h)-sigma w]>=0.

For H-owned northwest and u<=v, both closest-point coefficients are positive from(14), h>2/5 and the true mean. The exact equality-line intersection norm is increasing in h and decreasing in the allowed a_left comparison; Certificate III proves its strict excess on the whole remaining rectangle.

Thus all balanced northeast rows are excluded for either original endpoint occupying the left position. This directly uses the complete continuous identities of the pinned source, not its original alternating-cycle entry. All closed b_left=1/2 endpoints were already included in those identities, as checked in the full physical-mask extension in Section2 of FOUR_C6.

### 4.2. If the left endpoint is original Y, its vertical row is impossible without X properness

Here b_left=d. Equation(7) gives d>D. A whole E above d has center height at least d+1/2>M, contradicting the universal center bound.

This is the entire reflected vertical row. In particular the proof never invokes a proper inequality at the opposite original X.

### 4.3. If the left endpoint is original X, the opposite endpoint is the genuinely proper Y

Here b_left=b. If b>D, the same center-height contradiction applies immediately.

If b<=D, use the complete scalar and center-cap proof in Sections5--6 of SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md, together with its Certificate IV. Its exact force-dependent scalar premise is only

    h>=d(1-1/c),

at the opposite, right endpoint. This is exactly our unchanged proper Y inequality(4).

For clarity, the complete operative dependencies are as follows. The assumption b<=D forces a>7/4>A/2, a>c, d>b and delta<0. The source proves

    sqrt(M^2-(b+1/2)^2)
       <h+a-1+sigma-(b+1/2),                          (15)

with positive right side, using the lower rational height obtained from d>=b+A(a-c)/(b+c) and the available(4). Its entire fourth polynomial identity covers b from1/2 through61/60 and every scalar comparison a in its enlarged closed rectangle. It does not require h<b for that auxiliary scalar statement.

For the actual original center cap

    K={ (x,y): x^2+y^2<=M^2, y>=b+1/2 },

the unchanged strict mean gives b+1/2-h>1/2. The original(4), h>2/5, and the true common-radius domain give the other endpoint-distance bound u_0<53/50. Equation(15) puts the upper-left edge distance below1/2. The complete top-vertex and negative-v_0 alternatives are printed in Section6 of the source.

Its extension from that cap endpoint to all northwest normals uses concavity of the exact H support on either side of45 degrees. The only possible extra endpoint, at45 degrees, is proved using an auxiliary scalar tuple with

    b'=M/sqrt(2)-1/2>=b,
    a'=sqrt(R^2-b'^2), c'=A-a',
    d'=sqrt(R^2-c'^2), h'=d'(1-1/c').

No actual force is assigned to this tuple. Its use is solely in the already proved scalar inequality(15). The actual comparison back to h uses exactly(4), via the increasing function a-1+d(1-1/c) at fixed radius. No h>=b(1-1/a) inequality occurs in that comparison.

The result is the complete strict support bound

    h_K(r)<h_H(r)+1/2

for every northwest unit normal r. Every unit extra has support halfwidth at least1/2, so this excludes all possible H/E separators in the vertical row.

All physical radial and equality endpoints remain: b=1/2 is in the closed scalar rectangle, b=D is allowed, and T-a=(b^2-1/4)/(T+a) may vanish without division by that expression. The auxiliary b' used above is strictly greater than1/2 because R>=2.

Sections4.1--4.3 handle every owner and both reflected orientations in the balanced family. The unavailable X properness is never imported.

## 5. The asymmetric family uses only actual geometry and the strict mean at the tall endpoint

Assume at least one endpoint has horizontal farthest-coordinate at most its vertical one. Both cannot do so, because then

    A=a+c<=sqrt(2)R<3,

whereas A>3.

Under a>=c, the tall endpoint must be Y. Indeed if a<=b, then c<=a<=b<=d, which would make both endpoints tall. Hence

    c<=d, a>b.

This includes c=d.

The exact geometric bounds from Section3 of FOUR_C6 apply:

    11/8<c<=R/sqrt(2)<3/2,
    d>=R/sqrt(2)>=sqrt(2)>7/5,

    a>389/200, 1/2<=b<3/4,
    -delta>19/80.                                    (16)

They use only the actual common-radius equalities, horizontal sum and weak lower corner heights. Their strict high-radius height bound is

    R^2>=17/4 implies h>d-1>9/20,                     (17)

from the unchanged original side-interior mean at the tall Y. The full-radius h>43/100 is already supplied by(5).

The complete asymmetric proof is Sections4--8 of FOUR_C6. Its force-dependent quantities were fully checked here:

* The horizontal rows use only the whole-cap geometry and h.
* If the geometric proof is reflected so that the tall actual Y is on the left, Section5 excludes every northeast owner/angle by actual farthest-corner or top-height bounds. Its vertical row is excluded by the tall center-height bound. No concurrence is used there.
* With the short actual X on the left, Section6 excludes every northeast owner/angle using(16), h>43/100, and the high-radius bound(17). The comparison quantities have positive signs before squaring, and the H-owned closest-point coefficients are proved positive. No endpoint properness enters.
* For the short-X vertical row, Sections7--8 use the strict actual mean h>d-1 at the opposite tall Y. Their complete scalar inequality is proved by comparison to c=d and one strict convexity bound in the radius parameter. Its center-cap extension uses the same strict mean and the exact circle geometry. It does not use a proper concurrence at X or, in that row, even at Y.

These are all the premises of that asymmetric geometric argument. The two formal proper inequalities printed in the older simple-cycle entry are not used in Sections3--8 after h>43/100 has been supplied. In particular no force or degree-two condition is transferred to X.

For additional specificity, its key vertical scalar is

    X_0+Y_0<3sigma+(d-c),
    Y_0=b+1/2, X_0=sqrt(M^2-Y_0^2).

The actual h>d-1 then gives

    X_0<h+a-1+sigma-Y_0.

This bounds every northwest H support excess of the full center cap strictly below1/2, including the possible45-degree endpoint. It is that actual side-interior mean, rather than an invented X concurrence, which completes the asymmetric vertical exit.

Thus every asymmetric geometric separator is also impossible.

## 6. Whole theorem and exact original channel applications

Every endpoint belongs either to the balanced family(13) or to the asymmetric family of Section5. Section3 exhausts all actual separating-axis possibilities, and Sections4--5 exclude each one. Therefore no whole extra E exists in the original Omega.

The only geometric comparison of exterior spokes occurred for a physically radial X. Section2 proves winding equality at every extra-interior point by first ruling out even one such point in the small outer cap. No square is moved or rotated, no original selected normal is changed, no physical circle coefficient is removed, and no original exterior spoke is replaced in the certificate.

For D02.L0134, take the actual channel

    X=0 -- H=5 -- Y=4.

The degrees remain three,two,two. Y's other actual neighbor3 is physically boundary, so the genuine properness premise is exactly the one checked in83f60. Whenever X's center is nonnegative in the common h>0 chart and a>=c, this entire actual channel pocket is empty.

For D02.L0135, take

    X=3 -- H=4 -- Y=5.

Y's other actual neighbor0 is physically boundary. X's other neighbor2 is not assumed boundary. The same nonnegative-X and a>=c feature is empty with all actual degrees, masks and original applications retained.

These are local one-proper geometric applications, not claims that either original load row is closed. The nonnegative-X a<c alternative is not addressed by this theorem. The separate negative-center theorem also has its own exact proof and independent-review requirement.

## 7. Exact complete inputs and review scope

| Complete source or review | SHA256 | Operative role |
| --- | --- | --- |
| ONE_PROPER_DIAGONAL_CHANNEL_OUTER_POCKET_CAPACITY_ONE.md | 83f60e7c35fdd4c517d27db4d2755ea5e14a4bab2b876c52cdfce7a85d286889 | Entire actual one-proper chart, fixed original exterior spokes, correct upper-region join and literal original degrees |
| REVIEW_ONE_PROPER_DIAGONAL_CHANNEL_CAPACITY_ROOT_2026_10_28.md | fb949e7038d0a8dfe444ba223aef52b0f618abb9cae5e9f637ae120ac4ab523b | Full independent review of that exact local entry and routing |
| DIAGONAL_CHANNEL_EXTERIOR_CAPACITY_ONE.md | 46f8be67b5c447a78f12cefb3f96474973ead5d48d4e65b346a1c77bdd8fee02 | Pure proper-endpoint height comparison, reprinted in Section1 |
| FOUR_C6_DIAGONAL_CHANNEL_CAP_EMPTY.md | 454b1c9cabb614d8c2a16a2ca297d6bbbadcd94340423ac5c93b72e05a092b5d | Complete geometric separator cover, physical radial endpoints, and all asymmetric comparisons, used only at the exact premises identified above |
| SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md | c5dec5c8cb78f83715624b59a1401748f07616acf44f9c567ab88da778c3ebbe | Complete balanced geometric northeast proofs, one-opposite-proper vertical scalar and all four continuous polynomial identities |
| REVIEW_DIAGONAL_CHANNEL_EMPTY_ROOT_2026_10_26.md | 31e2964eca8eed01907129f8edb27475d0c1a6130cb155b4ac0c4913c6d9217e | Historical complete source and physical-mask audit of the older geometric argument |
| REVIEW_FOUR_C6_DIAGONAL_CAP_EMPTY_GLOBAL_2026_10_26.md | e2cc86f9285e13a9d58e5f8ca2ae2b3d8bec7ded04a3f2ba27288db9708cd112 | Historical separate complete geometric audit, including all original orientation and scalar endpoints |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | The unchanged original full-force/torque and physical-mask setting |

All complete mathematical sources and both older whole geometric reviews were read. The older FOUR_C6 reviews identify its pre-status-change mathematical pin dba7941f48fb1693518603e96751b78e1e2c3feb9c7d6135d1cdc4d1422efc4c; the current complete source read here is explicitly pinned454b1c9c. No old review is silently repinned to this new one-proper theorem. This manuscript's new scope and original-spoke join require their own full independent review.

The new work is the whole a>=c one-proper join, the full radial-chord winding argument at every extra-interior point, and the complete reflected vertical-row accounting which avoids imposing X properness. The older polynomial identities are continuous exact geometric inequalities on their displayed closed domains; they are inherited at that precise scope and are not pose-enumeration certificates.

No original family flag is changed. No Lean compilation, CI/workflow run, numerical pose search, remote write or shared-ledger edit is used.

