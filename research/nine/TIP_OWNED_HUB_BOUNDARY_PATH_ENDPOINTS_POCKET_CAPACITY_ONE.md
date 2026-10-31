# Two tip-owned endpoints leave a single-hub closing pocket capacity at most one

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed uniform hand theorem, submitted for full independent review.** The new low-roof opposite-vertex proof is printed in full below. It joins the independently reviewed adjacent-vertex theorem and the new complete high-roof opposite-vertex theorem, giving one whole endpoint-owner feature without any remaining height, orientation, or physical-circle-mask branch.

Put

    Q=1105/256, r=5/4, sigma=1/sqrt(2).

## 1. Entire unchanged physical setting

Work in 2<R<=sqrt(Q). Retain an entire selected positive component

    H, B_1,...,B_k, 3<=k<=6;
    B_i B_(i+1), 1<=i<k;
    H B_1, H B_k, and any subset of H B_i for 1<i<k.

The actual H is unloaded, every B_i has positive total circle load, and the actual exterior-face order is H,B_1,...,B_k,H. The two endpoints V=B_1 and T=B_k have their true positive degree two. All internal bodies retain their actual degrees and every original force and moment equation.

Assume the actual intersections H cap V and H cap T are singleton points in the relative interiors of sides of the respective endpoint tips. Thus both endpoint contacts are owned by the boundary tips. Keep every original internal spoke, all other owners and strict free normals, every genuine side mean including its endpoint values, every physical circle corner and individual zero circle coefficient, and every other physical unit.

**Theorem.** The actual closing exterior pocket through H between T and V has capacity at most one additional unit square.

No condition is imposed on the locations of the two endpoint vertices or on the norm of the intervening exterior H vertex. No internal loaded body receives a degree-two equation. The conclusion concerns this one exterior pocket; a caller must still supply its complete central and other exterior allocation.

## 2. Complete endpoint-feature cover and the actual opposite-vertex chart

A singleton contact in a relative side interior of a tip is a vertex of H. Its retained tip normal strictly exposes that vertex of H. An H-axis normal in this situation would give positive shared length, contrary to the singleton premise.

The two vertices are distinct. Indeed GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md proves that the two endpoint boundary squares are closed-disjoint: an extra contact between them would close a physical boundary cycle of length k<=6, which is impossible. Coincident H vertices would be a physical common point of those two endpoints.

There are therefore exactly two geometric possibilities:

* The vertices are adjacent. The complete theorem ADJACENT_HUB_VERTEX_TIP_OWNED_ENDPOINT_POCKET_CAPACITY_ONE.md already proves the claimed pocket capacity with all the present original data.
* The vertices are opposite. The rest of this source treats that entire possibility.

For opposite vertices, Section 6 of the general single-hub theorem, using all original H forces and moments, gives a rigid chart with occupied lower H arc:

    P_L=(-X,h), P_R=(Y,h),
    X,Y>0, X+Y=sqrt(2), h>0,
    c_H=(x_0,h), x_0=sigma-X=Y-sigma,
    A_H=(x_0,h+sigma).                                 (1)

Here A_H is the actual intermediate vertex on the exterior H arc. For each endpoint, reflected at the right one, write

    n=(-b,a), k=Jn=(-a,-b),
    a=sin(phi), b=cos(phi), 0<=phi<=pi/4,
    P=(-X,h),
    V=P+[0,1]n+[-rho,1-rho]k, 0<rho<1.                (2)

The weak angle endpoints enlarge the estimates harmlessly. The strict original endpoint moment is

    K=b*h-a*X>0.                                       (3)

The genuine all-mask degree-two proper-concurrence lemma applies because the endpoint's actual other neighbor is a physical boundary square. It gives q=P+ell*n, ell>=0, a positive multiple of the full circle resultant. Hence the resultant's k-component is negative. The center's n-coordinate N+1/2 is positive, where

    N=b*X+a*h>0.

The complete physical corner comparison therefore gives

    Z=K+rho>=1/2,
    R^2=(N+1)^2+Z^2.                                  (4)

For Z>1/2 the far negative-k corner is unique. For Z=1/2 both outer n-face corners are physical circle corners; the negative-k corner has positive weight, and the other original weight may be zero or positive. Thus (4) retains the whole two-corner mask.

The gap-facing physical circle corner and the intervening own corner are

    A=P-rho*k, Z_L=A+n=(N+1)n-Zk.                     (5)

Their chain P--A--Z_L lies in the actual tip, rises above h, and has strictly increasing norm: first its negative k-coordinate grows in absolute value with n=N>0 fixed, then its positive n-coordinate grows with k=-Z fixed. The right endpoint has the reflected description.

Since X=N*b-K*a<=N, equation (4) gives

    0<X<=N<=sqrt(R^2-1/4)-1<61/60<41/40,              (6)

and the same holds for Y. The strict radical reserve is

    (121/60)^2-1041/256=31/57600>0.

The left circle corner has negative x-coordinate and y>h, and the right one has positive x-coordinate and y>h. Also the whole left tip lies in x<x_0, because its maximum x is -X+rho*a<-X+sigma=x_0. The reflected right tip lies in x>x_0.

## 3. The whole high-roof domain is already covered

If

    |A_H|>=r,                                          (7)

apply OPPOSITE_HUB_VERTEX_TIP_OWNED_HIGH_ROOF_POCKET_CAPACITY_ONE.md. Its complete theorem has exactly the original component, endpoint, mask, and mean scope above. It proves capacity at most one, including equality in (7).

In brief, that source proves h>1/2, retains the actual whole cap above h, and uses the two actual H roof supports to separate every additional unit's connected inner-circle arc. The smaller-port side has less than pi/4 of usable arc after the complete scalar and occupied-crosscut argument; the other side has at most pi/2. All actual routing is part of that theorem, not supplied by this summary.

It remains to prove the complementary domain |A_H|<r. Sections 4 through 10 prove the slightly enlarged closed low-roof domain

    |A_H|<=r.                                          (8)

The overlap at equality is harmless.

## 4. Every original low-roof endpoint port is strictly inside the inner circle

Condition (8) and (1) imply

    0<h<=H:=r-sigma<11/20.                             (9)

Together with (6), this gives, at both endpoints,

    |P|^2=X^2+h^2
       <(41/40)^2+(11/20)^2
        =433/320<25/16=r^2.                            (10)

The exact final reserve is 67/320. Thus both original ports are strictly inside the inner circle. By (8), (10), the entire exterior H roof P_L--A_H--P_R is in the closed inner disk.

The norm-increasing endpoint chain (5), starting inside the inner circle and ending at radius R>r, crosses it exactly once. Write its gap-facing crossing angle at the left as pi-eta_L, and at the right as eta_R. For either endpoint,

    eta=phi+min{ arccos(N/r),
                 arcsin(min(Z/r,1)) }.                 (11)

If A lies outside or on the inner circle, the first segment P--A supplies the normal-face limiter arccos(N/r). If A lies inside, the second segment A--Z_L supplies the tangent-face limiter arcsin(Z/r). At the face join both expressions agree. Equation (11) is a calculation on the actual endpoint square, including the full physical mask Z=1/2.

For a tangent-face limiter define

    L=sqrt(r^2-Z^2).

Then Z<r and L>=N. Using (4),

    N>=(R^2-1-r^2)/2>=23/32.                           (12)

These are necessary full-interval inequalities, not selected orientations.

## 5. A complete tangent-face estimate for the original port

**Lemma.** For every tangent-face limiter in the low-roof domain, if B is the actual height of its inner-circle crossing, then

    X+B>10/7>sqrt(2).                                  (13)

In the endpoint's own chart,

    B=L*a+Z*b,
    X=(N-h*a)/b,
    0<=a<=sigma, b=sqrt(1-a^2)>=sigma.

We prove (13) over the complete domain with two continuous N intervals.

### 5.1. The whole interval 23/32<=N<=17/20

Equation (4), R>=2 and N<=17/20 give

    Z^2>=4-(37/20)^2=231/400>9/16,

so Z>3/4. Also L>=N and h<11/20. Multiply the expression for X+B by b and subtract (10/7)b. Using N>=23/32 yields

    b*(X+B-10/7)
      >47/32-(3/4)a^2+(23/32)a*b-(11/20)a-(10/7)b.

Since b>=sigma>7/10, this is greater than

    47/32-(3/4)a^2-(3/64)a-(10/7)b.                    (14)

The exact square-root bound

    b<=1-a^2/2-a^4/8

holds throughout 0<=a<=sigma. Its right side is positive, and, on putting t=a^2, the squared reserve against 1-t is t^3/8+t^4/64>=0.

Substitution in (14) gives the lower polynomial

    P(a)=9/224-(3/64)a-a^2/28+(5/28)a^4.              (15)

For 0<=a<=1/2, discard the nonnegative quartic and use the two endpoint bounds to get

    P(a)>=9/224-3/128-1/112=1/128>0.

For 1/2<=a<=sigma, use a^4>=a^2/4 and a<5/7:

    P(a)>=9/224+a^2/112-(3/64)a
         >9/224+1/448-15/448=1/112>0.

Thus (13) holds throughout this whole interval, including a=0 and every face join.

### 5.2. The whole interval N>=17/20

Here L>=N gives

    Z^2=r^2-L^2<=25/16-(17/20)^2=21/25<1,

so Z<1. The exact difference is

    X+B-(N+Z)
       =a^2/(1+b)*(N/b-Z)+a*(L-h/b).                  (16)

The uniform bounds imply

    N/b-Z>-3/20,
    L-h/b>17/20-(11/20)*(10/7)=9/140.

If a>0, use

    a/(1+b)<=sqrt(2)-1<3/7

in (16) to obtain

    X+B-(N+Z)
      >a*[9/140-(3/20)*a/(1+b)]>0.                   (17)

If a=0, the exact equality is X+B=N+Z; this endpoint is retained separately.

Finally, the following exact circle identity proves N+Z>10/7 uniformly, including a=0:

    (N+Z+1/2)^2+1/4-[(N+1)^2+Z^2]
        =(2Z-1)*(N+1/2)>=0.

Because R^2>=4, (4) implies

    N+Z>=sqrt(15)/2-1/2>10/7.

The strict radical comparison is sqrt(15)>27/7, with squared reserve 6/49. Equations (16), (17) and the explicit a=0 endpoint prove (13) on the whole second interval. This completes the tangent-face lemma.

## 6. A normal-face limiter retains the actual horizontal port bound

For a normal-face limiter,

    eta=phi+arccos(N/r)>=arccos(X/r).                   (18)

Indeed put gamma=arccos(X/r). If phi>=gamma the conclusion is immediate. Otherwise 0<=phi<gamma, and (10) gives

    N=X*cos(phi)+h*sin(phi)
      <=X*cos(phi)+sqrt(r^2-X^2)*sin(phi)
       =r*cos(gamma-phi).

The decreasing cosine on the relevant interval gives arccos(N/r)>=gamma-phi. This proves (18), without choosing a different contact point or dropping an endpoint circle corner.

## 7. Both normal limiters and every mixed limiter pair have gap below pi/2

We prove

    eta_L+eta_R>pi/2.                                  (19)

First suppose both limiters are normal faces. From (6),

    X^2+Y^2<(41/40)(X+Y)
              =(41/40)sqrt(2)<123/80<25/16=r^2.

For 0<X,Y<r, this is precisely

    arccos(X/r)+arccos(Y/r)>pi/2.

Apply (18) to prove (19).

Now suppose one limiter is tangent and the other normal. Reflect the complete chart if needed so that the tangent endpoint has port coordinate X and crossing height B=r*sin(eta_L). If (19) failed, both eta angles would be less than pi/2 and

    eta_R<=pi/2-eta_L.

The normal endpoint estimate (18) then gives

    Y>=r*cos(eta_R)>=r*sin(eta_L)=B.

This contradicts the tangent-face lemma:

    X+Y>=X+B>10/7>sqrt(2)=X+Y.

Thus (19) holds for every mixed pair. A face join can be classified either way, because the two limiting expressions coincide there.

## 8. Both tangent limiters: one coupled monotonicity argument covers every angle

Assume both limiters are tangent. Put

    alpha=arcsin(2/5),
    Phi=phi_L+phi_R,
    u_L=arcsin(Z_L/r), u_R=arcsin(Z_R/r).

Here Z_j denotes the scalar own-coordinate from (4), not a substituted circle point. Since Z_j>=1/2, both u_j>=alpha.

Suppose for contradiction that eta_L+eta_R<=pi/2. Then

    u_L+u_R<=pi/2-Phi,
    0<=Phi<=Phi_*:=pi/2-2alpha.                       (20)

### 8.1. A full fixed-sum minimum for the two circle coordinates

Define

    f(u)=sqrt(4-r^2*sin(u)^2), 0<=u<pi/2.

It decreases with u. For two arguments u>=v>=0 with u+v<=pi/2, the sine identity gives

    sin(2u)-sin(2v)=2*cos(u+v)*sin(u-v)>=0.

Also f(u)<=f(v). Consequently

    |f'(u)|=r^2*sin(u)*cos(u)/f(u)>=|f'(v)|.

For a fixed sum S<=pi/2, the function f(u)+f(S-u) therefore decreases as u moves from S/2 toward S-alpha. Its minimum with both arguments at least alpha is attained at the pair alpha,S-alpha.

Since the original sum in (20) may be smaller than pi/2-Phi, monotonicity allows it to be enlarged first. Equation (4), R>=2, and the full fixed-sum minimum then yield

    N_L+N_R
      >=f(alpha)+f(pi/2-Phi-alpha)-2
       =L(Phi),

where

    L(Phi)=sqrt(15)/2
              +sqrt(4-r^2*cos(Phi+alpha)^2)-2.         (21)

No concavity of f over an unjustified larger interval was used.

### 8.2. The actual shared height gives the opposite upper bound

The actual unchanged endpoint formulas give

    N_L+N_R
      =X*cos(phi_L)+Y*cos(phi_R)
         +h*(sin(phi_L)+sin(phi_R))
      <=sqrt(2)+2H*sin(Phi/2)
       =U(Phi),                                      (22)

because X+Y=sqrt(2), h<=H=r-sigma, and

    sin(phi_L)+sin(phi_R)
       =2sin(Phi/2)cos((phi_L-phi_R)/2)
       <=2sin(Phi/2).

Thus it is enough to prove L(Phi)>U(Phi) throughout (20).

### 8.3. The difference decreases, and its last endpoint is still positive

On 0<=Phi<=Phi_*, the angle Phi+alpha lies in [alpha,pi/2-alpha]. Its cosine squared is at most 21/25. Therefore

    L'(Phi)
      =r^2*cos(Phi+alpha)*sin(Phi+alpha)
          /sqrt(4-r^2*cos(Phi+alpha)^2)
      <=25/(8sqrt(43))<1/2.                           (23)

The strict final comparison follows from 625<688.

On the other hand,

    U'(Phi)=H*cos(Phi/2)
      >=H*cos(Phi_*/2)
       =(5sqrt(2)-4)*(sqrt(21)+2)/40>1/2.             (24)

For a fully rational verification of the last strict sign, use sqrt(2)>140/99 and sqrt(21)>32/7. Their squared reserves are 2/9801 and 5/49. The right side of (24) is then greater than

    1748/3465=1/2+31/6930.

Hence L-U decreases strictly on the entire interval. At its last endpoint,

    L(Phi_*)=sqrt(15)-2>13/7.

Also H<11/20, sqrt(2)<10/7, and

    sin(Phi_*/2)=(sqrt(21)-2)/(5sqrt(2))<3/8.

For this sine comparison, sqrt(21)<23/5 and sqrt(2)>7/5 give the stronger upper bound 13/35<3/8. Consequently

    U(Phi_*)<10/7+33/80,

and

    L(Phi_*)-U(Phi_*)>13/7-10/7-33/80=9/560>0.       (25)

Equations (23)--(25) prove L>U everywhere in (20), contradicting (21), (22). This excludes the entire both-tangent alternative and completes (19) for every pair of actual limiting faces.

## 9. Full low-roof physical routing into the interval in (19)

We now join the scalar bound to the whole actual pocket.

Use the actual endpoint gap-facing chains (5), the actual exterior H roof P_L--A_H--P_R, and their upper closing outer-circle arc. The complete endpoint and circle order from GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md identifies this as the original closing exterior region, up to its occupied endpoint pieces. Deforming the original center/contact crosscut to these chains takes place inside H,V,T. It preserves winding about every point of an extra's open interior. The other original units and zero-weight contacts can only subdivide or remove free space.

Every point of this boundary has y>=h, with the two endpoint circle corners strictly above h. Thus every whole extra assigned to this pocket lies in y>=h. Its open inner-circle arc, when supplied below, lies strictly above that line.

By (10), both endpoint chains start strictly inside the inner circle. Their norm is strictly increasing, so each crosses it once and its entire remaining strand lies in the upper annular region

    r<=|p|<=R, y>=h.

The two actual endpoint units are closed-disjoint; these strands are disjoint. They connect the inner upper cap arc to the outer upper cap arc without meeting the two horizontal side boundaries. The outer endpoints occur in right-to-left order Z_R,Z_L. The same order must hold for their inner endpoints: otherwise one strand, joined to a side boundary of this annular strip, separates the two ends of the other and forces an intersection. This is the ordinary Jordan separation argument on that strip; it requires no radial monotonicity of their angle.

Therefore the inner exits have the order

    eta_R<=pi-eta_L.

If no nonempty interval remains, there is no inner-circle point of a pocket extra. Otherwise every such point lies in the open intervening interval

    eta_R<theta<pi-eta_L.                             (26)

To see the side assignment directly, the inner-circle point at angle zero lies below h and outside the pocket. On following the upper inner circle, the endpoint strands are its two crossings of the occupied upper boundary. The H roof lies in the closed inner disk by (8), (10), and contributes no outward crossing; if A_H lies on the inner circle, that additional occupied point only removes space from (26). The outer-circle arc has radius R>r. Thus the actual bounded-pocket portion of the inner circle is between the endpoint crossings. Avoiding the whole closed endpoint squares cannot enlarge it.

This argument is for every point of every additional square's open interior, not only its center. At the single low-roof equality |A_H|=r, at a physical side contact elsewhere, or at a zero-weight junction, use a compact interior subset first and the same occupied homotopy. The unchanged closed core is avoided throughout, so winding and the open interval assignment survive. No mean in an original equation is replaced by a boundary extreme.

By (19), the full interval (26) has length

    pi-eta_L-eta_R<pi/2.                               (27)

## 10. Every actual extra needs more than pi/4, completing the low-roof capacity

The complete general single-hub theorem gives every whole unit E in this pocket strict distance greater than 1/4 from the original origin. This conclusion was proved there at every endpoint owner and every original mean; the present low-roof case is literal.

For clarity this distance statement supplies the exact hypothesis of the force-free cap-arc theorem. Let p be a nearest point of the actual closed convex E to O. Then |p|>1/4. For every x in E, the right derivative at zero of |p+t(x-p)|^2 is nonnegative, so

    p.(x-p)>=0.

Thus E lies in the actual support half-plane

    (p/|p|).x>=|p|>1/4.

Section 1 of GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md now supplies E one connected open r-circle arc of length greater than pi/4, lying wholly in E's open interior. This uses the entire actual E and its own support; it does not replace the pocket by a center sector or impose a common orientation on extras.

Two interior-disjoint extra squares supply disjoint such arcs, requiring total length greater than pi/2. Section 9 routes both entire arcs into the one interval (27), whose length is below pi/2. This is impossible.

Hence the whole low-roof opposite-vertex pocket has capacity at most one. Section 3 handles the entire complementary high-roof case, and Section 2 handles all adjacent vertices. The stated full tip-owned-endpoint theorem is proved.

## 11. Literal complete endpoint-owner consequence for D02.L01345

In the original row M6.B6.HEXAGON.D02.L01345 retain the six rim edges

    01,12,23,34,45,50

and its single positive chord 02. Take

    H=2, V=1, T=3,
    (B_1,...,B_5)=(1,0,5,4,3).

The true degrees and loads remain:

| Actual body | Role | Positive pair degree | Circle load |
| --- | --- | --- | --- |
| 2 | H | 3, neighbors 1,0,3 | zero |
| 1 | V=B_1 | 2 | positive |
| 0 | B_2 | 3 | positive |
| 5 | B_3 | 2 | positive |
| 4 | B_4 | 2 | positive |
| 3 | T=B_5 | 2 | positive |

If the actual 12 and 23 contacts are both singleton points in relative interiors of sides of their respective boundary tips 1 and 3, the whole closing exterior pocket has capacity at most one by this theorem, with no restriction on which distinct hub vertices occur or on any vertex norm.

The complete central-capacity theorem gives at most one additional unit in the whole central free union. Every direct boundary-pair exterior pocket along 1--0--5--4--3 is empty. Therefore at most two of the three original completing units can fit. This excludes the entire both-tip-owned endpoint feature of the original D02 load row.

The original row itself remains open: a hub-owned endpoint axis, including a positive shared side and its full mean, or a genuinely free vertex endpoint is outside this theorem's premise. No fixed-point selection theorem is used to erase either alternative. No new fine ID or whole-row/coarse credit is claimed.

## 12. Exact operative sources and honest scope

| Source | SHA256 | Exact use |
| --- | --- | --- |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 | Complete original path/hub order, endpoint moments and normal signs, all-owner exterior quarter-disk clearance, actual closing-pocket routing |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Local Lemma 2.1 only: true loaded-degree-two proper concurrence with an actual physical boundary neighbor, retaining both physical circle masks |
| ADJACENT_HUB_VERTEX_TIP_OWNED_ENDPOINT_POCKET_CAPACITY_ONE.md | d68e442989665d423d0f98963901785f93d5d5077e76663223d67d0cf2f69649 | Entire adjacent-vertex endpoint feature, with every actual spoke, mean, mask, and extra |
| OPPOSITE_HUB_VERTEX_TIP_OWNED_HIGH_ROOF_POCKET_CAPACITY_ONE.md | 121c24eea215f1d7de199467ba839aaeaa348007d4c4c57e54e21bca38c0b205 | Entire opposite-vertex domain norm(A_H)>=5/4, with its full geometric routing and separately reviewed continuous scalar input |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb | Force-free Section 1 for every actual additional square after its own nearest-point support is supplied |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Whole central capacity in the literal original D02 join |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Empty actual direct boundary-pair exterior pockets |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Original single chord, load mask and true degree table |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Supplies R>2 for the unchanged full nine-square caller |

The new tangent-face estimate, full coupled both-tangent comparison, and low-roof occupied routing are complete proofs above, not summaries of a parameter search. The complete adjacent and high-roof sources retain their own exact input and independent-review records. Adoption of the whole theorem requires a full independent review of this source and its literal joins.

No numerical pose, finite angle mesh, scalar certificate packet, force deletion, normal reselection, changed original contact application, Lean compilation, CI, remote write or ledger mutation is used.

