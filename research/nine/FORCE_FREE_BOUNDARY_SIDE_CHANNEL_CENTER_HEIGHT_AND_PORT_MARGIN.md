# Every physical boundary side channel has strictly outward endpoint centers

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed force-free geometric theorem, submitted for full independent review.** This source removes every endpoint-degree and positive-concurrence premise from the outward-center and port-margin conclusions for a width-one normal channel. It proves neither exterior-pocket capacity nor an occupied-channel proximity theorem.

All statements concern the unchanged actual units, original applications and complete shared-side mean intervals. Physical boundary means actual contact with the containing circle, independently of whether a particular corner coefficient is positive.

## 1. Exact geometric theorem

Put Q=1105/256. Let X,H,Y be actual unit squares with pairwise disjoint open interiors, contained in the same disk D_R centered at O, where

    2 <= R <= sqrt(Q).

Suppose X and Y physically touch its circle. Assume the two unchanged actual support applications have the width-one side-channel form

    H=[-a,b] times [v,v+1], a+b=1,
    P_X=(-a,h) in X intersect H,
    P_Y=(b,h) in Y intersect H,
    v<=h<=v+1,
    X subset {x<=-a}, Y subset {x>=b}.                 (1)

The coordinates retain the original disk origin. The two applications may be any actual shared-side weighted means, including either endpoint. No midpoint, new contact or replacement transmitter is introduced.

**Theorem.** The common port line does not contain O: h is nonzero. After the common reflection y to -y if necessary, so h>0, all of the following hold:

    (c_X)_y>0, (c_Y)_y>0,
    h>3/10,
    7/100<a,b<61/60.                                  (2)

The original endpoint centers have strictly opposite horizontal signs:

    (c_X)_x<-29/60, (c_Y)_x>29/60.                     (3)

Every actual vertex of H consequently has norm greater than 7/100, for its entire original transverse slider and every application mean.

This is a geometric theorem. It assumes no force, torque, circle weight, contact owner at X or Y, positive degree, boundary neighbor, concurrence, selected-normal modification, or simple-cycle component. All other packing units and their contacts can remain in place.

The center conclusions mean that both centers lie strictly on the side of the port line's parallel line through O facing that port line. In the normalized display, this is the upper half-plane y>0. It is not a claim that their heights exceed h.

## 2. Universal endpoint estimates without any center-height premise

Let K be a unit square contained in D_R with an actual right support point

    P=(-a,h), a>0, h>0, K subset {x<=-a}.

We prove

    R^2 >= (a+1)^2+h^2.                               (4)

This lower estimate needs only containment; physical boundary contact is unnecessary.

If the support is an own side axis, K is parallel to the displayed axes. The actual point P-(1,0) belongs to K, including at either end of the actual side. Its squared norm is the right side of (4).

Otherwise P is the exposed rightmost vertex. Write the actual inward unit side vectors as

    u=(-c,s), w=(-s,-c),
    c,s>0, c^2+s^2=1,

so K=P+[0,1]u+[0,1]w. The letters u,w denote actual orthogonal own axes, not selected normals at another contact.

Set C=c+s and D=c-s. The two actual vertex comparisons are

    |P+u|^2-[(a+1)^2+h^2]
        =2a(c-1)+2hs,                                (5)

    |P+u+w|^2-[(a+1)^2+h^2]
        =1+2a(C-1)-2hD.                              (6)

If h>=as/(1+c), the expression in (5) is nonnegative, because s^2=(1-c)(1+c). This proves (4).

If h<as/(1+c) and D<=0, every term on the right of (6) is nonnegative: C>=1, a>0, and -2hD>=0. In particular it is at least one.

If h<as/(1+c) and D>0, (6) is strictly greater than

    1+2a[(C-1)-sD/(1+c)]
      =1+2as/(1+c)>0.                                (7)

The identity follows by expanding the numerator and using c^2+s^2=1. These cases exhaust the exposed-vertex domain. Thus (4) holds without restricting the sign of the center height or guessing which actual corner is on the circle.

There is a complementary upper estimate. If K physically touches the circle and h>=a>0, then

    R^2 <= (a+1)^2+(h+1)^2.                           (8)

For an axis-owned support, every actual point of K has horizontal coordinate between -a-1 and -a, and every vertical coordinate lies between h-1 and h+1. This proves (8) at all its corners and hence at every physical circle corner, for every original mean.

For an exposed-vertex support, the only four candidate corner norms are those of P,P+u,P+w,P+u+w. The adjacent corners obey

    |P+u|^2 =a^2+h^2+1+2ac+2hs
                <=a^2+h^2+1+2a+2h,

    |P+w|^2 =a^2+h^2+1+2as-2hc
                <=a^2+h^2+1+2a.

The opposite corner obeys

    |P+u+w|^2
       =a^2+h^2+2+2[(a-h)c+(a+h)s]
       <=a^2+h^2+2+2(a+h),                            (9)

since a-h<=0 and 0<s<1. The same bound is immediate at P. An actual physical circle corner attains R, so (8) follows. Physical two-corner ties and zero individual circle coefficients are included.

Reflection in the vertical axis gives the identical statements for a left support point (a,h) and a square in x>=a.

## 3. The port line is nonzero and its horizontal signs are strict

For any contained unit with center c, its farthest own-frame corner has squared norm

    |c|^2+1/2+|c.e_1|+|c.e_2|
        >=|c|^2+|c|+1/2.

Let M=91/60. The exact reserve

    M^2+M+1/2-Q=31/57600>0                            (10)

therefore gives |c|<M for every actual contained unit.

Write H_X,H_Y for the true horizontal support halfwidths of X,Y. They satisfy H_X,H_Y>=1/2. The actual supports in (1) give

    (c_X)_x=-a-H_X, (c_Y)_x=b+H_Y.

Thus a,b<61/60. As a+b=1, also

    -1/60<a,b<61/60.                                  (11)

Moreover

    (c_Y)_x-(c_X)_x=1+H_X+H_Y>=2.

Combining this with |(c_X)_x|,|(c_Y)_x|<91/60 gives precisely (3), independently of the sign of h.

Suppose h=0. The smaller of a and b is at most 1/2 and, by (11), greater than -1/60. Hence one actual endpoint application has norm at most 1/2. A unit's diameter is sqrt(2), so an actual physical circle corner of that endpoint would give

    R<=1/2+sqrt(2)<2,

a contradiction. Consequently h is nonzero. Reflect the entire unchanged data if necessary, obtaining h>0.

We next prove a,b>0. If a<=0, then b>=1. Apply the reflected (4) at the actual right endpoint Y:

    h^2<=R^2-(b+1)^2<=Q-4=81/256.

The original left application then satisfies

    |P_X|^2<1/3600+81/256<(23/40)^2.                   (12)

The last reserve is 803/57600. Using an actual physical circle corner of X and its unit diameter,

    R<=|P_X|+sqrt(2)<23/40+57/40=2,

where (57/40)^2-2=49/1600>0. This is impossible. Reflection excludes b<=0 as well. Thus a,b>0 before any endpoint-center-height conclusion is used.

For later use, choose the smaller of the positive a,b, which is at most 1/2. Its actual boundary point has norm at least R-sqrt(2), again by the unit diameter. Therefore

    h^2 >= (R-sqrt(2))^2-1/4
          >= (2-sqrt(2))^2-1/4
          >9/100.                                    (13)

Indeed sqrt(2)<283/200, with squared reserve 89/40000, makes the last expression strictly greater than 23/4-4(283/200)=9/100. Since h>0, we obtain h>3/10.

## 4. A complete upper radius bound for a nonpositive endpoint center height

Assume for contradiction that the actual left endpoint has

    (c_X)_y<=0.                                      (14)

We prove the closed-endpoint bound

    0<h<=1/2,

    R^2 <= a^2-3h^2+2+2a sqrt(2-4h^2)
          <(a+sqrt(2))^2.                             (15)

The second strict inequality uses h>0 and a>0.

### 4.1. An exposed-vertex support

Use exactly the actual axes u=(-c,s),w=(-s,-c) of Section 2. Its center height is h+(s-c)/2. Thus

    D=c-s>=2h>0, D<=1,
    C=c+s=sqrt(2-D^2).

In particular h<=1/2. The opposite vertex P_X+u+w attains the largest squared norm of all four actual vertices. Here are all comparisons, retaining equality:

    |P_X+u+w|^2-|P_X+u|^2
        =1+2as-2hc
        >=1+2as-c(c-s)>=0,

    |P_X+u+w|^2-|P_X+w|^2
        =1+2ac+2hs>0,

    |P_X+u+w|^2-|P_X|^2
        =2+2aC-2hD
        >=2+2aC-D^2>0.                               (16)

The first lower bound equals s^2+cs+2as and is positive on the open vertex frame. Its weak form also retains the aligned physical-two endpoint. No unique physical circle mask is asserted.

Since X physically touches the circle, (16) gives

    R^2=a^2+h^2+2+2a sqrt(2-D^2)-2hD.                (17)

For fixed a,h>0, the last expression is strictly decreasing as a function of D on [2h,1]. Its derivative is

    -2aD/sqrt(2-D^2)-2h<0.

Substituting D>=2h in (17) proves the weak bound in (15).

### 4.2. An axis support and every original mean

Write the actual aligned square as

    X=[-a-1,-a] times [v_X,v_X+1].

The original application only gives v_X<=h<=v_X+1; it is not replaced by a corner or midpoint. The assumed nonpositive center height gives v_X<=-1/2. Since h>0, these facts imply

    h-1<=v_X<=-1/2, 0<h<=1/2.

The farthest vertical magnitude is -v_X, including the physical two-corner tie v_X=-1/2. Consequently

    R^2=(a+1)^2+v_X^2
        <=(a+1)^2+(1-h)^2.                            (18)

The right side of (18) is the expression in (17) at D=1. Since 2h<=1, the same decreasing-function comparison bounds it by its value at D=2h. This proves (15) at every axis mean, including h=1/2 and every equality in (18).

Thus the entire nonpositive-center domain satisfies (15), with no omitted support feature or physical mask.

## 5. Two complete interval comparisons exclude that domain

The strict part of (15) implies

    R<a+sqrt(2), b=1-a<1+sqrt(2)-R<=sqrt(2)-1.         (19)

In particular b<5/12, because sqrt(2)<17/12 with squared reserve 1/144.

If h<=b, the actual point P_Y belongs to the physical boundary unit Y, so its diameter yields

    R<=sqrt(b^2+h^2)+sqrt(2)
       <=sqrt(2)b+sqrt(2)
       <2+2sqrt(2)-sqrt(2)R.

This says R(1+sqrt(2))<2(1+sqrt(2)), contradicting R>=2. Hence h>b.

The reflected upper estimate (8) now applies to the original right endpoint:

    4<=R^2<=(b+1)^2+(h+1)^2.                          (20)

Since h<=1/2, (20) gives b>=sqrt(7)/2-1>3/10. The strict last comparison uses 7-(13/5)^2=6/25. Therefore

    a<7/10.                                         (21)

Since b<5/12, (20) also gives

    (h+1)^2>4-(17/12)^2=287/144>49/25.

The final positive reserve is 119/3600. Thus

    h>2/5.                                          (22)

Combining (15), (21) and (22),

    R^2
       <=a^2-3h^2+2+2a sqrt(2-4h^2)
       <49/100-12/25+2+42/25
       =369/100<4.                                   (23)

For the cross term, sqrt(2-4h^2)<sqrt(34)/5<6/5; the squared reserve 36-34=2 is positive. The final reserve is 4-369/100=31/100.

Equation (23) contradicts R>=2. It excludes every nonpositive height in (14), including center-height zero and all physical-two corner-weight endpoints. Thus (c_X)_y>0. Reflecting horizontally and interchanging the unchanged endpoint names proves (c_Y)_y>0.

This is a whole continuous geometric proof. The comparisons in (15)--(23) cover all actual orientations and means; they do not construct or sample comparison poses.

## 6. The complete strict port margin

The following proof is printed in full to make clear that no simple-cycle or concurrence premise remains.

Suppose 0<a<=7/100. If h<=a, then the original actual boundary point P_X and the unit diameter give

    R<=sqrt(a^2+h^2)+sqrt(2)
       <=sqrt(2)(1+a)
       <(3/2)(107/100)<2,

a contradiction. Hence h>a.

Apply (8) at the original left endpoint and (4) at the original right endpoint, with b=1-a:

    (2-a)^2+h^2 <=R^2<=(a+1)^2+(h+1)^2.

Expansion gives h>=1-3a>0, and therefore

    R^2 >=(2-a)^2+(1-3a)^2
          =5-10a+10a^2
          >=4349/1000>1105/256.                      (24)

The quadratic is decreasing on [0,7/100]. The final reserve is 1043/32000. This contradiction proves a>7/100, and reflection proves b>7/100.

Every actual vertex of H has horizontal coordinate -a or b. Thus its norm is greater than 7/100 for every v and every original shared-side application in (1). No location of a completion unit was assumed in deriving this conclusion.

## 7. Literal positive-channel callers and the remaining geometric obligation

At a genuine unloaded positive-degree-two unit H, its full original force balance makes its two positive pair forces equal and opposite. In the width-one normal-channel alternative, the normals are the opposite own side axes of H. Its complete original torque then makes the two unchanged actual application means have the same transverse coordinate. After one rigid coordinate change, these facts give exactly (1).

This application uses all of H's actual forces and torque. It does not require either actual endpoint to have degree two. All actual endpoint force equations, corner coefficients and zero-weight physical contacts remain unchanged.

For the original D02.L0134 graph, the literal channel is

    W=0 -- H=5 -- B=4.

The positive rim is 01,12,23,34,45,50, and its unchanged positive chord is 02. The loaded units are 0,1,3,4. Thus 5 is genuinely unloaded degree two, W=0 retains its true loaded degree three, and B=4 retains its true loaded degree two with its actual boundary neighbor 3. In the side-channel alternative at 5, the theorem applies to all their actual support features and original means. The diagonal-channel alternative is a separate obligation.

The same local theorem is available at every genuine width-one boundary-to-boundary channel in any larger selected graph satisfying the displayed radius window. Its endpoint degrees, other spokes and loads do not enter the proof.

The strict center signs and vertex margin are useful inputs to geometric allocation arguments, but they do not alone establish them. In particular:

* A unique physical circle corner of an endpoint is not proved to have height at least h.
* No proper radial concurrence is asserted at a higher-degree endpoint.
* The actual exterior pocket is not automatically proved to lie in y>=h.
* An occupied pocket is not proved to force dist(O,H)<1/60.
* No original graph/load family or fine/coarse checkbox is declared closed.

These are real distinctions. The previously accepted simple-cycle proximity theorem uses actual endpoint properness in its opposite-corner escape comparison. The present theorem does not transfer that step to a three-force endpoint.

## 8. Exact sources, authorship and verification

All new geometric assertions and every scalar comparison are proved above. The following sources identify the unchanged physical conventions, the earlier port-margin argument whose scope is strengthened here, and the exact original graph join.

| Source | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original physical contact applications, complete force/torque equations and unloaded degree-two channel conventions |
| SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md | 0fa62f59c2b228d235a3e1539f9bbf8c3e53f7f128052064b8157819dcf06b4c | The earlier complete port-margin proof, printed anew in Section 6 after removing its endpoint-center-height premise |
| FOUR_C6_SIDE_OCCUPIED_CAP_TRANSMITTER_PROXIMITY.md | d227307250320a41e00e54e8aaa2c2475c2a3180a89bb23d52f4e6e1746a74ad | Scope boundary only: its stronger occupied-cap proximity is not invoked here |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original D02.L0134 graph, loads and true degrees |

The new full endpoint estimates and strict-center proof are authored here. The port-margin comparison in Section 6 preserves the existing proof's exact algebra, with its broader force-free entry established in Sections 2--5. No old review is transferred to these new bytes.

The displayed rational reserves were checked by exact fraction arithmetic only. No numerical pose search, angle mesh, optimizer, finite exclusion certificate, selected-normal change, force deletion, physical mask reduction, Lean compilation, CI, remote write or shared-ledger mutation is used.

