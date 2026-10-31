# An occupied adaptive closing pocket forces the actual hub within one sixth of the origin

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed force-free geometric strengthening, submitted for full independent review.** The actual hub need not lie in the exterior pocket. No order between its two positive axis coefficients is assumed. The result controls the distance of the whole unchanged hub from the same circle origin, in addition to the earlier center-radius bound. It does not assert the stronger near-origin threshold required by the existing three-unit injection.

## 1. Complete actual hypotheses and conclusions

Keep pairwise interior-disjoint actual unit squares U,V,T and a collection of further actual units E in the unchanged disk centered at O=0, with

    2<=R<=sqrt(1105/256), rho=9/8.

T physically touches that circle. In an orthonormal frame about the same origin, suppose the full actual hub is

    U=P+[-1,0]u+[-1,0]v,
    P=(-E0,D), u=(b,a), v=(-a,b),
    a,b>0, a^2+b^2=1, E0>0,
    1/sqrt(2)<D<61/60.                              (1)

Thus its actual center is

    c_U=(-E0+(a-b)/2, D-(a+b)/2).                   (2)

Retain the complete adaptive angular hypotheses:

    140<theta_T<270,
    phi0<135,
    phi0<phi<theta_T,
    theta_T-phi<100,                                (3)

where theta_T is T's canonical left-half-plane center angle. Every point of the radius-rho circle with

    phi0<theta<=phi                                 (4)

lies in open V. For every additional actual E, its canonical left-half-plane center angle and actual distance satisfy

    dist(0,E)>=1/6,
    phi0<theta_E<270,
    theta_E<=theta_T+40.                            (5)

These are the same physical premises as the earlier center-radius theorem. A real whole cap may supply the clearance in (5), but no such cap is imposed on U.

**Theorem.** If at least one actual additional E exists, then simultaneously

    |c_U|<3/4,
    dist(0,U)<1/6.                                 (6)

The first conclusion is the earlier theorem at its exact pin below. The second is proved here. We also obtain the following independent geometric implication, requiring only the chart (1):

    E0<=D-b  ==>  dist(0,U)<1/40.                  (7)

Equivalently, if the actual U has distance at least1/40 from O, then its center has ordinary angle strictly between135 and180 degrees. The zero-center case cannot occur because the center's vertical coordinate is strictly positive.

## 2. The entire non-leftward-angle chart is within one fortieth of O

Put

    w=a+b, y=D-w/2.

Since 1<w<=sqrt(2), the full chart gives

    0<y<31/60.                                     (8)

In the actual orthonormal u,v coordinates, P has projections

    p_u=P.u=aD-bE0,
    p_v=P.v=bD+aE0.

Consequently the entire actual square has own-coordinate intervals

    [p_u-1,p_u] times [p_v-1,p_v].                 (9)

Suppose E0<=D-b. This assumption is merely the scalar alternative now being bounded; it is not imposed on an original mean or on a physical caller. First,

    p_u>=aD-b(D-b)
        =b^2-D(b-a)
        =1/2-(b-a)y
        >-1/60.                                   (10)

To check the last strict comparison on the entire orientation domain, if b-a<=0 the middle expression is at least1/2. If b-a>0, use b-a<1 and (8) to get a value greater than1/2-31/60=-1/60. Thus neither a>=b nor its strict version is needed.

Also E0>0, b>0 and a<1 give

    p_u<aD<D<61/60.                               (11)

The other projection is positive because every term of bD+aE0 is positive. Its upper bound is

    p_v<=bD+a(D-b)=wD-ab
        <(61/60)w-(w^2-1)/2
        =1/2+(61/60)^2/2-(w-61/60)^2/2
        <=7321/7200.                               (12)

The identity 2ab=w^2-1 is exact. The completed square is a bound for every real w, so no missing orientation interval or endpoint is being optimized numerically.

For an interval [p-1,p], its distance from zero is max(-p,p-1,0). Equations (10)--(12) therefore imply that the first own-coordinate distance is strictly less than1/60 and the second is strictly less than121/7200. Orthogonality in (9) gives

    dist(0,U)^2
       <1/3600+(121/7200)^2
       =29041/51840000
       <1/1600.                                   (13)

The exact last reserve is

    1/1600-29041/51840000=3359/51840000>0.

This proves (7), including every actual own-coordinate side or vertex nearest to O. No nearest point is selected in advance.

## 3. A hub at distance at least one sixth has the needed angular route

Suppose for contradiction that an E exists and dist(0,U)>=1/6. Since 1/6>1/40, Section2 forces

    E0>D-b.

Using (2),

    (c_U)_x+(c_U)_y=D-E0-b<0,
    (c_U)_y=y>0.

Hence (c_U)_x<-(c_U)_y<0, and its unambiguous second-quadrant center angle satisfies

    135<theta_U<180.                               (14)

This derivation uses the distance alternative, not a lower bound on |c_U|. In particular it covers the small-center regime not handled by the earlier center-radius argument.

Equations (3),(14) give theta_U>phi0 and theta_U<theta_T+40. Thus U has the same relevant angular route as an additional pocket unit, although it has not been assigned to the pocket and is not assumed to obey a whole-square cap.

## 4. The closed arcs force the same strict 100-degree contradiction

Under the alleged dist(0,U)>=1/6, the complete one-sixth-clearance theorem gives the entire closed radius-rho arc of halfwidth20 degrees centered at theta_U inside open U. It gives the same actual closed arcs for every E by (5).

T has actual distance at least R-sqrt(2)>1/2 from O, because it contains a physical radius-R point and its diameter is sqrt(2). Thus the same theorem gives T's closed centered arc inside open T, with every physical circle mask and individual zero weight retained.

Two such arcs cannot share an endpoint: every point of each closed arc lies in its square's open interior. Therefore the minor angle between any two of their center directions is strictly greater than40 degrees.

For U and E, their radius-rho points in their own center directions lie in their open interiors. Both directions exceed phi0. If either were at most phi, (4) would put that point in open V. Hence

    theta_U>phi, theta_E>phi.

If theta_U>=theta_T, its upper route gives a gap less than40; if theta_E>=theta_T, (5) gives a gap at most40. Either is a minor gap contradicting the strict separation from T. Thus

    phi<theta_U,theta_E<theta_T,
    theta_T-phi<100.                               (15)

Order U and one actual E in that ordinary interval. The first center is more than20 degrees after phi, since otherwise its closed arc would contain the actual open V point at phi. Their mutual gap is more than40 degrees, and the last center is more than40 degrees before T. Every one of these is a minor gap inside the interval shorter than100. Their sum would exceed

    20+40+40=100,

contradicting (15). This proves dist(0,U)<1/6. The complete earlier center-radius theorem applies to precisely (1)--(5), proving the other part of (6).

## 5. Exact scope and the remaining injection gap

The theorem uses no force equation, degree, load, normal ownership, application mean or source of the actual adaptive hypotheses. It preserves every actual square and the original origin. In particular no three-force hub or higher-degree endpoint is turned into a transmitter.

The former unique-plus and unique-minus callers already audited for the earlier theorem supply exactly (1)--(5), so both conclusions (6) hold whenever their actual closing pocket is occupied. Those already closed five-load families receive no further original flag credit. A new caller must establish its own whole cap, actual angle interval, route and chart before using this result.

Equation (7) is conditional on E0<=D-b. Pocket occupancy alone does not prove that condition. The present theorem therefore does **not** assert dist(0,U)<1/40 merely from occupancy, nor a three-unit near-origin injection, a joint channel/central capacity, or a whole original graph/load closure. Those stronger conclusions remain separate proof obligations.

## 6. Complete direct pins

| Complete source | SHA-256 | Exact use |
| --- | --- | --- |
| ONE_SIXTH_CLEAR_UNIT_CENTERED_NINE_EIGHTHS_ARC.md | ae58afaf0564b403ab802bdc4ccb5f5a318013fd9aba778c6e4220e720aceb0a | Entire closed centered arcs for actual U, T and E under their genuine clearance bounds |
| ADAPTIVE_CLOSING_POCKET_OCCUPANCY_FORCES_SMALL_HUB_CENTER.md | 182705c297ed3a52a525206b673b293dff1cc7cf6de76430fad52ed1797b1e3d | Identical complete physical premise, earlier strict center-radius conclusion and previously audited optional caller scope |

The coordinate box, completed square and exact rational reserve in Section2 are proved above. Exact arithmetic corroborates the displayed fractions; no pose search, numerical exclusion, normal adjustment, force deletion, Lean compilation, CI, shared-ledger change or remote write is part of this proof.
