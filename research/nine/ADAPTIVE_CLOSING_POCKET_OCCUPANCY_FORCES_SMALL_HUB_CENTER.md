# An occupied adaptive closing pocket forces the actual hub center inside radius three quarters

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed force-free geometric lemma, submitted for independent review.** This strengthens an adaptive capacity-one argument by retaining the actual hub as a competing centered arc. It needs no degree, force equation, owner classification or positive-component reduction. It does not yet prove a joint channel/central completion theorem.

## 1. Actual geometric hypotheses

Keep pairwise interior-disjoint actual unit squares U,V,T and a collection of actual further units E in the unchanged disk, with

    2<=R<=sqrt(1105/256).

The actual T physically touches the outer circle. Let rho=9/8. Work in an actual orthonormal coordinate frame about the same circle origin.

Assume the actual U is

    U=P+[-1,0]u+[-1,0]v,
    P=(-E0,D),
    u=(b,a), v=(-a,b),
    a,b>0, a^2+b^2=1,
    E0>0,
    1/sqrt(2)<D<61/60.                            (1)

The vectors u,v are an orthonormal positively oriented pair, so this is a full unit square. E0 is an actual coordinate, unrelated to the names of the additional units. The actual center is

    c_U=(-E0+(a-b)/2, D-(a+b)/2).                  (2)

Let theta_T be the canonical left-half-plane angle of the actual T center. Suppose there exist actual angles phi0,phi such that

    140<theta_T<270,
    phi0<135,
    phi0<phi<theta_T,
    theta_T-phi<100,                              (3)

and every radius-rho point with angle

    phi0<theta<=phi                               (4)

lies in the open interior of the actual V.

For each actual further unit E assume

    dist(0,E)>=1/6,
    phi0<theta_E<270,
    theta_E<=theta_T+40,                          (5)

where theta_E is its canonical left-half-plane center lift. In particular theta_E is also in(90,270). A proved whole cap x<=-q with q>=1/6 supplies the clearance; an actual occupied-pocket argument must supply the route and, when necessary, the lower entry in(5).

**Theorem.** If the collection contains even one actual further unit, then

    |c_U|<3/4.                                   (6)

The conclusion concerns the actual original hub, not a point assigned to an exterior unit. No whole-U cap assumption is needed.

## 2. Every hub with center radius at least three quarters has angle between135 and180

From a,b>0 and a^2+b^2=1,

    1<a+b<=sqrt(2), a-b<1.

Write c_U=(x_U,y_U) in the current frame. Equations(1)--(2) give

    0<y_U<61/60-1/2=31/60,
    x_U<1/2.                                     (7)

Suppose |c_U|>=3/4. If x_U>=0, the complete rectangle in(7) would give

    |c_U|^2<1/4+(31/60)^2
              =1861/3600<9/16,

whose exact positive reserve is41/900. This is impossible. Hence x_U<0 and y_U>0, so its unique angle theta_U lies in(90,180).

Moreover

    sin(theta_U)=y_U/|c_U|<31/45<1/sqrt(2).

The last strict squared comparison has reserve

    1/2-(31/45)^2=103/4050>0.

Sine decreases on(90,180), so

    135<theta_U<180.                              (8)

In particular theta_U>phi0 by(3), and theta_U<theta_T+40 because theta_T>140. The full hub center has therefore acquired the same relevant angle ordering as an additional pocket unit, without assigning the whole hub to that pocket.

## 3. All required centered arcs are actual interior arcs

Under the alleged |c_U|>=3/4, the complete center-radius theorem at the exact pin below gives the entire closed radius-rho arc

    [theta_U-20,theta_U+20]

inside open U. It requires only actual containment, unit geometry and this center-radius bound.

Every E has its entire closed centered halfwidth20-degree arc inside its open interior by the complete one-sixth-clearance theorem and(5).

The actual boundary T has clearance at least R-sqrt(2). Since R>=2 and sqrt(2)<3/2,

    dist(0,T)>=R-sqrt(2)>1/2>1/6.

Its entire closed centered halfwidth20-degree arc therefore lies in open T by the same theorem. These are arcs of the same radius rho; no claim about connectedness of the whole circle intersection is used.

The closed arcs of two different actual squares are disjoint, since the open square interiors are disjoint. Consequently their minor center separation is strictly greater than40 degrees. If a separation equalled40, a common endpoint of the two closed arcs would still lie in both open interiors and give a contradiction.

## 4. The hub and a putative extra compete in the same short interval

For either theta=theta_U or theta=theta_E, its center-direction radius-rho point lies in the corresponding open unit. Both directions exceed phi0 by(5),(8). If theta<=phi, equation(4) would put this same point in open V. Therefore

    theta_U>phi, theta_E>phi.                     (9)

If theta_U>=theta_T, equations(3),(8) give a nonnegative gap less than40. If theta_E>=theta_T, equation(5) gives a nonnegative gap at most40. Either contradicts the strict centered-arc separation from T. Thus

    phi<theta_U<theta_T,
    phi<theta_E<theta_T.                          (10)

Assume an actual E exists. Order the two different centers U and E in the interval in(10). Their separation is strictly greater than40, so the order is strict. The first center must be more than20 degrees after phi, because the actual radius point at phi belongs to open V and the first closed centered arc cannot contain it. The gap between the two centers exceeds40, and the gap from the second center to T exceeds40. All are minor gaps inside the interval of length less than100 from(3).

Their sum would be strictly greater than

    20+40+40=100,

contradicting theta_T-phi<100. Thus no E can exist when |c_U|>=3/4. This proves(6).

The proof keeps U as the same original unit and uses only its actual interior arc. It does not delete the hub, assign it an exterior region label, or suppose it obeys a whole-square cap that has not been proved.

## 5. Literal use with the existing adaptive point interval

For the actual V square

    V=[-Y,1-Y] x [D,D+1],

the two adaptive sources establish an interval of actual radius-rho points up to the smaller of the actual left-side and bottom-side limiters. The original low-Y theorem uses phi0=90. The high-Y extension uses phi0=100 after proving the actual right-side entry is smaller than100, including every allowed Y>=1. Both choices are below135, as required here.

Whenever a physical caller has the chart(1), the full actual cap/route, theta_T>140 and its adaptive strict angle comparison, it can choose phi in that actual V interval with theta_T-phi<100. Actual disjointness of V and T and the centered T arc ensure phi<theta_T; otherwise T's centered radius point would lie in open V. The established lower order of the extra centers supplies(5).

In the previously proved unique-plus terminal chart D>sqrt(3)-1>1/sqrt(2), E0=P0>1/5 and theta_T>142.5. In the unique-minus chart D>5/7>1/sqrt(2), E0=E>5/24 and theta_T>150. Both have D<61/60. The present local lemma therefore supplies an additional necessary condition whenever one of their actual closing pockets is occupied. Those complete original five-load features are already excluded for their three-extra budgets; this observation is intended for broader callers only after their own actual chart and angle premises are established.

The inequality |c_U|<3/4 does not imply dist(0,U)<1/40. No near-origin three-unit injection theorem, central capacity statement or joint channel allocation is inferred here. In particular, a higher-degree W does not acquire a degree-two properness equation through this lemma.

## 6. Complete operative sources

| Complete source | SHA-256 | Exact use |
| --- | --- | --- |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | The full actual hub's closed centered arc when its center radius is at least3/4 |
| ONE_SIXTH_CLEAR_UNIT_CENTERED_NINE_EIGHTHS_ARC.md | ae58afaf0564b403ab802bdc4ccb5f5a318013fd9aba778c6e4220e720aceb0a | Actual T and extra closed centered arcs from their true clearance |
| TERMINAL_PORT_ADAPTIVE_V_ARC_TWO_LIMITER_MATCHING.md | 8736d4890f2c4e7f12b5a5cb323f36e11c7646af1234391782413322d1ca7aff | Section5 only: the previously proved actual low-Y V interval and conditional angle hypotheses |
| TERMINAL_PORT_HIGH_Y_PROJECTION_ADAPTIVE_MATCHING.md | 33a45af35fe1ccdc07d05878810f311d161035ab98d6abd473f16babe46dd0a3 | Section5 only: the actual high-Y right-side entry below100 and complete conditional matching |
| TERMINAL_HUB_AXIS_TIP_OWNED_UNIQUE_PLUS_COMPLETE_POCKET_EXCLUSION.md | d4ac58913039370c12ec059c489e86620a3d635226ab12f4e339cab9bb12be87 | Section5 only: literal earlier unique-plus chart and theta_T>142.5 |
| TERMINAL_HUB_AXIS_TIP_OWNED_UNIQUE_MINUS_COMPLETE_POCKET_EXCLUSION.md | 91c286c7a01d1f6279e6349e24befe95767190a11dfb7ff68452e93c220c61a9 | Section5 only: literal earlier unique-minus chart and theta_T>150 |

The force-free theorem in Sections1--4 needs only the first two sources; the other four verify the stated optional physical substitutions. No original fine or coarse flag is changed by this lemma. No physical pose, force, mean, degree, normal, mask or square is modified, and no Lean compilation, CI, numerical sampling, remote write or ledger change is part of its proof.
