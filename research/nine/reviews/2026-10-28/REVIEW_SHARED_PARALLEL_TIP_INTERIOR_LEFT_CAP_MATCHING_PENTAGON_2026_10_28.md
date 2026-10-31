# Independent review of the shared parallel-tip interior-port matching theorem

Date: October 28, 2026 UTC. Reviewer: pentagon continuation.

**Result: PASS at the complete stated geometric and conditional-capacity scope, with no repair requested.** The exact target is

    SHARED_PARALLEL_TIP_INTERIOR_LEFT_CAP_MATCHING.md
    SHA-256 620a56fcc734a5d6224e3b7edc3ed264e4cfef649e579cc992f4f9e41d5a23e4.

I read the entire new source and all three complete direct inputs at their current pinned bytes. I independently audited the new actual-port lower bound, every physical-circle-corner comparison, both full matching-angle estimates, the new uniform twenty-degree entry margin, and the conditional all-extra capacity argument. I recomputed twenty-six exact displayed identities and reserves, plus four further strict rational comparisons; all agree.

I authored the three older direct inputs listed in Section 7 below. This is an independent review of the new root-authored theorem and its exact use of those already separately reviewed results. It is not presented as a new independent review of my own earlier lemmas. In particular the present theorem has a different port interval and a weaker cap line than the wide-cap predecessor; I checked the new argument at that changed scope, without importing the predecessor's stronger geometric hypotheses.

## 1. Full domain and closed endpoints

The theorem keeps actual contained units and the unchanged disk origin. Its complete domain is

    2<=R<=sqrt(1105/256),
    V=[-x,1-x] x [y-1,y],
    1/2<=x<=1, y>0, x^2+y^2=R^2,
    P=(-a,y-2), 0<a<=x.

The actual terminal T is physically boundary and contains P as a minimum support point for a direction with both coordinates strictly negative. No true degree, force equation, selected contact owner, fixed-circle-weight pattern, or terminal orientation is assumed. The geometric theorem itself needs no normal selection.

The closed endpoints R=2, x=1 and a=x are explicitly retained. The physical two-circle V endpoint x=1/2 is part of the initial domain and is subsequently excluded by an actual diameter inequality. No endpoint is removed by continuity from an open theorem.

The conditional capacity conclusion separately requires every whole extra to lie in the actual half-plane x<=-a and to have the specified common angular lift between arg(Z_V) and theta_T+15 degrees. These routing premises are not asserted to follow from an arbitrary cap or graph.

## 2. Actual port length and all terminal physical corners

The full circle bounds give sqrt(3)<=y<121/60 and -7/25<y-2<1/60. The actual boundary T contains a circle corner at distance at most sqrt(2) from P, so

    |P|>=R-sqrt(2)>=2-sqrt(2).

This remains valid at R=2. The comparison sqrt(2)<99/70 gives the strict lower square bound 12/35. Subtracting the entire allowed vertical-coordinate square proves

    a^2>1/4+253/17500,

hence a>1/2 using the stated positive sign of a.

The whole alleged x<=9/16 interval is then excluded separately: its actual y is greater than 19/10, and a<=x gives a port squared norm below 81/256+1/100<12/35. This contradicts the preceding boundary-diameter lower bound. In particular both x=1/2 and x=9/16 are handled explicitly.

For any physical T circle corner with Z_x>=-a, the original support inequality forces its vertical displacement from P to be nonpositive. The equality Z_x=-a is included. The actual unit diameter, 1/2<a<=1, and the full height interval give

    |Z_x|<=1, |Z_y|<299/175.

The exact reserve

    4-[1+(299/175)^2]=2474/30625>0

then contradicts physical circle contact for every R>=2. Thus every physical T circle corner lies strictly left of the actual line x=-a. This includes all circle masks and all zero individual coefficients. The proof never moves P to the stronger line x=-x.

## 3. Center lift and both complete matching-angle comparisons

The actual center satisfies |c_T-P|<=1/sqrt(2), while its boundary status gives |c_T|>=R-1/sqrt(2)>181/140. The strict inequality survives at R=2 because the rational upper bound on 1/sqrt(2) is strict.

If the center's first coordinate were nonnegative, the complete port box would imply

    (c_T)_x<5/24, |(c_T)_y|<1,

contradicting the lower center radius by the exact reserve 5/8. Thus its angle has the ordinary left-half-plane lift in (90,270) degrees. The negative-height ratio 691/905<49/64<sin(50 degrees) proves theta_T<230 degrees. A nonnegative center height is separately immediate.

Both limiting angles phi_L and phi_B are well defined and strictly between 90 and 180 degrees. For every angle between 90 and their minimum, its actual radius-9/8 point lies in open V. At x=1 its horizontal coordinate is still strictly negative, and therefore strictly below the right side x=0; no open-endpoint assumption is needed.

The four height intervals proving theta_T-phi_B<100 degrees cover the whole domain and share their endpoints. I checked each center ratio, actual port lower bound, trigonometric branch, and strict bottom-face comparison. In particular the high interval independently forces R>101/50 by the exact reserve 7/625. It is not assumed at the lower endpoint R=2.

For the left-face comparison, the new port is exactly y-2. On the entire closed interval [9/16,1], the function v_0(x) is positive and below 4/5. Its inverse-sine derivative is strictly below 875/1161, whereas phi_L' is at least 8/9. The difference is exactly 157/1161>0.

At x=9/16 the comparison angle is strictly below 220 degrees and phi_L equals 120 degrees. The difference therefore remains strictly below 100 degrees throughout the whole remaining interval, including x=1. For R=2 the inequality theta_T<180+asin(v_0(x)) still has strictness from the actual circumradius comparisons. A nonnegative center height again gives the conclusion directly.

Thus both limiting angles satisfy the complete strict matching bound. These arguments reproduce the needed scalar comparisons on the present actual domain. They do not transfer the predecessor's a>x condition, its upper b bound in a different chart, or its stronger cap line.

## 4. The new twenty-degree entry estimate is uniform and strict

Write arg(Z_V)=90 degrees+alpha. Since x=R*sin(alpha), 0<x<=1 and R>=2, the entire domain is

    0<alpha<=30 degrees.

The actual radial point (9/8)Z_V/R lies in open V. Its horizontal coordinate is strictly between the actual sides, also at x=1. Its vertical drop from Z_V is at most R-9/8<1, since the stated upper radius is below 17/8. Therefore

    arg(Z_V)<min(phi_L,phi_B).

This is an actual interior point argument, not a force-line construction.

I checked all new elementary bounds and their branches. The triple-cosine cubic is strictly increasing at the compared positive cosine values. It proves cos(40 degrees)<77/100 and cos(20 degrees)<47/50 with the printed reserves. The sine lower bound follows by a strictly positive squared comparison. The lower cosine and square-root bounds are also strict.

For the whole interval 0<alpha<=20 degrees,

    sin(alpha+20 degrees)/sin(alpha)>=2*cos(20 degrees),

because cot(alpha)>=cot(20 degrees). Multiplying by rho gives a candidate horizontal magnitude strictly greater than R*sin(alpha)=x, using

    2*rho*cos(20 degrees)>135/64>25/12>R.

The middle reserve is 5/192. The candidate point is consequently outside the actual left side. All alpha in this interval, including alpha=20 degrees, are covered without a small-angle limiting argument.

For the complete interval 20<=alpha<=30 degrees, the function

    g_R(alpha)=R*cos(alpha)-rho*cos(alpha+20 degrees)

is positive, concave in alpha, and increasing in R. Its minimum on that interval is at least the smaller endpoint value at R=2. The exact endpoint reserves are

    g_2(20 degrees)>1+7/800,
    g_2(30 degrees)>1+521/80000.

Both are strict. The candidate point therefore lies below the actual bottom side throughout this entire interval. The common alpha=20 endpoint is covered twice, and alpha=30, which may arise at x=1 and R=2, is included.

These two complete intervals prove

    min(phi_L,phi_B)<arg(Z_V)+20 degrees.

Together with the strict lower entry bound and both matching estimates, they give a nonempty open interval in which phi can be chosen. Equivalently, choose phi between max(arg(Z_V),theta_T-100 degrees) and min(phi_L,phi_B), sufficiently near the latter. It is an actual point of open V and satisfies both strict conclusions of Theorem A.

No sampled physical orientation or approximate angle certificate is used in this step.

## 5. The conditional capacity argument uses the weaker cap correctly

Every whole extra satisfying the actual x<=-a routing premise has center first coordinate at most -a-1/2<-1. Thus its center radius exceeds one. T's center radius also exceeds one. The complete centered-forty-degree theorem consequently puts each relevant closed radius-9/8 arc of halfwidth twenty degrees in the corresponding actual open square.

The new entry margin is essential and is used correctly. If an extra center were at or before phi, the lower routing bound theta_E>=arg(Z_V) and phi<arg(Z_V)+20 degrees would put the actual V point phi inside the extra's closed centered arc. This would be an actual interior overlap. Hence every extra is strictly after phi, and the same argument strengthens the gap to more than twenty degrees.

The upper routing bound theta_E<=theta_T+15 degrees, together with strict forty-degree separation of the actual E and T centers, places every extra strictly before T. No stronger ordering is inferred merely from the cap line when a<x.

For two extras, all three successive gaps lie in the interval from phi to theta_T, whose length is strictly below 100 degrees. They are therefore genuine minor gaps. The first exceeds twenty degrees and the next two each exceed forty degrees, contradicting that matching bound. This proves capacity at most one for the full collection satisfying the stated routing premises.

The corollary retains actual whole squares. It neither assumes a graph pocket automatically has those premises nor replaces an original terminal mean or direction to make them true.

## 6. Exact endpoint and proof-boundary assessment

The following endpoint issues are all accounted for:

- R=2 retains every strict estimate needed for the theorem.
- x=1 preserves the open-V inner-point interval and the left-face derivative proof.
- a=x is permitted throughout; no strict predecessor condition is imported.
- x=1/2 and x=9/16 are excluded by the complete actual port-diameter comparison.
- Both alpha=20 and alpha=30 belong to the continuous entry-margin proof.
- Every shared height-interval endpoint retains strict matching inequalities.
- Z_x=-a is included in the terminal physical-corner contradiction.
- All terminal support owners, physical masks and individual circle coefficients are unrestricted.

I pass Theorem A and the complete conditional Theorem B exactly as written. This review supplies no original graph/load gate credit. A physical caller must still prove the original port formula, strict support signs, whole-cap containment, and common angular-routing interval from its unchanged geometry and full equations.

## 7. Complete source pins and verification record

| Complete source | SHA-256 | Exact operative scope checked |
| --- | --- | --- |
| ADJACENT_CIRCLE_TIP_WIDE_LEFT_CAP_INNER_ARC_MATCHING.md | 14ca7fbac82fb74b698ab17df01eb1783ce558e75fa8b5a528bbb8fb7bba76c1 | The continuous angle-comparison method and exact elementary comparisons, reproduced on the new port interval |
| PERPENDICULAR_HUB_W_OWNED_TWO_CIRCLE_TIP_CLOSING_POCKET_CAPACITY_ONE.md | cef7f26f395968b9d1a68f07bb531569ba12e72500cd23839ca9d4f97bf29923 | Exact elementary trigonometry only; no perpendicular chart or physical two-circle force equation |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | Closed centered arcs in actual open units, only in the conditional capacity theorem |

All three complete current files were read and their hashes matched. Twenty-six exact displayed identities and positive reserves, and four additional strict rational comparisons, were recomputed. These checks verify hand-algebra transcriptions; they are not a numerical packing search or an exclusion certificate.

The reviewed source remains unchanged. No Lean compilation, CI, workflow, force deletion, normal change, mean substitution, changed degree, shared ledger mutation, commit, remote write or new gate credit occurred.

