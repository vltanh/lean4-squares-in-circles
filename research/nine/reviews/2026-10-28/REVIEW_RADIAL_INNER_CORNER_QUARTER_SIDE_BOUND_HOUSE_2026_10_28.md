# Independent review of the full-radius radial inner-corner quarter-side bound

Date: October 28, 2026 UTC.
Reviewer: house.
Decision: **PASS at the complete stated scope and exact source bytes.**
No source repair was required.

## 1. Exact object and independent scope

Reviewed manuscript:

- RADIAL_INNER_CORNER_BOUNDARY_NEIGHBOR_QUARTER_SIDE_BOUND.md
- SHA256: 37f0f207a86a9d2c4ead42edcfaac01c5dbdd4f08bc66e98e41f985adedc4011.

I read the complete self-contained proof and independently checked its physical frame and side endpoints, full physical W mask, exact circle equation, all three derivative signs, all three continuous scalar intervals, and the radius entry.

The root-authored new conclusion is a force-free bound for the actual whole W in the printed chart. The mask calculation is also the one printed in the separately reviewed perpendicular physical-two-circle proof; the new all-beta scalar argument here is independent of that proof's V force inequality. No latter force inequality, graph, other-square geometry or coefficient premise is imported.

The exact conclusion is beta*gamma<1/4 for d>11/12 and the complete closed quarter-circle frame and side parameter. It has no upper-radius bound. The conditional unique-corner statement applies to the open frame with beta>0, exactly as stated.

## 2. Complete weak endpoints and actual mask

If beta=0 or gamma=0, the desired product is zero. These endpoints require no unproved unique physical mask.

If eta=0, then gamma=1. The actual rectangle has |x|<=3/2 and |y|<=d because d>1/2. Its maximum squared radius is at most d^2+9/4, strictly below the prescribed R^2 by 2d-1>0. This excludes the whole endpoint frame directly.

In the remaining open quarter-circle frame, beta>0 gives 0<=tau<1, retaining beta=1. I independently derived the two actual own center coordinates. The f-coordinate is strictly positive since eta>1-gamma and d>1/2.

If the g-coordinate were nonpositive, the actual top corner would be a farthest corner, including a tie. Its displayed deficit decreases strictly with tau. At tau=1 the alleged g-center sign makes that deficit nonnegative, so at the actual tau<1 it is strictly positive. A farthest corner of a contained boundary square cannot be strictly inside the circle. Hence both own center coordinates are positive.

The physical farthest corner is therefore uniquely M+tau*f+g. Expanding that actual point gives exactly equations (5)--(6), with a strictly positive denominator. No physical mask or positive coefficient was assumed to get this circle equality.

The final observation about beta=1 via tau=0 is valid in this continuing open-frame case. The weak aligned frames have already been handled for the theorem's product conclusion, so there is no endpoint gap in the stated theorem.

## 3. The three monotonicities

For the actual function F(gamma,tau), differentiating in tau gives the printed strictly positive numerator.

Differentiating along eta=sqrt(1-gamma^2), then multiplying by eta, gives exactly

    tau*(1-tau)*eta-(1+tau^2)-(1+tau^3)*gamma.

It is strictly negative on the entire enlarged rectangle 0<gamma<1, 0<=tau<=1: the first term is at most 1/4 and the second subtraction is at least one. The denominator remains positive even at tau=1.

For the algebraic eta comparison with gamma,tau fixed, the numerator of the eta derivative is D+tau*N>0, where D=1+gamma-tau*eta and N=tau^2+tau*gamma+eta. All three eta enlargements in Section 5 retain positive denominator. They are scalar bounds, not changes to an actual W frame.

## 4. Complete alleged-product domain and exact upper bounds

Under beta*gamma>=1/4, the original beta<=1 gives gamma>=1/4, and tau<=1-1/(4gamma). The following intervals exhaust every possibility:

| Entire gamma interval | Valid tau upper bound | Algebraic eta enlargement after lowering gamma | Resulting exact F upper bound |
| --- | --- | --- | --- |
| [1/4,1/2] | 1/2 | eta<1 at gamma=1/4 | 11/12 |
| [1/2,2/3] | 5/8 | sqrt(3)/2<7/8 at gamma=1/2 | 101/122 |
| [2/3,1) | 3/4 | sqrt(5)/3<3/4 at gamma=2/3 | 87/106 |

I checked the directions of both monotone substitutions. Increasing tau and decreasing gamma give an upper bound even when the resulting comparison pair is outside the original product domain. That enlargement is legitimate and explicitly scalar.

Each subsequent eta comparison is strict. The first ratio is exactly 11/12. The latter two have exact positive reserves

    11/12-101/122=65/732,
    11/12-87/106=61/636.

The radical comparison sqrt(5)/3<3/4 has squared reserve 1/144. The corresponding sqrt(3)/2<7/8 comparison is also strict by squaring. Both shared interval endpoints are covered. Every alleged product at least 1/4 therefore gives d<11/12, contradicting the strict hypothesis.

This proves the full continuous theorem. There is no finite orientation check, omitted interval, or unproved endpoint optimization.

## 5. Radius entry and exact limits

At every R>=2, the prescribed d satisfies d>=sqrt(15)/2-1. Comparing its positive shifted coordinate with 23/12 gives squared reserve 11/144, so d>11/12. The R=2 endpoint is included.

The theorem still requires a caller to derive the actual chart with the actual point M and physical W boundary status. It does not apply to an arbitrary unnamed boundary neighbor merely because a radial square is present. The other radial square is not itself a hypothesis of this geometric lemma.

No force, circle coefficient, normal selection, original mean substitution, graph degree, extra-square placement, radius upper bound or same-nine lower-radius theorem is used. The source is self-contained and proves the statement for every contained actual W in its displayed chart. It supplies a uniform support restriction, not a whole original graph/load closure.

The review used hand differentiation and exact rational identities only. No sampled pose, numerical optimization, angle grid, computational exclusion certificate, Lean compilation, CI, remote write or shared-ledger edit was performed.

