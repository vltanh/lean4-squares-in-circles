# Independent review of the three-fifths minus-corner ratio theorem

Date: October 28, 2026 UTC. Reviewer: house continuation.

## Verdict and exact frozen targets

**PASS: the complete new scalar theorem and its stated conditional physical join are correct. No repair is requested.**

| Complete source read | SHA-256 | Review scope |
| --- | --- | --- |
| THREE_FIFTHS_RATIO_BOUND_FOR_POSITIVE_DOT_MINUS_BOUNDARY_CORNER.md | 692044ebc896f0464fb2b9bf5d6ae07db38f8cfd7ab29054dd47bbcd5b554fdc | Entire source, all derivatives, the complete half-angle polynomial and every comparison endpoint |
| TERMINAL_HUB_AXIS_TIP_OWNED_POSITIVE_DOT_FULL_MASK_ENTRY.md | 1e9e597ad4b13995909cdac5d204b111d20ef305768fe6d44def11264e4a4c49 | Entire source, for the literal actual minus point and unchanged unique-V side/torque identities in Section 5 |

The new scalar argument was authored by root, with cycles' threshold suggestion and exact coefficient corroboration. I did not contribute its proof, its threshold, its monotonicity reductions or its polynomial. I independently rederived those steps for this review.

I authored the older physical-entry manuscript. This record does not claim an independent review of my own entry. Its complete separate independent review is REVIEW_TERMINAL_HUB_AXIS_TIP_OWNED_POSITIVE_DOT_ENTRY_CYCLES_2026_10_28.md, SHA-256 77623fdce8cb6d780ce745a788d52d21719bf796d4ba717954784a4ae14252c8. The new scalar theorem itself is self-contained and has no mathematical dependency on that entry. Below I check only that its precisely stated conditional invocation uses the actual displayed identities, without assigning the still-missing L bound to the entry.

## 1. Exact domain and the first comparison

The theorem assumes

    R>=2, X>Y>0, X^2+Y^2=R^2,
    K>0, L>=1/2, K^2+L^2=1,
    r=Y/X in (0,1),
    L/(L+Kr)<s<1,

and the circle equality for the specified minus point. It concludes r<3/5. No upper radius or terminal hypothesis is hidden in the proof.

K>0 implies L<1, while L>=1/2 implies K<=sqrt(3)/2<7/8. Both K and L are positive, hence K+L>1 and L>1-K. Direct subtraction gives exactly

    s0-(1-K)=K[L-r(1-K)]/(L+Kr)>0.

Thus A(s0)=s0+K-L>1-L>0. Throughout the full comparison interval from s0 to s,

    A(s)<1+K-L<11/8<sqrt(2)<X.

The original circle deficit is

    D(s;X,r)=2X[A(s)+r(1+K+L)]
                      -A(s)^2-(1+K+L)^2.

Its s derivative is strictly positive. Since the actual value is zero and the actual s strictly exceeds s0, D(s0;X,r)<0. The entire comparison uses scalar inequalities; no physical square, force or application is moved.

## 2. Complete ratio derivative

For an alleged r>=3/5, define

    A0=K-L+L/(L+Kr), B=1+K+L,
    X0=2/sqrt(1+r^2).

The coefficient A0+rB is positive, so the deficit increases in X. The radius lower bound gives X>=X0. The enlarged closed ratio interval [3/5,1] has X0>=sqrt(2)>11/8>A0>0, including its artificial r=1 endpoint.

I differentiated the complete expression before applying any estimates. The derivative is

    D0'/2=X0(B-rA0)/(1+r^2)+(X0-A0)A0',
    A0'=-LK/(L+Kr)^2>=-1/(4r).

The denominator inequality is the exact square (L-Kr)^2>=0. Also

    B-rA0>=B-A0=1+2L-s0>2L>=1.

Because 0<X0-A0<X0, multiplication by the negative derivative bound is in the correct direction. It follows strictly that

    D0'/2>X0/(1+r^2)-X0/(4r)>0.

The last sign holds on the entire interval: 4r-1-r^2 increases there and has value 26/25 at r=3/5. No unexamined interior ratio or L=1/2 endpoint remains.

## 3. Independent reconstruction of the boundary polynomial

At r=3/5, X0=10/sqrt(34)>12/7. The strict positive squared reserve is 2/833. Replacing X0 by 12/7 decreases the deficit, because its X coefficient was already proved positive.

The half-angle variable t=K/(1+L) covers the entire L>=1/2 domain:

    0<t<=1/sqrt(3)<3/5,
    K=2t/(1+t^2), L=(1-t^2)/(1+t^2).

All displayed denominators are positive. I independently reconstructed the common numerator before comparing it with the printed polynomial. With

    d1=1+t^2, d2=1+(6/5)t-t^2, d=d1*d2,

the numerators are exactly

    N_A=(4/5)t+(22/5)t^2-(4/5)t^3-2t^4,
    N_B=2(1+t)d2.

The polynomial I expanded was the actual cleared deficit

    (24/7)(N_A+(3/5)N_B)d-N_A^2-N_B^2.

Its nine coefficients agree term by term with equation (8). This independently checks the sign and scale of the negative square terms, as well as the two rational comparison constants.

The completed square in equation (9) is exact: its coefficient, center and positive remainder are respectively

    7404/875, 95/1851, 1192/12957.

After removing that quadratic, the remaining terms are exactly the cubic-bracket grouping in equation (10). Each negative monomial of the bracket is minimized over 0<=t<=3/5 at t=3/5. The resulting lower bound is exactly 179188/21875>0. The two remaining monomials have nonnegative coefficients and powers. Consequently the proof gives a strict positive polynomial on the whole enlarged closed interval, rather than only at selected orientations.

This proves D0(3/5)>0; the full derivative proves D0(r)>0 for every alleged r>=3/5. Monotonicity in X then contradicts the already strict negative comparison at s0. All signs and comparison directions agree.

## 4. Exact checks and their role

Standard rational arithmetic and polynomial multiplication were used only to verify the displayed continuous proof. In particular I reconstructed the numerator from the original rational expression; I did not merely evaluate the supplied polynomial at a set of points.

| Exact comparison | Recomputed value |
| --- | --- |
| (10/sqrt(34))^2-(12/7)^2 | 2/833 |
| 4r-1-r^2 at r=3/5 | 26/25 |
| (7/8)^2-3/4 | 1/64 |
| 2-(11/8)^2 | 7/64 |
| (3/5)^2-1/3 | 2/75 |
| Completed-quadratic minimum | 1192/12957 |
| Full negative-bracket endpoint lower bound | 179188/21875 |

The complete coefficient expansion and the completed-square equality were also checked exactly. These checks support the printed global derivative and positivity proof; no pose enumeration, sampled geometric point, numerical minimizer or computational certificate is a premise.

## 5. Literal physical invocation and remaining scope

The actual unique-minus entry supplies

    Z_W^-=(X-s+L-K,Y-1-K-L),
    s=1-tau, X>Y>1/2,
    rho=a-(L/K)(b+tau)=1-(Y/X)s.

Since a<1 and b>0,

    rho<1-(L/K)tau.

Substitution gives r*s>(L/K)(1-s), hence s>L/(L+Kr), precisely as needed. This argument does not borrow the plus-mask Y<1 result and does not assume Y>=1. A physical W tie remains included whenever its actual minus corner is on the circle.

The entry alone does not prove L>=1/2; the new source explicitly preserves that as a separate caller obligation. Therefore the theorem supplies the claimed ratio bound on the entire stated domain, but does not by itself close the minus physical feature, a terminal pocket or an original graph/load row.

All actual forces, masks, weights, original means, selected normals and true degrees remain. No higher-degree unit receives a two-force equation. No Lean compilation, CI, workflow, remote write, shared-ledger mutation or original count change was made in this review.

