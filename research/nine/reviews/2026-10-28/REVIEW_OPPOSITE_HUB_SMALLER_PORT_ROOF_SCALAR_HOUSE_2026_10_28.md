# Independent full review of the opposite-hub smaller-port roof scalar bound

Date: October 28, 2026 UTC. Reviewer: house continuation.

**Result: PASS at the repaired frozen source**

OPPOSITE_HUB_SMALLER_PORT_ROOF_SCALAR_BOUND.md

SHA-256

4d45da08bee1d7c8de15a0eb9f8cb9d2f4dacb811f5e77e070037140882df535.

I read all ten sections, independently derived every derivative and continuous case reduction, and checked every displayed rational reserve. I did not contribute the scalar proof or its fixed-sum reduction. This is a separate review of the complete algebraic lemma, not author corroboration or a sampled evaluation.

## 1. Repairs found and current-byte readback

The first submitted version, 031c6459e1e4b10a591d760bc506a68ae7bda3af3614898625ad8868adc7c460, had two literal transcriptions which I reported before acceptance:

* In Section 8, K=v*c-S*s=0 implies c=S/r and s=v/r. The first version swapped these in its introductory sentence, although its following beta formula already used the correct order.
* In Section 4, the closed interval includes h=1/2, where S=S0. The correct statement is S>=S0>17/20, not S>S0 throughout.

Root repaired both. I reread the complete current source and verified the current hash above. The beta formula, all derivative calculations and all strict scalar reserves were unchanged. No further repair is required.

## 2. Entire original scalar domain and fixed-sum boundary reduction

The exact domain is

    sigma=1/sqrt(2), r=5/4,
    0<=X<=sigma, h>=1/2, 0<=phi<=pi/4,
    S=(X+h)/sqrt(2),
    v=sqrt(r^2-S^2)>=h,
    K=v*cos(phi)-S*sin(phi)>=0.

Thus v>=1/2, so every denominator used later is strictly positive. The weak endpoints X=0, X=sigma, h=1/2, phi=0, phi=pi/4, v=h and K=0 are all retained.

At fixed X+h and phi, S,v,K are fixed. Increasing X and decreasing h by the same amount preserves v>=h and the other domain conditions until X=sigma or h=1/2. The quantity N=X*c+h*s increases weakly because c>=s; N is nonnegative. Hence F=(1+N)^2+K^2 increases weakly along this whole path. This proves the exhaustive reduction to the two stated boundary intervals without choosing a physical configuration.

The phi=pi/4 endpoint has c=s, so the increase may be equality there. The later strict boundary estimates still give the required strict F<4 on the original domain.

## 3. The entire h=1/2 boundary

I independently expanded the derivative to obtain

    F_X/2
      =c+(X/2-1/4)c^2
        +(1/2-sigma*H)c*s+sigma*S*s^2,
    H=v-S^2/v<=v.

The dropped final term is nonnegative. The bracket in the resulting lower bound is at least 27/64>0. Thus F increases strictly with X.

This derivative estimate does not require K>=0 after its expansion. It consequently remains legitimate to bound the whole first boundary by X=sigma even if an intermediate enlarged comparison point were outside the original K constraint.

At the corner X=sigma,h=1/2, the source's S0^2 and v0^2 identities are correct. The bounds S0>17/20, v0>9/10 and sigma>7/10 imply C0<0 and L<43/100 at their required signs.

The expansion and its two sign-sensitive substitutions give exactly

    F<=43/16+(3/2)*sigma+L*s-(17/16)*s^2.

Because s>=0, replacing L by 43/100 is an upper bound whether or not L itself was separately known positive. The bound c<=1-s^2/2 and the strict sigma<17/24 are both valid on the entire angle interval.

Completing the square gives

    F<40306/10625<4,

with strict reserve 2194/10625. This covers every angle on the first boundary.

## 4. Exact h interval and all derivative identities on X=sigma

The condition v>=h on this boundary is precisely

    1/2<=h<=h_*,
    (1/2+sigma*h_*)^2+h_*^2=r^2.

The squared sum is strictly increasing for h>=0. The rational comparisons correctly give 29/40<h_*<3/4. Eliminating h_* gives

    3S_*^2-2S_*-17/16=0,

whose endpoint values -77/6400 and 1/200 prove 81/80<S_*<61/60. Throughout the closed interval, the repaired statement S>=S0>17/20 is correct, and 0<v<1 with v>=h>=1/2.

The quantity K decreases strictly with h, since

    K_h=-sigma*((S/v)*c+s)<0.

Thus K>=0 only shortens the interval at its upper end. Any nonempty admissible subinterval has the same lower endpoint.

I independently obtained the exact derivative identities

    F_h/2=s*(1+sigma*c+h*s)
            -sigma*(S*cos(2phi)+c*s*H),

    F_hh=4s^2-1+c*s*(3t+t^3),
    t=S/v,

and

    dH/dS=-(3t+t^3).

The ratio t increases strictly with h. Therefore F_h, as a function of h, is convex; at phi=0 its convexity is weak, which is enough for the endpoint comparison. This is a statement about F_h, not an erroneous assertion that F is convex in the low-angle range.

The derivative of F_h/2 with respect to phi is exactly

    c+sigma*(1-H)*cos(2phi)
      +2*(h+2*sigma*S)*c*s.

It is strictly positive on 0<=phi<=pi/12, since H<=v<1 and all other required signs hold.

## 5. Entire low-angle range

At phi=pi/12 the exact facts c*s=1/4, s<13/50, s^2<27/400 and cos(2phi)>173/200 are valid. The rational bounds on sigma include the strict lower bound 70/99.

At h=1/2, H is positive. Discarding its negative contribution is an upper bound, and the stated rational expression is exactly

    -613/15000<0.

At h=h_*, H is negative. The source bounds its positive contribution using

    -H<(2*(61/60)^2-25/16)/(29/40).

Both numerator and denominator are at their proved signs. The resulting complete upper bound is exactly

    -114011/13780800<0.

Convexity of F_h puts its value throughout [1/2,h_*] below the larger of its two negative endpoint values. Its strict increase with phi then proves F_h<0 for every smaller angle down to phi=0. Therefore F is bounded by its already treated h=1/2 value throughout the whole low-angle domain, including any K-truncated interval.

## 6. Entire high-angle range

For pi/12<=phi<=pi/4, one has s>1/4 and c*s>=1/4. The strict t>17/20 gives

    3t+t^3>25313/8000>3.

Thus F_hh>0 throughout the whole h interval. Convexity of F now bounds its maximum on the allowed subinterval by its endpoints. The lower endpoint is already covered. The only possible upper endpoints are h=h_* or K=0.

This is a complete angle and h cover. The common angle phi=pi/12 is included in both proofs, and no orientation or root of a derivative is numerically assumed.

## 7. Every K=0 endpoint

At the corrected endpoint,

    c=S/r, s=v/r,
    N=beta(h)=(sigma*S+h*v)/r.

The numerator's derivative is

    1/2+v-sigma*h*S/v
      >=1/2+v-sigma*S>19/80>0.

Thus beta increases on the entire closed interval. At h=h_*, the identity

    (3/2)h_*^2+sigma*h_*=21/16

gives the stated expression

    r*beta(h_*)
      =7/8+sigma/2+(1/2-2*sigma/3)*h_*.

The coefficient of h_* is positive because sigma<3/4. Using the strict h_*<3/4 gives r*beta(h_*)<r. Hence N<1 at every possible K=0 endpoint, and F=(1+N)^2<4.

The point K=0 is not omitted as a degenerate concurrence or geometric transition. It is proved directly at its exact scalar scope.

## 8. The remaining endpoint h=h_*

At h=h_*, the source's comparison N_phi>=K follows from

    N_phi-K=(S_*-sigma)*s>=0,

where S_*>81/80>sigma. Cauchy gives -K_phi<=r. Also N+1>=3/2>r.

Consequently

    F_phi/2>=K*(N+1-r)>=0

on the entire allowed interval. Its upper angular endpoint is K=0, strictly before pi/4 because h_*<S_*. Its value is already strictly below four. This bounds every earlier phi by the same strict value.

Together with the previous sections, this proves both full boundary intervals and hence the original complete domain.

## 9. Exact reserve checks

The following printed expressions were independently checked by rational arithmetic, in addition to the hand derivative and domain analysis:

| Comparison | Exact value |
| --- | --- |
| First-boundary derivative bracket | 27/64 |
| Corner bound | 40306/10625 |
| Corner reserve below four | 2194/10625 |
| Lower h_* squared reserve | 1771/184320 |
| S_* polynomial at 81/80 | -77/6400 |
| S_* polynomial at 61/60 | 1/200 |
| 1/2-(70/99)^2 | 1/19602 |
| (17/24)^2-1/2 | 1/576 |
| Lower h derivative endpoint bound | -613/15000 |
| Upper h derivative endpoint bound | -114011/13780800 |
| 3*(17/20)+(17/20)^3 | 25313/8000 |
| beta numerator derivative lower comparison | 19/80 |

These arithmetic checks confirm transcriptions. They do not replace the continuous monotonicity, convexity or endpoint arguments.

## 10. Decision and physical boundary of the review

**PASS at 4d45da08bee1d7c8de15a0eb9f8cb9d2f4dacb811f5e77e070037140882df535.** The theorem proves its entire strict scalar conclusion F<4, including all declared weak endpoints.

The source is self-contained and imports no physical geometry. A later caller must independently establish its actual X,h,phi, the roof constraints v>=h and K>=0, the relevant actual circle-corner comparison, and the complete occupied routing of extras. This review does not supply any of those missing physical joins, a capacity bound or an original family closure.

No new pose sample, numerical optimization, orientation mesh, Lean compilation, CI, workflow, ledger edit or remote action was used.

