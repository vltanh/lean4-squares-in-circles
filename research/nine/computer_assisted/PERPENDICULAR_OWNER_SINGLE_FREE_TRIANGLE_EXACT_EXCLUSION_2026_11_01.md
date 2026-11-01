# Perpendicular-owner, one-free-internal-edge triangle: exhaustive exact exclusion

November 1, 2026. PR #11 continuation. **Evidence at construction: X; independent proof review and replay requested.** The executable checker uses exact rational interval arithmetic and integer square-root bounds only. No floating-point or numerical-optimizer result is used as proof, and no Lean, Lake or CI is run.

**Result.** The complete physical chart specified below forces

    R > 25/12,
    R² > 625/144 > Q=1105/256,
    625/144-Q=55/2304.

The proof has three complete root regions: one analytic corner rectangle and two compact exact interval rectangles. The latter require only **898 tree nodes**, **441 certified variance leaves**, and **9 empty-order leaves**, with maximum depth 15. There are no unresolved leaves. This closes the whole displayed physical feature, not merely a sampled angle set.

## 1. Original physical chart, owner hypotheses and precise scope

Keep the same nine actual interior-disjoint unit squares in one disk with center O and radius R and their unchanged selected physical force-and-torque certificate. Let A,B,C be entirely circle-unloaded, with the three original positive internal edges AB,AC,BC and exactly one original positive outside edge at each. The outside terminals may repeat and have arbitrary frames, loads, other forces and circle masks.

This theorem concerns the distinct-singleton physical chart in which the AB contact is free vertex/vertex, C owns the AC and BC normals on two perpendicular side axes, and the A and B outside exits have their indicated own-axis normal directions. The separate owner and geometric reductions establish when an original surviving triangle has this chart; this source proves its complete radius obstruction.

After a rigid motion and relabeling, write

    C=[0,1]²,
    p_A=(1,s), p_B=(t,1),   0<s,t<1,
    0<alpha<beta<pi/2,
    u_A=(cos(beta),sin(beta)), v_A=(sin(beta),-cos(beta)),
    u_B=(cos(alpha),sin(alpha)), v_B=(-sin(alpha),cos(alpha)),
    A=p_A+[0,1]u_A+[0,1]v_A,
    B=p_B+[0,1]u_B+[0,1]v_B.

The original AB application is the actual common vertex

    P=p_A+u_A=p_B+u_B.

Therefore the actual contact positions are exactly

    t=1-cos(alpha)+cos(beta),
    s=1+sin(alpha)-sin(beta).

Both lie strictly between zero and one. The complete C translation makes its outside normal Southwest, so its original application is `(0,0)`. Its full torque at that corner equates the two perpendicular internal moments. After a common positive rescaling of this original local stress, the C-to-A vector is `(t,0)` and the C-to-B vector is `(0,s)`. No normal or application is reselected. The C outside vector is `(-t,-s)`.

At A and B, the original positive outside vectors are `z_A v_A` and `z_B v_B`, respectively. Their original applications retain the complete own-side means

    q_A=p_A+v_A+tau_A u_A,  0<=tau_A<=1,
    q_B=p_B+v_B+tau_B u_B,  0<=tau_B<=1.

Both original applications and all their endpoint possibilities are retained until the full torque equations determine them below.

## 2. Complete force and moment elimination

Summing the unchanged A and B full translations cancels their original AB force and gives

    z_A v_A+z_B v_B=(t,s).

Let `Delta=sin(beta-alpha)>0`. Solving this exact two-dimensional system gives

    z_A=(t cos(alpha)+s sin(alpha))/Delta,
    z_B=(t cos(beta)+s sin(beta))/Delta.

Both denominators of the corresponding inverse expressions are strictly positive. The original AB force remains the vector `(t,0)-z_A v_A`; it is not set to zero or replaced by a limiting force.

Take A's complete torque about its unchanged AB vertex P. The C force contributes `-t sin(beta)`. The original outside force contributes `(1-tau_A)z_A`, because `det(u_A,v_A)=-1`. Thus

    tau_A=1-t sin(beta)/z_A.

At B, the C force contributes `s cos(alpha)` and the outside force contributes `(tau_B-1)z_B`, since `det(u_B,v_B)=1`. Hence

    tau_B=1-s cos(alpha)/z_B.

Cancelling Delta before any interval evaluation yields the exact rational expressions

    tau_A=1-t sin(beta) Delta/(t cos(alpha)+s sin(alpha)),
    tau_B=1-s cos(alpha) Delta/(t cos(beta)+s sin(beta)).

This cancellation permits continuous enclosures at alpha=beta. That enlarged boundary is used only as an overapproximation of the strict original angle domain; no finite physical stress is asserted to exist there.

## 3. Three actual outside points and the exact variance obstruction

If q minimizes a unit direction e on an actual unit square, then q+e remains in that square: in each own coordinate it moves inward from its minimizing endpoint by at most one. This includes all original side means and both endpoints.

Thus the unchanged outside neighbors contain the following actual points of the same original disk:

    w_A=p_A+2v_A+tau_A u_A,
    w_B=p_B+2v_B+tau_B u_B,
    w_C=(-t,-s)/sqrt(t²+s²).

In components,

    w_A=(1+2 sin(beta)+tau_A cos(beta),
         s-2 cos(beta)+tau_A sin(beta)),
    w_B=(t-2 sin(alpha)+tau_B cos(alpha),
         1+2 cos(alpha)+tau_B sin(alpha)).

The third point is a unit vector in the closed negative quadrant. Its denominator is positive at every original strict angle pair.

For any three points in a disk, the exact mean-square identity gives

    R² >= V := (|w_A-w_B|²+|w_B-w_C|²+|w_C-w_A|²)/9.

Indeed their average squared distance from O equals the squared distance of their mean from O plus V. Consequently an exact lower enclosure `V>625/144` excludes the physical chart at every radius `R<=25/12`.

## 4. Exact rational charts and exhaustive root coverage

Set

    p=tan(alpha/2), q=tan(beta/2).

All original angle pairs lie in `0<p<q<1`; the checker encloses the larger closed triangle `0<=p<=q<=1`. The trigonometric quantities become exact rational functions:

    cos(alpha)=(1-p²)/(1+p²), sin(alpha)=2p/(1+p²),
    cos(beta) =(1-q²)/(1+q²), sin(beta) =2q/(1+q²),
    Delta=2(q-p)(1+pq)/((1+p²)(1+q²)).

Their chart denominators are strictly positive. Sine of the half-angle chart is increasing on [0,1], cosine is decreasing, and Delta is bounded by its angle-difference endpoints inside `0<=alpha<=beta<=pi/2`.

The three **closed** root rectangles are

| Root | p interval | q interval | Whole-region method |
| --- | --- | --- | --- |
| Analytic corner | [0,1/20] | [10/11,1] | Two coordinate bounds and the negative unit point |
| Low-p compact part | [0,1/20] | [0,10/11] | Exact rational interval variance |
| Remaining-p part | [1/20,1] | [0,1] | Exact rational interval variance, restricted by p<=q |

Their union contains the entire closed ordered triangle; duplicated boundary faces cause no problem. The only point where t and s both vanish is `(p,q)=(0,1)`, wholly contained in the analytic corner. Everywhere on the two compact roots subject to p<=q, t and s are positive and the two cancelled mean denominators and `sqrt(t²+s²)` are strictly positive. The checker never divides by an interval containing zero: it subdivides until strict positivity is proved.

The proof uses `0<=tau_A,tau_B<=1` exactly as original support-mean conditions. Interval intersections with [0,1] retain every physically allowed mean; if an interval were disjoint from [0,1] the corresponding physical chart would be empty. In this actual run all nine empty leaves are solely from the order condition `p>q`; no mean-based empty leaf was needed.

## 5. Uniform analytic exclusion of the singular corner

On the analytic rectangle,

    sin(alpha)<=1/10,
    cos(beta)<=cos(2 atan(10/11))=21/221<1/10.

Since a nonnegative unit coordinate is at least its square, this implies

    cos(alpha)>=99/100, sin(beta)>=99/100.

The original side means are nonnegative, so the actual outside points satisfy

    w_A,x>=1+2 sin(beta)>=149/50,
    w_B,y>=1+2 cos(alpha)>=149/50.

Suppose R<=25/12. The actual disk center O=(h,k) must then satisfy

    h,k >=149/50-25/12=269/300 >0.

Write `w_C=(-u,-v)` with u,v>=0 and u²+v²=1. Then u+v>=1, whence

    |w_C-O|²=h²+k²+1+2(hu+kv)
       >=2(269/300)²+1+2(269/300)
       =625/144+5497/90000 >R².

This is a contradiction throughout the entire corner region, irrespective of the ratio t/s or of the two original side means. The enlarged undefined corner point needs no arbitrary value of `(-t,-s)/sqrt(t²+s²)`: the proof permits every negative-quadrant unit point there, thereby covering all original strict approaches and all their directional limits.

## 6. Exact arithmetic kernel and finite coverage

The checker [verify_perpendicular_single_free_triangle.py](verify_perpendicular_single_free_triangle.py) implements rational closed intervals with `fractions.Fraction`. Addition, subtraction, products, squares and positive-denominator reciprocals are bounded outward by exact arithmetic. Orientation ranges use the exact endpoint monotonicity just stated.

For a rational radicand interval it computes the lower floor and upper ceiling square roots on denominator `2^18`, using integer `isqrt` and exact comparisons of the resulting rational squares. An explicit check requires `lower²<=radicand_lower` and `upper²>=radicand_upper`. No approximate square root is trusted.

Every variance-certified leaf encloses the three original outside points whenever its original hypotheses are feasible, sums lower bounds on their six squared coordinate differences, and proves V strictly greater than 625/144. Such a leaf need not contain a feasible physical configuration. Otherwise a box is bisected exactly at a rational midpoint in its wider coordinate; **both** closed children are included. A box is never discarded because of numerical infeasibility or small width. Exceeding a resource limit raises `UNRESOLVED` rather than success.

The complete emitted [split-tree certificate](perpendicular_single_free_triangle_certificate.json) contains the root rectangles, every split axis and rational midpoint, the full binary addresses, and all leaf boxes/reasons/exact variance bounds. Thus the arithmetic result can be replayed from source or checked from the explicit finite tree, without trusting the split heuristic.

## 7. Reproduction and compact exact summary

From the repository root:

    python research/nine/computer_assisted/verify_perpendicular_single_free_triangle.py --certificate research/nine/computer_assisted/perpendicular_single_free_triangle_certificate.json

The checker has no third-party dependencies.

| Compact root | Tree nodes | Strict variance leaves | Empty-order leaves | Maximum depth |
| --- | ---: | ---: | ---: | ---: |
| Low-p below analytic corner | 143 | 72 | 0 | 10 |
| Remaining p | 755 | 369 | 9 | 15 |
| **Total compact cover** | **898** | **441** | **9** | **15** |

Every compact variance leaf has exact certified reserve greater than `1/6000` above 625/144; the smallest raw fraction is retained in the certificate. The analytic root has the independent exact reserve `5497/90000`. The three-row summary is a summary of one analytic proof and 441 exact arithmetic rejection leaves, not a claim that all three rows are independent handwritten inequalities.

## 8. Join and evidence boundary

This proves a complete original physical chart exclusion with all three full internal forces, all three actual positive outside exits, the original support means, strict interior angle domain, every closed boundary needed for exhaustive enclosures and all repeated terminal identities retained. It is uniform in every compatible outside placement; it does not require a separately optimized or fictitious continuation square.

The original chart classification and same-selected-certificate owner reduction must be supplied by the caller. This source does not infer that every remaining distinct-singleton triangle has this owner mask. Other owner masks and the later original nine-square parent joins retain their own obligations.

At construction the exact checker and complete split tree have been generated successfully, but independent mathematical review of this physical transfer, interval kernel and root cover is still requested. This is an exact computer-assisted proof at the stated feature scope, not a Lean proof and not an automatic change to the canonical original parent/fine counts.
