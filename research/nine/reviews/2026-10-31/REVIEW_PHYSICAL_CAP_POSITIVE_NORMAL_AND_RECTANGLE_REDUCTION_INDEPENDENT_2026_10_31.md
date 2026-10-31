# Independent hand review: physical two-square cap, rectangle reduction and nonnegative normal half

Date: October 31, 2026. Reviewer: branching continuation, independently reconstructing the root manuscript.

**Reviewed source:** `PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`.

**Scope:** complete Sections 2–4, including the separating-axis/support reduction, all triangle bounding-rectangle formulas, the four-row convexity table, both auxiliary convexity arguments, the large-weight diagonal-loss quartic, and all five ownership cases on `0<=c<=1`. This review does not certify the separate negative-normal half or the unrestricted extraction of four-plus-three chains.

**Verdict: PASS on the stated scope.** I found no mathematical error or uncovered endpoint. All calculations below were reconstructed by hand; no mathematical script, numerical sampling, interval program, Lean, or CI was used.

## 1. The physical separation and support signs are correct

For disjoint open rectangle interiors, the displacement of centers is outside the interior of their Minkowski difference. That difference is a convex polygon whose facet normals belong to the union of the two rectangles' own axes. Thus the source's actual separator

    n.(c_B-c_M) >= h_M(n)+h_B(n)

has an owner without assuming that the two frames agree. Boundary contact is included.

Adding the two actual circle support inequalities with vectors `-ae-kn` and `-be+kn` produces the center term

    -a e.c_M-b e.c_B+k n.(c_B-c_M).

Moving its last term to the other side and using the actual separation gives precisely the two **subtracted** quantities `P_M,P_B` in (6). Their signs are correct. If `R<r`, the subsequent replacement of `R(L_a+L_b)` by `r(L_a+L_b)` is strictly increasing because both lengths are positive.

## 2. Independent reconstruction of the rectangle lemma

For the triangle `0,we,-kn`, the sum of its two projection ranges in a frame equals the stated sum of three square supports: in each coordinate the three edge projections sum to zero, so half the sum of their absolute values is the coordinate range.

With fixed extreme vertices, the sum of the ranges is a positive expression `A cos(theta)+B sin(theta)`. Its second derivative is its negative, hence it is strictly concave on each nondegenerate interval of fixed extremes. Its minimum occurs at an interval endpoint. Such endpoints make a triangle edge parallel to a frame axis. Degenerate line triangles at `c=+-1` follow directly.

The three endpoint formulas were reconstructed as follows:

- In the `e` frame the longitudinal range is `w+k max(c,0)` and the transverse range is `ks`, giving `E_w`.
- In the `n` frame the longitudinal projections are `0,wc,-k`. Their ordering changes exactly at `c=0` and `c=-k/w`; adding transverse width `ws` gives all three printed branches of `N_w`.
- In the `we+kn` frame the extreme longitudinal projections are `0,w(w+kc)/L,-k(k+wc)/L`, and the transverse range is `wks/L`. Their ordering changes at `c=-k/w`, giving both printed branches of `D_w`.

Since `w>k`, the longitudinal length `L` never vanishes. When the actual square owns `n`, the value is exactly `N_w`, so the five inequalities in (8) are a complete ownership cover, not an assumption about an unowned frame.

## 3. Constants, derivatives and the four-row table

I independently checked

    L_a(0)^2=584545/256=529Q,
    L_b(0)^2=89505/256=81Q,
    H(0)=1105/8,  H'(0)=k/2,
    H(0)-(a+b+2k)=211/4.

The second derivative in (10) is correct. For `c>=23/24`, the sign `bc-k>=0` permits the printed bound on `L_b`, and hence (12). The endpoint bound (13) has upper value `6555/128<6752/128=T`.

For the functions `A=a^2k^2(s/L_a)^3` and `B=b^2k^2(s/L_b)^3`, the derivative numerator signs are exactly

    -(a+kc)(k+ac),  (b-kc)(k-bc).

Thus `A` decreases and `B` increases through `c0=23/24`. The lower radical bounds in the table are valid. For example the deliberately close last `L_b` bound has squared reserve

    11259/256-(53/8)^2=23/256>0.

Every printed rational comparison giving the table entries passes. The larger products in the most restrictive comparisons reduce to:

    5*7476000 < 8*4900172,
    80325000 < 9*9199872,
    5*2492000 < 3*4214784,
    71400000 < 11*6539203,
    4*165540000 < 758550528,
    14229000 < 12*1191016.

The last continuous bound is `B<=k^2/b=1587/128`, directly from `L_b^2>=b^2s^2`. All four row sums are below `38/3`; in the last row this is the integer comparison `4857<4864`. Therefore

    s^3 F'' >423/16-(133/64)(38/3)=11/96>0

is justified on the complete closed table interval, with the derivative argument used on its interior.

At `c0`, the source's particularly tight upper bound is also correct:

    (133/64)(62373/1000)=8295609/64000
        <8296000/64000=1037/8.

The reserve is `391/64000`. The subtracted expression is exactly

    [9131+141sqrt(47)]/128,

and `sqrt(47)>137/20` makes it greater than `631/8`, with reserve at least `17/2560`. Hence `F(c0)<203/4`, and the chord slope `48/23` in (16) is correct.

## 4. The other two convexity estimates

On the nonnegative half, `L_a>=a` and

    L_b^2-bk s^2=(b-k)^2+bk(1-c)^2>=0.

This proves the estimate `-s^3H''<315/8`. Both relevant coefficients, `a+k` and `a+b`, are larger than this bound, so (18) and (19) are convex on their stated intervals. Convexity extends to `c=1` by continuity despite the derivative singularity of `s` there.

Their endpoint evaluations and the strict upper bound `G(c0)<45` are valid. The resulting chord slope is

    (T-45)/c0=(31/4)(24/23)=186/23,

as printed.

## 5. The diagonal-loss inequality

Writing `Delta=L_a-a-kc` gives the exact identity

    E_a-D_a=k^2 cs/L_a-Delta(1-ks/L_a).

The source bounds the positive term above and the subtracted term below in the correct directions. Its coefficient comparisons

    k^2/a=1863/512<11/3,
    (1-k/a)k^2/[2(a+k)]=985527/965632>1

are correct.

For `s>=6/11`, squaring uses two nonnegative sides. Expanding gives exactly

    130s^4-132s^3-85s^2+132s-36.

The expansion about `s=3/4` has coefficients `81/128,9/8,227/4,258,130`, as printed. On the negative part of its shifted interval the two lower bounds are valid, including

    227/4-258(9/44)=175/44>0.

This proves `E_a-D_a<=2c` over the entire nonnegative half. At zero the separate strict inequality `D_a(0)>E_a(0)` follows from `(L-a)(L-k)/L>0`.

## 6. All five nonnegative ownership cases

Each case was checked against the correct branches of (7).

1. `N_a+E_b(-c)` is exactly (18). `N_a+N_b(-c)` is exactly `G` until `c0`; afterwards its coefficient of `c+s` is negative, so `c+s>=1` gives the endpoint bound (13).

2. `E_a+N_b(-c)` is exactly `F` until `c0`. Afterwards `c+s<5/4` and `r<25/12` give `9973/192<T`, as claimed. The bound on `c+s` follows from its decrease for `c>1/sqrt(2)` and `(23+sqrt(47))/24<5/4`.

3. `D_a+N_b(-c)` uses the valid loss bound `E_a-D_a<=2c`, leaving the positive reserve `(2/23)c` before `c0`. Beyond `c0`, the lower bound on `D_a` and coefficient estimates give `6723/128<T`. In particular the transverse coefficient comparison is the exact inequality `23391/5248<9/2`.

4. For `N_a+D_b(-c)`, the identity

       D_b(-c)-N_b(-c)=(L_b-k)(L_b-bs)/L_b

   is valid on `0<=c<=c0`. Its sign is nonnegative until `c=12/23`. On the remaining interval, `bs/L_b>3/4` bounds the possible loss by `k/4`. The `G` chord reserve exceeds this loss: `93/23>207/64`. All radicals are positive, and both transition endpoints are included.

5. For the final `c>=c0` portion of that same case, any triangle bounding-rectangle semiperimeter is at least the length `b` of its side. The resulting negative coefficient of `c+s` justifies the substitution `c+s>=1`, again giving (13).

Thus all five expressions in (8) are bounded by `T` on `0<=c<=1`. They are strictly smaller for `c>0`, and the two entries involving `D` are strictly smaller also at `c=0`. The frame-minimum reduction consequently has the exact strictness needed by the source's later equality argument on this half of the scalar domain.

## 7. Review boundary

This review checks a complete analytic half-domain and its common physical reduction. It assigns no original graph/load flag and does not infer a global chain extraction. The negative half requires its own verification. No source was altered to obtain the verdict, and no external computation was a proof premise.
