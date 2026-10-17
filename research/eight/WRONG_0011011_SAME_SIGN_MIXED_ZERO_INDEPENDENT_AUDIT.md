# Independent audit: wrong 0011011 same-sign mixed zero-quarter theorem

**Result: PASS.** The whole continuous argument, its 32-case cover, and a
fresh exact replay of all 126 strict comparisons have been reviewed.
This is an independent review by the global_attack agent; the proof
sources were not modified.

## Bound sources

| File in proof_integration | SHA-256 |
|---|---|
| WRONG_0011011_SAME_SIGN_MIXED_ZERO_HAND_PROOF.md | f95575cadcefe37e3035365c9c672d9f1ba72e393f062e112a5963f3ea74b587 |
| verify_wrong_0011011_same_sign_mixed_zero_hand.py | 9aab2def1b3f514ee3f84588395dbf143034e51d65d20f02c182b991d5d07b79 |
| wrong_0011011_labels.json | a4349b3d463bf9e67ecbb86f575c4d15df059d12c195b84eddceab85463eef6d |
| wrong_0011011_same_sign_mixed_zero_hand_arithmetic.json | 1e87fd82ebd83700704dbdc6a776371a6df1f8e91eb3505ae489c06be6e25ce2 |

A fresh execution of the checker returned
\(\{"status":"PASS","strict\_comparisons":126\}\).

## Coverage and coefficient review

I compared every displayed P,J,L,K coefficient and every affine core
coefficient against the exact label JSON, including the reflected target
role 5. The sign identity \(L_{2-i}^{\sigma}=L_i^{-\sigma}\) sends
edges 0 and 1 to one another and sends edge 4 to itself with opposite
signs. The four allowed same-sign classes therefore reduce exactly to
edges 0 and 4, signs ++, each in the two radial orders.

For C+ to O+, the possible axes after the stated exclusions are source
+f (family I) and target +e (the reversal of family IV). For O+ to C+,
they are source +f (family II) and target +f (the reversal of family III).
The other four normalized axis/kind combinations are impossible by
the explicit cap estimates in Section 2. Restoring the reflection gives
all \(4\cdot2\cdot4=32\) stated branches. No other sign or owner assumption
is used in a later family.

The lower bound \(\phi>-.026\), exclusion of nonpositive angles,
and the positive-core primary and transverse exclusions all have the
correct inequalities. In particular the core corner is not silently
replaced by its straight side.

## Derivatives and contact reductions

I rederived the three polynomial-label derivatives in equation (10).
Their signs give the stated global concavity of J,K, increasing
convex P, and the uniform strong convexity of \(L'\). The completion
of the square in (15) is valid on the entire outer arc: \(L'''>2\)
and the derivative value and slope at .5 yield the advertised bound.

For family I, subtracting \(gM\) cancels the source transverse
coordinate exactly for both core pieces. The full-circle support
formula (18) and the norm identity (19) have the correct constant
and sine terms. The .44 angle barrier and four endpoint comparisons
close its whole domain.

For family II, subtracting \(M\), using \(\cos\phi>g\), and applying
the lower affine slope bounds gives precisely (21). Its derivative
is positive and the .49 barrier is valid.

For family III, relaxing the core transverse upper endpoint lowers
the cost, because its coefficient is negative. The derivative of the
relaxed expression in B is strictly positive, so its minimizing
coordinate is the first feasible point, where the relaxed core
coordinate is zero. This is a valid lower-bound argument and does
not assume the relaxed state is a physical core state.

I independently differentiated the exact contact curve (24). The
identities \(U'=Vf,\ V'=-Uf\) and the formula for \(f'\) are correct.
The numerator of \(f'\) increases with \(m=\sin\phi+\cos\phi\) because
\(m<Q-9/4\); its denominator decreases. Hence all monotonicity
used in (28) follows on the whole enlarged interval. The signs of
both terms in the curvature bound (28) are correct. The eight
declared intervals exhaust the curve, and the unknown true initial
angle is bounded in the safe direction by .3024.

## Core-corner argument

For family IV, the outer source can always be moved to contact:
its label increases with its transverse coordinate, while its
primary projection decreases. The endpoint b=d is infeasible.
On the core side the two monotonicities in (33)–(34) place the
minimum at the stated endpoint.

On the corner I rederived
\[
 b_B=(u/v)(t\cos\phi+\sin\phi),\quad
 b_{BB}=(u/v)\kappa\cos\phi-Q(t\cos\phi+\sin\phi)^2/v^3.
\]
Thus the normalized curvature identity (35) is correct. The factor
\(\kappa\cos\phi/(t\cos\phi+\sin\phi)^2\) decreases with angle;
the three elementary t ranges in (36) give a uniform strict lower
bound 10. The largest feasible b is at the core diagonal and
angle .7, justifying the common .381 cutoff.

Both terms in the derivative of \(K_0(v)\) in (37) are positive
when \(3v^2<Q\). The four fixed derivative rectangles in (39)
therefore imply strict convexity of \(F(b(B))\), and hence strict
concavity of the cost in the core coordinate. The feasible core
coordinates form a terminal interval, whose complete endpoint list
is exactly the side junction, core diagonal, or first feasible b=0.

Finally, \(T_F(b)\) decreases and the diagonal speed \(w_0(b)\)
increases. The two product bounds in (42) safely cover their whole
common interval without assuming their product is monotone. The
final diagonal and side cost bounds are all strictly above gamma.

## Scope

This audit certifies the same-sign mixed zero-quarter component
only, conditional on the upstream frame/gap premises named in the
proof. It does not assert the remaining wrong-word outer or
quarter-one components or the unrestricted eight-square theorem.

