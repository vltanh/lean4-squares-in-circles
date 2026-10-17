# Independent review of all core/core cases for 0011011

**PASS.** The restored **WRONG_0011011_ALL_CORE_CORE_HAND_PROOF.md**
proves every stated core/core pair bound, on the whole core side and
corner, with the strict threshold \(91/100>17953/20000\).
This records a fresh review of the current restored bytes in addition
to the earlier independent review.

I rederived the core endpoint lemma. Concavity of arctangent gives its
lower bound. For its upper bound on the side, increasing the slope to
\(8/7\) is the worst case because \(d_c-b>0\). The sole side minimum
is \(b/a_c=1/\sqrt2\), and tangent subtraction gives exactly
\(\arctan(3-2\sqrt2)-(4-2\sqrt2)/7\). The cubic arctangent lower bound
exceeds \(1/400\). On the corner,
\[
 \alpha''=
 \frac{-ba''(a^2+b^2)-2(a-ba')(aa'+b)}{(a^2+b^2)^2}>0.
\]
The first numerator term is at least \(3\); the second is at most
\(7/6\), since \(2(aa'+b)=1-d/e\in[0,1]\).
Consequently the corner maximum is at one of its two endpoints,
which joins correctly to the side proof.

The sole nonaffine label differs from its core-side affine expression
by
\[
 E=.34492(a_c-a)-.05334b^2.
\]
Its lower bound is \(-.05334d_c^2\). Its upper bound is zero on the
side, and is strictly negative on the corner using
\(a_c-a<1/30\) and \(b^2\geq1/4\).
Thus the stated potential intervals include every core state.

The ray-gap argument uses the actual incircles: disjoint open unit
squares have center distance at least one. Each core radius is less
than \(4/5\). If a gap were at most \(27/20\), separate convexity in
the two radii reduces the maximum squared distance to the four
corners of \([0,4/5]^2\); the displayed cosine lower bound then makes
all four values less than one. This proves the strict gap needed
by the potential calculation without assuming equal radii.

I reconstructed the signed potential intervals directly from the exact
role-coefficient JSON, applied the reflection coefficient identities,
and independently recalculated all ten printed cost rows.
The exceptional edge-3 \((+,-)\) row correctly uses the direct
quarter-angle and label bound. Its treatment does not substitute a
potential bound with the wrong sign. Every printed row exceeds
\(.91\); all unlisted rows are the explicitly stated reflected
partners. The proof includes zero-coordinate choices and the
side/corner join, and has no equality case at the wrong-word
threshold.

The companion **audit_wrong_0011011_all_core_hand.py** freshly ran
the author checker in an isolated temporary directory and compared
its **52-comparison** report byte-for-byte with the stored report.
Its separate Fraction calculation reconstructs the root/arctangent,
radius/gap, nonaffine-correction and all ten signed table comparisons.
The resulting **wrong_0011011_all_core_independent_audit.json**
binds the reviewed manuscript, author checker/report, exact label
file and independent checker by SHA-256.

This audit is a whole core/core component review. The other radial
orders and the full-word telescoping argument are separate inputs.
