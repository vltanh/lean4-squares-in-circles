# Independent review: complementary mixed 0/2 branch and complete orbit join

Date: October 26, 2026.

**Verdict: PASS.** The saved manuscript
`SIX_CYCLE_MIXED_02_LARGE_FORCE_BRANCH_ANALYTIC.md` excludes the
entire \(q<p\) branch of the mixed corner pattern 110 with genuine
shares at loaded units 0 and 2. Together with the independently
reviewed `SIX_CYCLE_MIXED_02_SMALL_FORCE_BRANCH_ANALYTIC.md`, it
excludes that full contact orbit. The result is an analytic physical
contradiction, with no computational coefficient packet.

## 1. Original physical data and the force-ratio bound

I checked the saved source end to end against the complete-domain
source and the accepted mean-preserving support formulas. The
nonshared middle vector is
\((1+p\sin\theta_1,1-p\cos\theta_1)\), with squared norm
\(2+p^2+2p(\sin\theta_1-\cos\theta_1)\). The shared
directions and the two actual chords in (5) have their correct
incoming/outgoing signs. No mean is replaced by an endpoint, and a
genuine share with chord one remains in the initial domain.

Direct expansion of both coordinates of the true contact closure
reproduces (6)--(7), with all three identities in (8). Since the
middle turn is strictly greater than \(\pi/2\), the right side
of (7) is strictly positive, forcing \(q>1\) and \(t_0>0\).
Thus the branch \(q<p\) indeed gives \(p>q>1\).

The upper bound \(p<27/10\) applies to the actual nonshared
bit-one loaded unit. For an independent local check, its true
unique-corner inequality is

\[
 L D_1<2R(1+pc_1),\qquad
 L^2-D_1^2=1+2p s_1>0.
\]

Hence \(p^2<(2R-2)pc_1+2R-1\). The retained upper radius
bound gives \(R<133/64\), and
\(c_1\le1/\sqrt2<99/140\), yielding the polynomial
\(p^2-(6831/4480)p-101/32<0\). At \(27/10\), its value
is \(151/8960>0\), and it is increasing thereafter. This
independently confirms the force bound with its correct strictness.
Its premise is the physical unique-corner mask, not merely a positive
selected load at one corner.

## 2. Both uniform scalar gaps

Differentiation of the middle direction gives exactly (13):
\(\partial X/\partial p=(s-c)(1+pc)/L^3\ge0\). The
enlargement \(L(p_0)\le p_0+\sqrt2\) is valid for every
original turn. Subtracting \(U\) and applying Cauchy yields the
radicand \(2-\sqrt2+2v+2v^2\) in (15) exactly.

The squared comparison (16) is correct, and its other squared side
\(1+v-\epsilon\) is positive. Thus there is no reversal or
extraneous root when passing to the square-root comparison. The
strict lower bound \(\sqrt2>140/99\) and the two corresponding
upper bounds for \(v\) preserve the required monotonic signs.
Independent exact rational reconstruction gives precisely

\[
 \frac{1248475}{90479664}>0,
 \qquad
 \frac{218416231211}{47929626360000}>0.
\]

Consequently \(X-U>1/12\) for every \(p\ge1\), and
\(X-U>27/200\) for every \(p\ge21/10\), over all
original turns. In particular \(s=c=1/\sqrt2\), where the
derivative of \(X\) vanishes, remains included.

## 3. Closure contradiction with no omitted endpoints

Subtracting the hypothetical equal-force value in the horizontal
closure reproduces (17) exactly. The bound \(c_2\le1/\sqrt2\)
has the correct sign because \(t_1\ge0\). The strictly positive
scalar gap forces \(t_2>0\). Thus the endpoint \(t_2=0\),
equivalently the genuine incoming share having chord one, is
explicitly contradicted by the equation rather than removed from the
domain. Likewise the other endpoint \(t_0=0\) was already
contradicted by (7).

The sum-to-product identity (20) is exact. Its positive bracket has
square \(1-\sin\theta_1=z>0\), so the bound by
\(2\sqrt z\) holds at every retained angle. Applying Cauchy
to \((\sqrt a,\sqrt b)\) and
\((\sqrt{t_0},\sqrt{t_2})\) gives the middle inequality in
(21). The strictness follows from \(bt_2>p\epsilon\).
All denominators in the subsequent division are positive.
The arithmetic-geometric mean step gives exactly
\((p-1)^2/p>8\epsilon\).

The two final intervals are exhaustive for \(1<p<27/10\),
and their common boundary \(p=21/10\) is included. The exact
positive reserves \(19/210\) and \(13/1350\) reproduce
the two final contradictions. These are two scalar constant choices
in one analytic argument, not a force-ratio mesh or numerical sign
certificate.

## 4. Full mixed 0/2 join and precise scope

The normalizing magnitude \(\mu_0\) is strictly positive, so
every original force triple has exactly one normalized pair \((p,q)\).
The orderings \(q\ge p\) and \(q<p\) are exhaustive, with
the equality boundary assigned to the first. The small-force source
proves a radius contradiction on the first branch and has its own
independent saved-source review in
`REVIEW_C6_MIXED_02_SMALL_FORCE_BRANCH_2026_10_26.md`. The present
source proves a closure contradiction on the second. The original
incoming/outgoing placement, circle masks, means, positive forces,
transmitter equations, and full radius window agree between the two
sources. They therefore join to exclude the entire mixed 110,
shares 0/2 contact orbit.

No actual transmitter is moved, no shared side becomes a singleton,
and the three additional physical squares remain arbitrary. The
constant-corner orbit and the other mixed orbit require their separate
proofs before the complete two-share gate is closed. The one-share
and strictly obtuse one-radial families, the global sharp inequality,
all equality packings, and the earlier prerequisite-chain audit are
not closed by this joined result. No Lean compilation, CI, workflow
dispatch, or numerical proof premise was used.

A harmless cross-reference typo was reported to the author: the
closure-difference identity is equation (7), rather than (6), in the
small-force source. This does not affect any equation or inference.
