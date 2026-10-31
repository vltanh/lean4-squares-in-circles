# Root review: the one-share alternating-C6 family reduces to one physical orbit

Date: October 26, 2026.

**Result: PASS for the full constant-corner one-share exclusion, the
mixed sole-incoming-share-2 exclusion, and the exact four-orbit
cover with its unchanged residual domain.**

The complete saved sources reviewed were
SIX_CYCLE_CONSTANT_CHI_ONE_SHARE_EXCLUSION.md,
SIX_CYCLE_MIXED_ONE_SHARE_2_CLOSURE_EXCLUSION.md, and
SIX_CYCLE_ONE_SHARE_FULL_ORBIT_COVER_AND_RESIDUE.md, with the
earlier accepted middle-share exclusion and all stated local
normal-form dependencies. Both new exclusions also have separate
independent source-and-scope reviews.

## 1. Constant-corner orbit: original equations and angle reduction

The sole genuine outgoing share has its actual chord
\(\ell_0=1-qA_0\). The other two chords are one because their
actual contacts are nonshared. Re-expanding the true support vectors
gives exactly the displayed positive-vector direction cones.
Horizontal closure gives \(A_1\ge h_0-1\), and the imported
scalar implication from the two-share manuscript is independent of
the number of shares, as required here.

The physical bound \(p<27/10\) applies to the actual nonshared
bit-one body at unit 1. It uses the original unique-corner mask and
the full upper radius endpoint, both of which remain in scope.
The resulting lower line for \(Y_1\), its monotonicity in \(p\),
and the actual vertical closure give the stated necessary \(F\ge0\).

For the second angular restriction, the source uses convexity of
\(F(x,x-7\pi/80)\) and two correctly signed Taylor endpoint
upper bounds. I independently recomputed both exact negative
fractions from the displayed elementary polynomials. Intersecting
the three half-planes gives exactly the three stated angle vertices.
This is one triangle containing the full physical domain, not a
collection of numerical feasible samples.

## 2. Constant-corner orbit: complete rational matrix check

The denominator bound is the square-root chord inequality with
adjacent normalized force sum at most one. The numerator tangent
bounds retain both nonshared couplings. Collecting the quadratic
independently gives \(C=(2+\sqrt2,2+\sqrt2,2+h_0)\) and the
displayed matrix entries.

All half-angle coefficients have the positive sign and all
\(h_i\) coefficients the negative sign required by the entrywise
Taylor replacement. The global strengthened \(h_i\) bound has
the exact positive coefficient reserve \(289/415800\).
The control formula for \(1-h_i/\sqrt2\) uses
\((\sqrt2)^2=2\) exactly before rational interval arithmetic.

Starting from the rational angle vertices and radical intervals,
I reconstructed every one of the 54 directed control entries with
exact fraction arithmetic. Each of the six minimum reserves agrees
exactly with the source's stated fraction, and each exceeds
\(1/500000\). I independently multiplied every displayed integer
matrix by its positive weight vector; all six products agree
exactly and exceed seven times that vector coordinatewise.

The weighted-row square identity is exact and its coefficients are
nonnegative. The six barycentric weights are nonnegative and sum to
one. Applied to the actual positive force vector and rescaled
homogeneously, these inequalities give
\[
 \frac{79}{40}\sum_iD_i-N>
                      \frac7{30000}\sum_i\mu_i>0.
\]
The true virial identity contradicts \(R\ge79/40\).
The finite work here is openly six small rational matrices; this
review does not call this proof table-free.

## 3. Mixed sole incoming-share 2: one exact diagonal projection

The original bit-one nonshared support vectors are exactly
\[
 g_0=(qA_0,-1-qh_0),\qquad g_1=(1+ps_1,1+pc_1).
\]
The bit-zero shared body's actual direction is
\(u_2=(-s_1,-c_1)\), with \(0<\ell_2\le1\).
Projection of the actual channel closure on \((1,-1)\) gives
the four terms \(1-h_1+A_0,\ U+V,\ X-Y,\ -\ell_2A_1\).
Their lower bounds are respectively unchanged, at least one,
nonnegative, and at least \(-A_1\).

Their sum is consequently at least \(2(1-s_1)+A_0>0\), since
the original turn is strictly greater than \(\pi/2\).
This contradicts exact closure. The argument retains every
positive force ratio and every mean endpoint; it needs no radius
estimate or finite positivity certificate.

## 4. Exact symmetry cover and remaining physical domain

Reflection followed by reversal sends
\(\chi_i\) to \(1-\chi_{-i}\) while carrying the true side
base and means. Constant words therefore give one orbit, and
nonconstant words give the canonical word 110 with three distinct
share positions. Its cyclic stabilizer is trivial, and a
reflection-reversal changes the number of one-bits. Thus the four
listed contact types are exhaustive and no mixed positions have
been identified incorrectly.

Constant bits, mixed share 1, and mixed share 2 now have complete
exclusions. The middle-share proof was already accepted; a later
shorter version must not be counted as a new closure. The exact
remaining type is mixed 110 with its sole outgoing share at 0.

I also read the complete shorter alternative
SIX_CYCLE_MIXED_ONE_SHARE_1_CLOSURE_EXCLUSION.md. Its bounds
\(V>1/\sqrt2\), \(Y_2\ge A_0/\sqrt2\), and actual vertical
closure force \(h_1>\sqrt2\), exactly as claimed. This is a valid
independent proof of the existing middle-share result, with all
means and forces retained; it contributes no new orbit count.

I checked the residual support vectors, the two closure
coordinates, direction cones, virial numerator, physical corner
inequalities and their local force-ratio consequences. The proof
that \(A_0>0\) is valid: \(A_0=0\) would force
\(N\le s_1-1<0\). Hence its genuine shared chord is strictly
less than one by contradiction of the actual endpoint, rather
than by removing that endpoint from the original scope.

The residual manuscript retains every actual pairwise channel
equation, the physical square poses, all containment and
nonintersection requirements, and every true transmitter slider.
The common occupied transmitter rectangle follows from the full
interval endpoints with the correct signs.

The accepted central-capacity theorem gives at most one central
extra. The listed remaining allocations keep repeated exterior
occupancy, including two or three extras in one cap. They are
exhaustive count possibilities, not asserted feasible packings.
No whole-cap bound or central-exclusion claim is inferred from
diagnostic core area.

The review therefore accepts the stated reduction to one original
completion problem. It does not exclude that remaining problem,
the strictly obtuse one-radial branch, or the unrestricted
nine-square/equality problem. No new gate is introduced and no
existing coarse gate is ticked by this review. No Lean compilation,
CI, workflow dispatch, or numerical proof premise was used.
