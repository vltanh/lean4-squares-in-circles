# Independent review: full constant-corner one-share C6 exclusion

Date: October 26, 2026.

**Result: PASS for the whole constant-corner one-share orbit.**
Independently reviewed the complete saved manuscript
SIX_CYCLE_CONSTANT_CHI_ONE_SHARE_EXCLUSION.md, its physical
normalization, both angular reductions, all force-ratio eliminations,
the six complete control matrices, and the final homogeneous join.
The exact interval calculation was reconstructed from the displayed
formulas and constants using fresh rational arithmetic; no author's
checker, floating-point eigenvalue, or optimizer result was used.

This review accepts the precise whole-family conclusion in that
manuscript. It does not certify mixed-corner one-share cases, the
one-radial family, the unrestricted sharp bound, or equality
classification. No Lean compilation or CI was run.

## 1. Physical orbit, true means, and original support vectors

The proper reflection-plus-reversal operation exchanges the two
constant bit patterns and exchanges incoming with outgoing shares.
Cyclic relabeling therefore legitimately reduces the entire
constant-corner one-share orbit to bits 111 with its sole outgoing
genuine share at unit 0. This argument is independent of the number
of shares, as the source states.

At unit 0 the actual chord remains
\(\ell_0=1-(\mu_2/\mu_0)A_0\), with \(0<\ell_0\le1\).
The other two bodies have their actual singleton endpoint ports and
chords one. Independently expanding \(f_{i-1}+JF_i\) gives exactly
the two nonshared support norms in the source.

After normalization \(\mu_0=1\), the two support directions are

\[
 u_1=\frac{(1+ps_1,1+pc_1)}
                {\sqrt{2+p^2+2ph_1}},
\]
\[
 u_2=\frac{p(-h_1,A_1)+q(-s_0,c_0)}{E_2}.
\]

Both expressions use positive actual forces. Their direction cones
give \(X_1\le s_1\), \(X_2\ge s_0\), and
\(Y_2\ge A_1/\sqrt2\), exactly as claimed. The first cone is
the positive span of the directions \(\beta_1\) and \(\pi/4\);
the second is ordered by \(\beta_2\le\pi/4\). No false direction
ordering is used.

The original horizontal closure equation therefore gives
\(A_1\ge h_0-1\). The imported analytic implication
\(y+3x/8\le\pi/4\) is exactly the full scalar implication proved
in Section 3 of SIX_CYCLE_CONSTANT_CHI_TWO_SHARE_EXCLUSION.md;
that implication does not assume the second physical share.

## 2. Use of the actual unique-circle corner and vertical closure

The \(p<27/10\) bound is applied to the actual nonshared bit-one
body at unit 1. Section 5 of
SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md explicitly
proves that local bound independently of the number of other shares.
Its derivation uses the full upper radius endpoint and the physical
unique-circle mask, both retained here.

The auxiliary denominator satisfies \(L\le p+\sqrt2\). The
derivative of \((1+pc_1)/(p+\sqrt2)\) has the sign of
\(\sqrt2c_1-1\le0\). Consequently the force bound gives the
claimed whole-domain lower line

\[
             Y_1>\frac{35}{144}+\frac{21}{32}c_1.
\]

I independently checked its coefficients:
\((1+(27/10)c_1)\cdot35/144
 =35/144+(21/32)c_1\).

The actual vertical closure, including the real shared chord, is

\[
 Y_1+Y_2=1+s_0-s_1-qA_0.
\]

Because \(qA_0\ge0\), this gives the displayed necessary inequality
\(F(x,y)\ge0\). The source only weakens a strict bound at this
step. No endpoint mean is silently removed.

## 3. The second angular inequality and the single triangle

For \(d=7\pi/80\), the original angle sum already gives
\(y\ge x-d\) when \(x\le27\pi/160\). On the remaining whole
interval, \(F\) increases with \(y\). The second derivative of
\(f(x)=F(x,x-d)\) is correct, and its lower bound is

\[
 f''(x)\ge-1+(53/32)/\sqrt2>0.
\]

This follows from \(\cos x\le1\),
\(\cos(x-d)\ge1/\sqrt2\), and
\(\sin(x-d)\le1/\sqrt2\). The signs of all coefficients are
retained, including \(1/\sqrt2-21/32>0\).

The alternating cosine and sine bounds have the stated remainder
signs on \([0,1]\). Each endpoint substitution uses the correct
monotonicity: a smaller argument for the positive cosine upper
bound, a larger argument for the subtracted cosine lower bound,
and a larger argument for the positive sine upper bound.

The two fixed rational upper values were independently reproduced
exactly:

\[
 -\frac{2012570178689899309}{274793126952960000000},
 \qquad
 -\frac{19023159189132991}{68698281738240000000}.
\]

Both are negative. Convexity therefore puts \(f\) below zero
throughout the complete interval. The ensuing contradiction for
\(y<x-d\) is valid.

I also independently recomputed the three intersections of

\[
 x+y\ge\pi/4,\qquad y\le\pi/4-3x/8,\qquad
 y\ge x-7\pi/80.
\]

They give precisely the three rows of the angle triangle in the
source. In particular the third intersection has
\(x=27\pi/110,\ y=139\pi/880\), yielding
\[
 (\theta_0,\theta_1,\theta_2)
       =(41\pi/55,\ 579\pi/880,\ 105\pi/176).
\]
The triangle includes every original feasible angle and stays within
the interval required by the global Taylor bounds. No portion of the
actual force domain is removed by an unexplained numerical cutoff.

## 4. Force homogenization and both retained nonshared couplings

After normalization \(\sum\mu_i=1\), the denominator lower bound
is the square-root chord inequality with each adjacent force sum at
most one. Both nonshared support norms have the exact form needed
for the upper tangent inequality.

Collecting the numerator independently gives

\[
 C_0=C_1=2+\sqrt2,\qquad C_2=2+h_0,
\]

with both corrections
\[
 (1-h_1/\sqrt2)\mu_0\mu_1,\qquad
 (1-h_2/\sqrt2)\mu_1\mu_2.
\]

The diagonal and off-diagonal entries of the manuscript's matrix
therefore agree with direct expansion of the displayed homogeneous
quadratic. Both nonshared force couplings are present. The three
force ratios remain unrestricted in this scalar inequality.

## 5. Global trigonometric inequalities and exact controls

The half-angle lower bound is the correctly signed global
second-derivative bound from the independently reviewed two-share
source. For the stronger upper bound on \(h\), writing
\(t=3\pi/4-\theta\) gives exactly \(h=\sqrt2\cos t\).
The fourth-order cosine upper bound and \(t\le\pi/4\) give

\[
 h\le\sqrt2-\frac{67}{100}t^2.
\]

The claimed positive coefficient reserve was reproduced exactly as
\(289/415800\). Equality at \(t=0\) is harmless.

All occurrences of half-angle sine in the force matrix have positive
coefficients; all occurrences of \(h_i\) have negative coefficients.
Thus the Taylor replacements give an entrywise lower matrix. The
source correctly applies this comparison only to nonnegative force
vectors; it makes no unsupported matrix-order claim on signed vectors.

Polarizing each quadratic over the three displayed angle vertices
gives all six controls in the source. The linear terms use the
midpoint of the two vertex values, and the quadratic terms use their
product. The simplified formula
\[
 a_i^{UV}=(67\sqrt2/200)Q_i^{UV}
\]
uses \((\sqrt2)^2=2\) exactly, as it must before interval
evaluation. The six barycentric weights are nonnegative and sum to
one.

## 6. Independent reconstruction of the six finite matrix checks

Starting only from the source's rational vertex rows and constant
intervals, I rebuilt every control entry with exact fraction
arithmetic. The minimum reserves agree exactly with the manuscript:

| Control | Independently reproduced minimum reserve |
| --- | --- |
| \(AA\) | \(77990999/1920000000000\) |
| \(BB\) | \(861418452763/25600000000000000\) |
| \(CC\) | \(96882465720597229/37171200000000000000000\) |
| \(AB\) | \(3872613890129/737280000000000000\) |
| \(AC\) | \(111318954535853/2703360000000000000\) |
| \(BC\) | \(222213135184519/10137600000000000000\) |

Every one exceeds \(1/500000\). Thus all 54 directed entries,
or equivalently all 36 independent symmetric entries, have the
claimed strict rational lower bounds.

I independently multiplied the six integer matrices by their
displayed positive vectors. The resulting rows are

\[
 (3123,1319,1577),\quad (907,1445,1992),\quad
 (346,377,1698),
\]
\[
 (3743,3242,1584),\quad (991,1921,562),\quad
 (3566,1817,1190),
\]

in the displayed order. Each coordinate is greater than seven times
the corresponding positive-vector coordinate.

The weighted-row sum-of-squares identity is algebraically exact.
All off-diagonal entries of the rational lower matrices are
nonpositive, so every extra square has nonnegative coefficient.
This proves the stated uniform lower quadratic bound without
appealing to sampled eigenvalues or an unstated determinant sign.

## 7. Whole-family conclusion

The six strict entrywise bounds, their nonnegative barycentric
combination, and the actual positive force vector give the claimed
strict gap

\[
 \frac{79}{40}\sum_iD_i-N
                >\frac7{30000}\sum_i\mu_i>0.
\]

The homogeneous rescaling is correct. The original physical virial
identity \(N=R\sum_iD_i\), with positive denominator, then
contradicts \(R\ge79/40\).

This proves the full constant-corner one-share orbit, including both
constant bit patterns, every placement of the sole genuine share,
every original positive force ratio, all allowed mean endpoints,
both radius endpoints, all transmitter positions, and all three
extra physical squares. The upper radius endpoint enters through
the actual nonshared unique-corner force-ratio bound, and is not
silently omitted from the dependency chain.

The manuscript's remaining-scope statements are correct. This
review accepts no mixed-corner one-share orbit or later global
classification claim.
