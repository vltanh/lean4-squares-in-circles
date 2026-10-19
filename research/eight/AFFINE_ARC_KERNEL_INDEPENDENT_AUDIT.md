# Independent review of the affine-arc one-angle kernel

**Result: PASS for the stated circular/core boundary domain and declared
nonempty tangent intervals.** The reviewed immutable source is
`verify_G_upper_affine_hand.js`, SHA-256

```
1bd04b7b8890f7008108489da6fdf24b947e472eb4873f7523994ce4b81b85ee
```

This is the frozen copy of the generic kernel described in
`AFFINE_ARC_ONE_ANGLE_HAND_KERNEL.md`. I rederived its continuous support,
signed-axis normalization, radical, and pointwise polynomial arguments.
I also reviewed the actual coefficient and coverage implementation. No
correction to the kernel or to the G-upper table was required.

## 1. Geometry and complete support scope

For a canonical tangent \(v=b/a\), substitution in the outer equation
gives

\[
 (1+v^2)a^2+(1+v)a+1/2-Q=0.
\]

The positive root is the expression used by `abAt`. On the core corner
the equation is

\[
 (1+v^2)a^2-(1+v)a+71/144=0.
\]

The larger root is used, and the exact junction \(v=6/7\) agrees with
the straight side \(a=7/12\). The code requires every core arc to be
wholly side or wholly corner. These choices select the intended positive
coordinate branches. In each case \(v\) increases with \(b\), since
\(d(b/a)/db=(a-ba')/a^2>0\).

For a circular branch \(a=h+\sqrt{R^2-(b-h)^2}\), the identities
\(a'=-r\), \(r=(b-h)/(a-h)\), and \(r'>0\) prove every support rule.
An affine functional \(Xa+Yb\) is concave when \(X\ge0\); its derivative
\(Y-Xr\) lies between its two endpoint values for any sign of \(X\).
Thus both monotone endpoint rules are valid even when coefficients vanish.
The full-circle lower support \(h(X+Y)-R\sqrt{X^2+Y^2}\) is valid
without assuming that its minimizer lies on the subarc. It is never used
on a straight core side. These observations cover every path through
`sourceMinimum` and every declared target mode.

The interval returned for the smaller of two endpoint values is correctly
enclosed by taking the smaller of their lower bounds and the smaller of
their upper bounds. An uncertain derivative sign causes a lower-support
fallback, rather than an unsupported monotonicity inference.

## 2. Signed SAT normalization and cost direction

Starting with the four actual margins in the kernel note, direct
substitution confirms that reflection and reversal send axes 2 to 4 and
3 to 1. The operation exchanges states, changes both signs, and replaces
the labels by the negatives of the old target and source labels. It keeps
\(\phi\) and \(\phi+L_s-L_t\) unchanged. No reflection symmetry of the
role labels is assumed.

For \(M\ge0\) and \(\lambda\ge0\), subtracting \(\lambda M\) produces
a lower bound for the corrected cost. Expansion gives exactly the four
coefficients in the kernel's two-row source/target table. Independently
squaring the target coefficients gives its stated \(V_1,V_4\), after
using \(\sin^2\phi+\cos^2\phi=1\). They are genuine squared norms.
Consequently the radical majorant does not require a separately verified
polynomial lower bound on \(V\).

The optional nonnegative width charge is invariant under the same
normalization. Its sign in the code is the required negative sign. A row
override is required to be at least the declared edge target, so it cannot
weaken the claimed inequality.

## 3. Global radical and pointwise polynomial arguments

With \(z=\sqrt V/h\), the radical identity is equivalent to

\[
 (z-1)^4(z^2+4z+5)=z^6-5z^4+15z^2-16z+5.
\]

I expanded this identity independently. It proves the upper majorant for
every \(V\ge0\) and every \(h>0\), including \(V=0\). The negative
radius coefficient therefore gives the correct lower support direction.

For \(\phi=k\pi/2+r x\), with \(0\le x\le.7\), the code's signed sine
and cosine substitutions and the width \((1+\sin x+\cos x)/2\) are
correct on both sides of both quarters. The degree-9 sine and degree-10
cosine coefficient intervals follow from the alternating series.

Coefficient interval multiplication remains valid when the Taylor error
parameters vary with \(x\): for each fixed \(x\), all actual parameters
lie in their stated intervals. Selecting the lower power coefficient at
each degree is a pointwise lower bound because \(x\ge0\). Repeated uses
of a parameter enlarge the enclosure and never reverse it. No derivative
or unjustified independence assumption about the error parameters occurs.
Discarding trailing zero lower coefficients simply lowers the degree of
the same selected polynomial.

## 4. The exact integer Bernstein optimization

I checked the denominator-clearing implementation against the ordinary
power-to-Bernstein formula. If \(p_i=q_i/D\), and a row interval is
\([L/U,(L+W)/U]\), its substituted power numerator is

\[
 A_j=\sum_{i\ge j}q_i\binom ij L^{i-j}W^jU^{n-i}.
\]

Taking \(B\) to be a common multiple of the \(\binom nj\), the
Bernstein coefficient numerator is

\[
 N_k=\sum_{j\le k} A_j\binom kj\frac{B}{\binom nj},
\qquad \text{denominator }DU^nB>0.
\]

These are the exact integer operations in the code. The optimization
introduces no rounding and changes no coefficient. Constant polynomials,
zero-width closed angle intervals and mixed-sign power coefficients are
all handled by the same identities. The final decimal record is rounded
down, and strictness is tested on the exact rational before that display.

As a separate implementation check,
`audit_affine_arc_kernel_independently.py` reconstructs 93 polynomials of
every degree 0 through 30 by solving the triangular Bernstein basis system,
which does not use the kernel's direct conversion formula. Every resulting
coefficient agrees exactly. It also checks all distinct fixed state
endpoints from the G-upper table against their defining quadratics and
recomputes the radical identity with integer polynomial arithmetic.

## 5. Endpoint enclosures and whole-domain coverage

The integer square-root routine brackets every nonnegative rational root
by exact squared comparisons. The half-angle arctangent formula has a
positive denominator and an argument at most \(\sqrt2-1\). The alternating
partial sums through powers 49 and 51 therefore have the stated directions.
Interval evaluation and outward decimal rounding preserve those directions.
The Machin enclosure is checked by exact alternating rational sums.

The necessary frame-angle endpoints correctly use the largest source
angle and smallest target angle for the lower bound, and the opposite
extrema for the upper bound. Both half-angle branches are converted with
the right direction. The closed-chain routine checks the original four
axes, before normalization, and retains isolated required angle endpoints.
The G-upper independent assembly audit recomputes these angle bounds with
a different root mesh and verifies every one of the 8,876 required chains.

The mathematical calling interface supplies actual circular/core states,
the physical gap hypotheses and valid tangent intervals. The G-upper
assembly checks these declared cuts have positive length, and all 26
nonempty sign/kind domains are covered. The kernel alone is not a theorem
about arbitrary invalid geometric input, and a pair table without a
declared closed-domain cover is only a conditional pair theorem.

## 6. Conclusion

The reviewed kernel turns each supplied fixed rational row into a proved
continuous lower bound on its whole angle interval. Its arithmetic,
support premises, sign normalization and domain-chain logic are valid.
The G-upper table additionally has a complete independent state/angle
assembly and the exact positive cyclic reserve. Thus the kernel review
leaves no geometric or arithmetic premise open in that exclusion.

The final candidate capture and uniqueness theorem still require the
separate remaining capture gates; this review makes no inference about
their completion.
