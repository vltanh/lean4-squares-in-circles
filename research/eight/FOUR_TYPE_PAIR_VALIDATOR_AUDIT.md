# Independent audit of the continuous four-type pair verifier

**Scope.** This audit concerns the mathematical formulas and acceptance rules in
`verify_fourtype_pairs.cpp`, with its included exact dyadic interval
kernel. Every required branch is now complete in
`fourtype_pair_logs_checked/manifest.json`. The constants match
`fourtype_rational_certificate_data.json` exactly. A sample, an unfinished branch,
or an exhausted budget would not count as a certificate.

## 1. State coordinates and exact boundary curves

Let \(Q=9789/2500\), \(\rho=1/12\), and choose a representative
\(\alpha\in[-\pi/4,\pi/4]\) of the square frame relative to its outward
center ray. Write

\[
t=\tan\alpha,\qquad a=r\cos\alpha,
\qquad r=a\sqrt{1+t^2}.
\]

The state has one of two boundary kinds after the independently proved radial
boundary reduction. Both curves depend only on \(x=|t|\in[0,1]\).
The outer disk boundary satisfies

\[
(1+x^2)a^2+(1+x)a+\frac12-Q=0,
\]

so its positive root is

\[
a_+(x)=\frac{\sqrt{(1+x)^2+4(1+x^2)(Q-1/2)}-(1+x)}
                  {2(1+x^2)}.
\]

The core boundary is

\[
a_-(x)=\frac7{12}\quad(0\le x\le6/7),
\]

and beyond the side-to-corner transition it is the larger root

\[
a_-(x)=\frac{1+x+\sqrt{(1+x)^2-4(1+x^2)(71/144)}}
                  {2(1+x^2)}
\quad(6/7\le x\le1).
\]

Both are nonincreasing in \(x\). Implicit differentiation gives a strictly
negative derivative for the outer curve. For the core corner,

\[
a_-'(x)=\frac{a(1-2ax)}{2(1+x^2)a-(1+x)}\le0,
\]

because the larger-root denominator is positive and the corner satisfies
\(ax\ge1/2\). The side is constant. Therefore interval values of \(a\)
may be bounded by outward-rounded evaluations at the two endpoints. The
verifier also encloses both formulas at the rounded transition point.

Types 0,1,2,3 are respectively the core, outer \(x\in[0,1/4]\), outer
\(x\in[1/4,3/7]\), and outer \(x\in[3/7,1]\). The type-0 function has
knots \(k/8\); the other knots are \(k/32\), \((56+5k)/224\), and
\((6+k)/14\), for \(k=0,\ldots,8\). These are exactly eight equal pieces
on each stated domain. The two one-sided potentials at a type boundary are
independent. Verifying both closed branches covers either deterministic
choice of type at that boundary.

## 2. Exact SAT numerator

Place a source center at \((r_A,0)\) and a target center at
\(r_B(\cos\delta,\sin\delta)\). The source and target relative frame
parameters are signed \(t,u\), with local first coordinates \(a,b\).
Define

\[
A=1+t^2,\quad B=1+u^2,\quad Z=\sqrt{AB}>0,
\quad K=1+tu,\quad L=u-t,\quad V=bB,\quad W=aA.
\]

The relative frame angle is \(\phi=\delta+\arctan u-\arctan t\), and

\[
Z\cos\phi=K\cos\delta-L\sin\delta,\qquad
Z\sin\phi=K\sin\delta+L\cos\delta.
\]

After multiplying by \(Z\), the four center projections onto the two
square frames are \(X_j\cos\delta+Y_j\sin\delta+C_j\), where

| Axis | \(X_j\) | \(Y_j\) | \(C_j\) |
|---|---:|---:|---:|
| source first | \(V\) | \(Vt\) | \(-aZ\) |
| source second | \(-Vt\) | \(V\) | \(atZ\) |
| target first | \(-W\) | \(Wu\) | \(bZ\) |
| target second | \(Wu\) | \(W\) | \(-buZ\) |

The two squares have disjoint interiors exactly when one of these four axes,
with some sign \(\varepsilon\in\{-1,1\}\), has nonnegative SAT numerator

\[
F_{j,\varepsilon}(\delta)
=2\varepsilon(X_j\cos\delta+Y_j\sin\delta+C_j)-Z
-|K\cos\delta-L\sin\delta|
-|K\sin\delta+L\cos\delta|.
\tag{2}
\]

This is the usual square separating-axis criterion multiplied by the
strictly positive factor \(2Z\). Boundary contact is included as equality.

For arbitrary signs \(s_c,s_s\), replacing the two absolute values in (2)
by the corresponding signed linear expressions gives an upper bound

\[
(2\varepsilon X_j-s_cK-s_sL)\cos\delta
+(2\varepsilon Y_j-s_sK+s_cL)\sin\delta
+2\varepsilon C_j-Z.
\tag{3}
\]

Taking the least of four valid interval upper bounds remains a valid upper
bound for that signed axis; taking the greatest over all eight signed axes
bounds every possible separating axis. A strictly negative result proves
interior overlap and hence excludes the pair. The code implements exactly
these operations. It does not infer a bound for a supremum by exchanging a
minimum in the wrong direction: \(\sup\min f_k\le\min\sup f_k\) is the
valid inequality used here.

## 3. The cost restriction only needs a finite gap interval

Let the width excess be

\[
e(\phi)=\frac{|\cos\phi|+|\sin\phi|-1}{2},
\qquad 0\le e(\phi)\le\frac{\sqrt2-1}{2}.
\]

The target pair inequality is

\[
H(\delta)=\delta-\frac9{50}e(\phi)
+\psi(u)-\psi(t)-\Gamma_{ij}\ge0.
\]

The function \(e\) is globally \(1/2\)-Lipschitz, including its quadrant
corners. Consequently \(H\) is strictly increasing in \(\delta\), with
increase at least \(91/100\) times the gap increase. The exact geometric
radial bounds imply \(\delta>3/5\) for every disjoint pair under study.

If \(H(\delta)<0\), then

\[
\delta<\Gamma_{ij}-\psi(u)+\psi(t)
+\frac9{50}\frac{\sqrt2-1}{2}.
\]

The code first takes an outward-rounded upper bound of this expression.
It then bisects the gap variable: whenever an interval lower bound for
\(H(d)\) is nonnegative simultaneously for every state in the tangent
box, monotonicity permits replacing the upper gap bound by \(d\).
An inconclusive evaluation never discards states. Finite bisection accuracy
can therefore affect running time but cannot remove a possible violating
pair. For the declared constants, the initial upper bound lies below
\(5/2\); the code refuses to continue otherwise.

## 4. Bounding a linear trigonometric expression

On the full declared gap interval \([3/5,5/2]\), sine is positive. Thus
an upper endpoint for the sine coefficient is safe. When the interval lies
below \(157/100<\pi/2\), cosine is also positive and the upper cosine
coefficient suffices. Otherwise both endpoint cosine coefficients are tested;
the supremum over a coefficient interval always occurs at one of its two
endpoints.

For fixed coefficients \(x,y\), the function
\(x\cos\delta+y\sin\delta\) has derivative
\(-x\sin\delta+y\cos\delta\). The gap interval has length below
\(\pi\), so this derivative has at most one zero unless it vanishes
identically. A maximum occurs at an endpoint or at an interior positive
stationary value \(\sqrt{x^2+y^2}\). Such an interior maximum requires a
nonnegative derivative at the left endpoint and a nonpositive derivative at
the right. The implementation includes the stationary bound whenever its
outward-rounded derivative intervals do not rule out that necessary sign
pattern. Extra stationary candidates only weaken the bound.

Endpoint trigonometric values use rational alternating Taylor bounds through
sine degrees 17 and 19 and cosine degrees 16 and 18. Their omitted tails
have the required decreasing alternating signs throughout \(|\delta|\le5/2\).
Every polynomial operation is enclosed with dyadic interval arithmetic.
Square roots use an approximate seed corrected by exact integer inequalities;
the seed is not trusted as a numerical bound.

## 5. Branch coverage and symmetry

There are four positive tangent domains, two signs on each, and eight closed
affine pieces per domain. For each type pair the verifier starts with every
one of the 64 piece rectangles and bisects closed tangent intervals. Children
cover their parent, including their common boundary. Internal subdivisions
of the gap interval have the same property. A tangent leaf is accepted only
when all possible gaps with negative cost are proved to overlap on every
signed SAT axis.

The symmetric \(\Gamma\) matrix and odd state potential allow reversal
plus reflection to reduce sixteen ordered type pairs to ten unordered pairs.
Indeed the transformation

\[
(i,j,t,u,\delta)\longmapsto(j,i,-u,-t,\delta)
\]

reflects the geometric pair and swaps its labels. It preserves disk/core
membership, width, gap, disjointness, and the corrected cost, since
\(\psi(-t)-\psi(-u)=\psi(u)-\psi(t)\).
Thus ten unordered type pairs times four sign choices gives the required
40 full branches. Each must pass, with all 64 piece rectangles included.
The endpoint \(t=0\) is safely duplicated by signs, and \(t=\pm1\)
represents equivalent square frames; both endpoint potentials are zero.

## 6. Completed coverage audit

The independent coverage check verified all forty expected type/sign branches,
each with exactly the 64 required piece pairs. It independently matched every
log hash, both source hashes, all rational potential/cost entries, every
strictly negative terminal bound, and the binary partition accounting. Totals:

| Item | Verified total |
|---|---:|
| Full branches | 40 |
| Initial closed piece rectangles | 2,560 |
| Tangent subdivision nodes | 3,746,056 |
| Terminal rectangles | 1,874,308 |
| Maximum depth | 24 |
| Largest terminal SAT upper numerator | -53,128 |
| Common dyadic denominator | 281,474,976,710,656 |

The authoritative manifest also matches the executable
`/tmp/verify_fourtype_pairs_ubsan`, whose dependency record includes the
undefined-behavior sanitizer. All forty runs completed successfully without
sanitizer output. The final source now rejects invalid optional piece indices,
resolving the minor vacuous-selection issue identified during audit.

No invalid geometric implication or unsound acceptance criterion was found.
The completed proof is computer-assisted: the interval partition is finite
and uses exact arithmetic, but these approximately 1.87 million terminal
rectangles have not been replaced by a short human-readable family of
continuous pair inequalities. That hand-conversion task is distinct from
soundness and completeness of the executed certificate.
