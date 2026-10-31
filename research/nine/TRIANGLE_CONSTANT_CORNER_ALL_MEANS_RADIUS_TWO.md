# One table-free Fermat bound covers every constant-corner shared mean

Date: October 26, 2026.

**Status: complete hand scalar, geometric and original-physical proof,
accepted after full-source reviews in
REVIEW_TRIANGLE_CONSTANT_CORNER_ALL_MEANS_ROOT_2026_10_26.md and
REVIEW_TRIANGLE_CONSTANT_ALL_MEANS_BLOCK_2026_10_26.md.** This source supplies one
uniform radius bound for all constant-corner mean choices. Together
with the independently reviewed whole-nine-square R>2 theorem, it
replaces the two earlier constant-corner one-share and two-share
exclusions as current dependencies, including their twelve rational
three-by-three matrices. No parameter grid or coefficient packet is
used here.

The older matrix proofs remain valid historical alternatives. Their
stronger direct R<79/40 conclusions are not claimed by this source.
The new statement gives R<2, which suffices by
NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md. That single global geometric
certificate remains explicit; it is not erased or duplicated here.

## 1. A single two-variable inequality

For a,b>=0 put
\[
 D=\sqrt{a^2+ab+b^2},\qquad
 E=\sqrt{2a^2+(1+\sqrt3)ab+b^2}.
\tag{1}
\]
If a+b>0, then
\[
 \boxed{\qquad
 2D-\max\{E,\sqrt2D\}>\frac{5a+6b}{11}.
 \qquad}
\tag{2}
\]
For a=b=0 all terms vanish, so the weak inequality still holds.

### 1.1. The collapsed-endpoint branch

The exact quadratic identity
\[
 \frac{124}{3}D^2-(5a+6b)^2=\frac{(7a-4b)^2}{3}\ge0
\tag{3}
\]
gives
\[
 \frac{5a+6b}{11}\le\frac{\sqrt{124/3}}{11}D
                         <(2-\sqrt2)D.
\tag{4}
\]
For the final fixed comparison, positive squaring reduces it to
\[
              1027>726\sqrt2,
       \qquad1027^2-2\,726^2=577>0.
\tag{5}
\]
The intermediate algebra is
\(121(2-\sqrt2)^2-124/3=2054/3-484\sqrt2>0\).
Both sides before squaring are positive. This proves the strict
inequality in (2) when its maximum is the collapsed norm sqrt(2)D.

### 1.2. The original-corner branch

If a=0 and b>0, then 2D-E=b>6b/11. Otherwise divide by a,
put t=b/a>=0, and abbreviate
\[
 D_0=\sqrt{1+t+t^2},\quad
 E_0=\sqrt{2+(1+\sqrt3)t+t^2},\quad
 L=(5+6t)/11.
\]
The first squared difference is
\[
 4D_0^2-E_0^2-L^2=H/121,
\qquad
 H=217+(303-121\sqrt3)t+327t^2>0.
\tag{6}
\]
Its positivity follows coefficientwise from sqrt(3)<7/4. Direct
expansion gives the exact quartic
\[
 \begin{split}
 H^2-484E_0^2(5+6t)^2={}&22889
 +(61322-64614\sqrt3)t\\
 &+(201662-102366\sqrt3)t^2\\
 &+(151698-96558\sqrt3)t^3+89505t^4.
 \end{split}
\tag{7}
\]
Since t>=0, replacing sqrt(3) by its upper bound 7/4 gives a lower
bound Q(t)/2, where
\[
 Q(t)=179010t^4-34557t^3+45043t^2-103505t+45778.
\tag{8}
\]
This polynomial is positive on its entire half-line by one translated
quadratic comparison. Set y=t-1/2>=-1/2. The exact identity is
\[
 Q(t)=y^2\left(179010y^2+323463y+\frac{523445}{2}\right)
                   +\frac{20501}{4}y+\frac{48619}{4}.
\tag{9}
\]
The bracket increases for y>=-1/2: its derivative there is at least
144453>0. Its endpoint value is 289487/2>140000. Consequently
\[
 Q(t)\ge140000y^2+\frac{20501}{4}y+\frac{48619}{4}>0.
\tag{10}
\]
The last quadratic has negative discriminant, since
\(20501/4<6000\), \(48619/4>12000\), and
\(6000^2<4\cdot140000\cdot12000\). This is a complete
half-line proof, not a list of sampled polynomial signs.

Equations (6)--(10) show
\[
 H^2>484E_0^2(5+6t)^2,\qquad H>0.
\]
Taking positive square roots and dividing by121 yields
\(4D_0^2-E_0^2-L^2>2E_0L\). Thus
\(4D_0^2>(E_0+L)^2\), and another positive square root gives
\(2D_0-E_0>L\). This proves the other branch of (2), including
t=0. No denominator or squaring sign is left implicit.

## 2. The complete constant-corner geometric functional

Let f0,f1,f2 be a nonconstant counterclockwise force triangle;
collinear and coincident limits are included below. With cyclic
indices put
\[
 F_i=f_{i-1}-f_i,\qquad P=\sum_i|F_i|>0,
\qquad J(x,y)=(-y,x).
\]
Choose one constant bit chi in {0,1}, and define
\[
 g_i=\chi f_{i-1}+(1-\chi)f_i+JF_i,
\qquad k_i=\chi f_i+(1-\chi)f_{i-1}.
\tag{11}
\]
For arbitrary independent numbers \(0\le\delta_i\le1\), set
\[
 \Phi_{\boldsymbol\delta}(x)
 =\sum_i|f_i-x|
   +\sum_i|g_i-\delta_i k_i-(1-\delta_i)x|.
\tag{12}
\]

**Common-point theorem.** One Fermat point o of the original three
force points works for every mean triple simultaneously:
\[
                    \Phi_{\boldsymbol\delta}(o)<2P
                    \quad\text{for all }
                    \boldsymbol\delta\in[0,1]^3.
\tag{13}
\]
If all three force points coincide, the corresponding minimum is zero;
that is the only constant exception, and it does not occur in the
physical application.

Indeed
\[
 |g_i-k_i|=\sqrt2|F_i|
\]
for both constant bits, because \(g_i-k_i=(I+J)F_i\) for chi=1
and \((-I+J)F_i\) for chi=0. At any one fixed point x, norm
convexity gives the pointwise bound
\[
 \begin{split}
 |g_i-\delta_i k_i-(1-\delta_i)x|
 &\le(1-\delta_i)|g_i-x|+\delta_i\sqrt2|F_i|\\
 &\le\max\{|g_i-x|,\sqrt2|F_i|\}.
 \end{split}
\tag{14}
\]
Thus independent endpoint minimizers are never combined. The same
actual Fermat point is used before every one of the three mean
convexity bounds.

## 3. Interior Fermat points: cyclic cancellation handles all means at once

If o is not a force-triangle vertex, its three unit radial vectors
sum to zero and have successive angles120 degrees. Write
\(a_i=|f_i-o|>0\). In the counterclockwise order,
\[
 |F_i|=D(a_{i-1},a_i).
\]
For chi=1 one has \(|g_i-o|=E(a_{i-1},a_i)\); for chi=0
the two arguments of E are interchanged. These are exactly the
oriented-corner expansions in TRIANGLE_SQUARE_CORNER_FERMAT_BOUND.md.

Sum (2) cyclically. For either constant bit its linear right sides
sum to \(\sum_i a_i\). Therefore
\[
 \sum_i a_i+\sum_i\max\{|g_i-o|,\sqrt2|F_i|\}<2P.
\tag{15}
\]
Together with (14), this proves (13) for every independent mean triple
at once, without any restriction on the ratios of the positive a_i.

## 4. Every vertex, collinear and coincident Fermat alternative

If a Fermat point is a triangle vertex, relabel it f0=o=0. Write
\(p=|f_1|\), \(q=|f_2|\), \(S=p+q>0\), and
\(d=|f_1-f_2|\). If both rays are nonzero, their angle is at least
120 degrees by the usual sum-of-distances subgradient condition.
Consequently
\[
       d^2\ge p^2+pq+q^2\ge\frac34S^2,
                \qquad P=S+d.
\tag{16}
\]
The same inequalities hold if one ray vanishes, which covers every
coincident-point case with this Fermat point. For three distinct
collinear points, their median is a force vertex and the ray angle
is180 degrees, so (16) again applies. These cases exhaust all
nonconstant degenerate triples.

For chi=1, the three maxima in (14) are bounded respectively by
\[
            \sqrt2q,\qquad\sqrt2p,\qquad
                     \max\{\sqrt2p+q,\sqrt2d\}.
\tag{17}
\]
For the third entry, use
\(g_2=(I+J)f_1-Jf_2\) and the triangle inequality. For chi=0
the reflected statement exchanges p and q. It therefore suffices
to prove both of the following strict inequalities:
\[
 (1+\sqrt2)S+\sqrt2d<2(S+d),
\tag{18}
\]
\[
 (1+\sqrt2)S+\sqrt2p+q<2(S+d).
\tag{19}
\]
The difference in (18) is
\((2-\sqrt2)(d-S/\sqrt2)>0\), by (16) and
\(\sqrt3/2>1/\sqrt2\).

For (19), the exact complete square is
\[
 \begin{split}
 4(p^2+pq+q^2)-[(2\sqrt2-1)p+\sqrt2q]^2
  ={}&2\left(q-(1-\sqrt2/2)p\right)^2\\
    &+(6\sqrt2-8)p^2>0.
 \end{split}
\tag{20}
\]
The last coefficient is positive because sqrt(2)>4/3. The entire
expression is strictly positive for every p,q>=0 with p+q>0,
including p=0. Both sides in the associated square-root comparison
are nonnegative, and (16),(20) give
\[
                  2d>(2\sqrt2-1)p+\sqrt2q.
\]
This is exactly (19). Equations (17)--(19) prove (13) in every
remaining Fermat case. No limiting equality case has been discarded.

## 5. Original physical join: arbitrary constant-corner shares imply R<2

Retain the entire original nine-unit packing and its selected
alternating six-cycle with three physically unique-circle-corner
loaded units and three true unloaded side-normal transmitters.
Assume only the accepted actual adjacent-side normal form and
a constant actual corner bit chi. All original positive forces,
physical interfaces and actual application means remain fixed.

Write the original forces as \(f_i=\mu_i n_i\), \(\mu_i>0\),
and the actual directed loaded chords as \(\ell_i u_i\),
\(0<\ell_i\le1\). Put \(\delta_i=1-\ell_i\).
At a nonshared body delta_i=0. At a genuinely shared body, the
accepted mean-preserving normal form forces an outgoing share when
chi=1 and an incoming share when chi=0. Substituting those actual
means into the unchanged support-vector identity gives precisely
\[
                    g_i^{\rm actual}=g_i-\delta_i k_i,
       \qquad u_i=g_i^{\rm actual}/|g_i^{\rm actual}|.
\tag{21}
\]
For chi=1 the actual endpoints are (0,ell_i), giving
\(g_i^{\rm actual}=f_{i-1}+JF_i-\delta_i f_i\).
For chi=0 they are (delta_i,1), giving
\(g_i^{\rm actual}=f_i+JF_i-\delta_i f_{i-1}\).
In particular a genuine shared mean at a side endpoint, delta_i=0,
retains its original genuine contact type. No mean has been selected
after the physical certificate was fixed.

The true channel equations imply
\[
                  \sum_i n_i+\sum_i\ell_i u_i=0,
\tag{22}
\]
and the exact original virial identity is
\[
          RP=\sum_i\mu_i+\sum_i|g_i^{\rm actual}|
                         =\Phi_{\boldsymbol\delta}(0).
\tag{23}
\]
Every actual support vector in (21) is nonzero. The functional (12)
is convex in x, and (22) says exactly that its gradient vanishes
at zero. Thus the original point is a global minimum. The original
force triangle is nonconstant and counterclockwise, so P>0 and
the common-point theorem applies. Hence
\[
 RP=\Phi_{\boldsymbol\delta}(0)
       \le\Phi_{\boldsymbol\delta}(o)<2P,
                   \qquad\boxed{R<2.}
\tag{24}
\]
Only necessary consequences of the true full channel equations were
used. They do not replace containment, actual contact restrictions,
nonoverlap, original transmitter sliders or any of the three extras.

## 6. Exact scope and certificate replacement

The whole-nine-square theorem NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md
gives R>2 for these same nine unchanged squares. It contradicts (24).
Thus every constant-corner all-unique side C6 is excluded, simultaneously
for zero, one, two or three genuine shares and every original mean.

In particular the constant one-share and constant two-share rows in
SIX_CYCLE_ALL_UNIQUE_SIDE_COMPLETE_EXCLUSION.md may use this single
proof instead of their earlier six-matrix proofs. The exact retired
obligations are those twelve displayed rational three-by-three matrix
positivity checks. The previous stronger R<79/40 matrix bounds remain
historical alternatives; this source proves the radius bound needed
for the new common global lower bound without either matrix packet.

No new original gate is introduced by this simplification. It does
not identify physically radial two-corner loads with unique-corner
loads, close any remaining radial parent, or strengthen the global
radius-two lower bound to the sharp target1105/256. The global measure certificate, now reduced from208 charges to five
fixed mass checks, one fixed derivative enclosure and displayed
analytic comparisons, is a single separately counted dependency,
and every other inherited packet remains explicitly outside this
replacement. No Lean compilation or CI was run.
