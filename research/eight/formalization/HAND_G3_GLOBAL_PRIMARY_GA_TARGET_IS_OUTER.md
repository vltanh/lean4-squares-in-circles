# A global GA1 witness has an outer target

## 1. Statement on the original boundary cycle

Work on the G0--G2 boundary cycle at
\[
 Q=\frac{9789}{2500},\qquad
 \Gamma=\frac{8833}{10000},\qquad \kappa=\frac{49}{50}.
\]
Keep the original separating witnesses, the same G1 marker at
each shared vertex, and the full frame interval of length less
than \(7/10\). No mismatch bound, tangent cut, frame order,
E sign, or BT/DE owner restriction is assumed.

**Theorem.** If an original GA witness has owner 1, its target
A cannot be a core boundary state. Thus A is an outer state
in the witness-preserving boundary reduction.

This is a radial restriction on that boundary cycle. It does
not assert that the original, untranslated A center was on
the containing circle, nor does it exclude the GA1 witness.

The global zero--quarter sign propagation theorem
HAND_G3_GLOBAL_A_SIGN_UNDER_FORBIDDEN_B_OWNER.md applies to
HG--GA and gives \(y_H=b_H>0,\ y_A=b_A>0\).
Write \(y_G\) for the signed G tangent, allowing either sign,
and put
\[
                    v=d_{HG},\qquad t=d_{GA}.
\]
The actual GA1 inequality is
\[
             a_A+a_G\sin t+y_G\cos t\ge\widehat W(t),
 \qquad \widehat W(t)=\frac{1+\cos t+|\sin t|}{2}.       \tag{1}
\]
The global coordinate bounds are
\[
 L=\frac{447}{800}<a_i<U=\frac{283}{200},
 \qquad |y_i|<c_0<\frac9{10},\qquad |v|,|t|<\frac7{10}.
                                                               \tag{2}
\]

## 2. A signed HG charge, including a positive G tangent

Every actual HG witness satisfies
\[
                    v+\kappa(b_H-y_G-1)\ge0.           \tag{3}
\]
If \(y_G\le0\), this follows directly from the all-sign
zero-edge theorem HAND_G4_ALL_SIGN_ZERO_LINEAR_CHARGE.md:
its clipped labels are exactly \(b_H\) and \(-y_G\), and
its retained \(h(|v|)/50\) term is nonnegative.

Suppose \(y_G>0\). The global zero-owner sign theorem
excludes HG2, so the original witness is HG0:
\[
                  b_H+a_G\sin v-y_G\cos v\ge\widehat W(v).
\]
It forces \(v>0\), since otherwise its projection is at most
\(b_H<1\). Rearrangement and the actual G corner circle give
\[
\begin{aligned}
 1-b_H+y_G
 &\le(a_G-\tfrac12)\sin v+(y_G+\tfrac12)(1-\cos v)\\
 &\le2\sqrt Q\sin(v/2)-\sin v.
\end{aligned}                                                   \tag{4}
\]
The last line is one Cauchy support of the shifted G corner.
Consequently the left side of (3) is at least
\[
               f(v)=v+\kappa\sin v-2\kappa\sqrt Q\sin(v/2).
\]
This function is strictly concave on \((0,7/10]\), because
\[
 f''(v)=\kappa\sin(v/2)\{\sqrt Q/2-2\cos(v/2)\}<0.
\]
It vanishes at zero and is positive at \(7/10\).
For an entirely rational endpoint check, use
\(\sqrt Q<1979/1000\), the degree-seven lower sine
polynomial at \(7/10\), and the degree-five upper sine
polynomial at \(7/20\). They give \(f(7/10)>1/1000\).
Concavity now proves (3) on the whole interval.

## 3. A core target forces a large two-edge angle

Suppose, for contradiction, that A is core. Then
\[
                         a_A\le\frac7{12}.
\]
Since \(\cos t>0\), (1) implies the signed lower bound
\[
 y_G\ge\frac12-\frac1{12}\sec t+
                    \frac12|\tan t|-a_G\tan t.        \tag{5}
\]
We claim that, for either sign of t,
\[
                         t+\kappa y_G>\frac{327}{1000}. \tag{6}
\]

For \(0\le t\le7/10\), use \(a_G<U\) in (5). It suffices
to bound
\[
 j(t)=t-\frac{\kappa}{12}\sec t
                         -\kappa(U-\tfrac12)\tan t.
\]
Both \(\sec t\) and \(\tan t\) are convex on this interval,
so j is concave. At zero, \(j(0)=-49/600>-163/1000\).
The elementary whole-interval bounds
\[
                  \sec(7/10)<\frac{131}{100},\qquad
                  \tan(7/10)<\frac{843}{1000}           \tag{7}
\]
give
\[
 j(7/10)>
 \frac7{10}-\frac{49}{600}\frac{131}{100}
       -\frac{49}{50}\frac{183}{200}\frac{843}{1000}
 >-\frac{163}{1000}.
\]
Concavity gives this lower bound everywhere. Adding
\(\kappa/2=49/100\) proves (6).
For (7), the degree-six lower cosine polynomial at
\(7/10\) exceeds \(100/131\), and \(843/1000\) times that
cosine polynomial exceeds the degree-five upper sine
polynomial at the same point.

For \(t=-z\le0\), use \(a_G>L\) in (5). Now
\[
 t+\kappa y_G\ge\frac{\kappa}{2}
       -z-\frac{\kappa}{12}\sec z+\kappa(L+\tfrac12)\tan z.
\]
Here \(\kappa(L+1/2)=41503/40000>1\) and \(\tan z\ge z\).
Thus this expression is greater than
\[
               \frac{49}{100}-\frac{49}{600}\frac{131}{100}
                            >\frac{327}{1000},
\]
which proves (6) also on the negative half.

Combine (3), (6), and \(b_H<9/10\). The result is
\[
\begin{aligned}
 v+t+\frac{43}{50}b_H
 &\ge\kappa+t+\kappa y_G+
                          (\tfrac{43}{50}-\kappa)b_H\\
 &>\frac{49}{50}+\frac{327}{1000}
                            -\frac3{25}\frac9{10}
  =\frac{1199}{1000}.                                  \tag{8}
\end{aligned}
\]

## 4. The unchanged G1 markers close the cycle

The whole-chart marker bound in
HAND_G3_BT_PATH_MARKER_AND_NEGATIVE_AB_COMPARISON.md gives
\[
                           F_H\ge\frac{43}{50}b_H.
\]
A core A has \(b_A<14/25\), \(a_A>L\), and
\[
 F_A=7.506931(7/12-a_A)+1.077372b_A<\frac45.             \tag{9}
\]
The final inequality follows already by substituting
\(a_A>L,\ b_A<14/25\); all decimals here are exact rationals.

The actual uncharged G1 marker sum on HG--GA is
\[
                        C_2=\frac\pi2+v+t+F_H-F_A.
\]
Equation (8) and (9) imply
\[
                        C_2>\frac\pi2+\frac{399}{1000}. \tag{10}
\]
The five unchanged complementary edges each have marker
charge greater than \(\Gamma\), after discarding only their
nonnegative width-cusp terms. Their marker contributions
telescope with this same C2. Therefore the full cycle would
satisfy
\[
             2\pi>C_2+5\Gamma
                    >\frac\pi2+\frac{399}{1000}+5\Gamma.
\]
But \(\pi<22/7\) gives the strict excess
\[
 \frac{399}{1000}+5\Gamma-\frac{3\pi}{2}
 >\frac{399}{1000}+5\frac{8833}{10000}-\frac{33}{7}
 =\frac{1417}{14000}>0,
\]
a contradiction.

Thus A is outer whenever GA1 is an original feasible witness.
All source signs, both HG owners, radial kinds at H/G, and
weak original-axis ties were retained. The proof uses two
one-variable concavity comparisons and exact rational
endpoint bounds; no mesh, numerical acceptance premise,
Lean compilation, or CI is used.
