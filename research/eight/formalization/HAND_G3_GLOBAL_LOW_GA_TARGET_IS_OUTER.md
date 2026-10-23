# Global outer-anchor rigidity beside a zero edge

## 1. The low-index GA conclusion

On the same G0--G2 boundary cycle and with the same original
witnesses as HAND_G3_GLOBAL_PRIMARY_GA_TARGET_IS_OUTER.md:

**Theorem.** Any original GA0 or GA1 witness forces its target
A to be an outer boundary state.

The companion note proves the GA1 case without any other
owner, sign, mismatch, or frame-order hypothesis. We prove
GA0 here. The proof also yields the local reflected statement
in Section 3; its application makes B outer globally.

Write \(v=d_{HG}\), \(t=d_{GA}\), \(\kappa=49/50\), and
\(\Gamma=8833/10000\). The global zero--quarter propagation
theorem gives \(y_H=b_H>0,\ y_A=b_A>0\). Suppose A is core.
Then
\[
 a_A\le7/12,\qquad b_A<14/25,\qquad
 F_A<\frac15+\frac{27}{25}b_A.                         \tag{1}
\]
For the marker bound, use its exact core formula
\[
 F_A=7.506931(7/12-a_A)+1.077372b_A,
\]
together with \(a_A>447/800\):
\[
 7.506931(7/12-447/800)<1/5,\qquad1.077372<27/25.
\]
There is no fitted marker or new choice of vertex label.

The original GA0 inequality is
\[
             y_G+a_A\cos t+b_A\sin t\ge\widehat W(t).
                                                               \tag{2}
\]
The core bounds in (1) give \(a_A^2+b_A^2<1\). Therefore
(2) forces \(y_G>0\), since \(\widehat W(t)\ge1\).
The original HG owner is consequently 0 by the global
zero-owner sign theorem. Section 2 of the companion proves
the exact signed charge
\[
                         v+\kappa(b_H-y_G-1)\ge0.       \tag{3}
\]
In particular its treatment of a positive G tangent is
already supplied, with the same actual G circle.

## 2. The two-edge marker charge

Rearrange (2), use \(a_A\le7/12\), and subtract (1).
Since \(\cos t>0\),
\[
\begin{aligned}
 t+\kappa y_G-F_A
 &>t+\frac{\kappa}{2}-\frac15-\frac{\kappa}{12}\cos t
       +\frac{\kappa}{2}|\sin t|
       -\left(\frac{27}{25}+\kappa\sin t\right)b_A\\
 &\ge\frac{\kappa}{2}-\frac15-\frac{27}{25}\frac{14}{25}
                         +r(t),                       \tag{4}\\
 r(t)&=t-\frac{\kappa}{12}\cos t
       +\frac{\kappa}{2}|\sin t|-\kappa\frac{14}{25}\sin t.
\end{aligned}
\]
The coefficient of \(b_A\) in the first line is negative:
\(27/25+\kappa\sin t\ge27/25-\kappa=1/10>0\).
Thus its replacement by \(14/25\) is in the stated direction.

On \(0\le t\le7/10\), \(\sin t\le t\), \(\cos t\le1\)
give
\[
 r(t)\ge-\frac{\kappa}{12}
            +\{1-\kappa(14/25-1/2)\}t
       \ge-\frac{\kappa}{12}>-\frac3{20}.
\]
For \(t=-z\), \(0\le z\le7/10\), use
\(\sin z\ge z-z^3/6\) and \(\cos z\le1\):
\[
\begin{aligned}
 r(-z)
 &\ge-\frac{\kappa}{12}
       +\{\kappa(53/50)-1\}z-\frac{\kappa(53/50)}6z^3\\
 &\ge-\frac{\kappa}{12}
             -\frac{\kappa(53/50)}6(7/10)^3
       >-\frac3{20}.                                  \tag{5}
\end{aligned}
\]
Here \(\kappa(53/50)=2597/2500>1\).
Equations (4)--(5) prove
\[
                   t+\kappa y_G-F_A>-\frac{581}{1250}. \tag{6}
\]

The same original G1 marker satisfies
\(F_H\ge(43/50)b_H\). From (3), (6), and \(b_H<9/10\),
\[
\begin{aligned}
 C_2&=\frac\pi2+v+t+F_H-F_A\\
 &>\frac\pi2+\kappa-\frac3{25}\frac9{10}
                              -\frac{581}{1250}
  =\frac\pi2+\frac{509}{1250}
  >\frac\pi2+\frac{399}{1000}.                          \tag{7}
\end{aligned}
\]
The five unchanged complementary G1 edges contribute more
than \(5\Gamma\). Their same-vertex markers telescope with
C2, and the exact final contradiction in Section 4 of the
companion applies. Hence A is not core.

This proves both low-index GA alternatives, including
every tied original witness and both radial kinds at all
other vertices.

## 3. Generic form and reflected high-index form

The argument used the named roles only to specify one zero
edge followed by one quarter edge, with five complementary
G1 edges in the same seven-cycle. It therefore proves:

- On a zero edge followed by a quarter edge, an original
  quarter owner 0 or 1 forces that quarter's target outer.
- On a quarter edge followed by a zero edge, an original
  quarter owner 2 or 3 forces that quarter's source outer.

For the second statement apply the same local reflected
reversal used in
HAND_G3_GLOBAL_D_OWNER_BY_CYCLIC_MARKER.md, Section 11.
It swaps the endpoints and changes original owner numbers
\(0\leftrightarrow2,\ 1\leftrightarrow3\), preserving the
actual error and the marker charge. The retained signed
marker changes sign under the reflection, exactly as the
path direction reverses, so the complementary charge still
telescopes to \(2\pi\). Radial kind and the circle bound are
unchanged. This is an identity of the original witness
formulas and their common marker; no altered representative
or unproved orientation restriction is used.

Consequently, on the surviving role word:

- GA0/1 forces A outer, while GA2/3 forces G outer.
- Every original BT2/3 witness forces B outer.
- Every original EH2/3 witness forces E outer.

The complete global BT-owner theorem supplies BT2/3, so
**B is outer on every G0--G2 boundary candidate after the
established E-sign normalization**. The GA and EH conclusions
retain their displayed original-owner conditions.

All assertions refer to the witness-preserving radial
boundary representatives. They neither force the original
untranslated centers to touch the containing circle nor
replace the remaining mixed-owner or alignment arguments.
No numerical acceptance result, state or angle mesh, Lean
compilation, or CI enters the proof.
