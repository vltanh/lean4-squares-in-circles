# Independent review: isosceles common side with two owned exits

Reviewed November 1, 2026, by a noncontributor to the theorem under review.
Source:
[`../../ISOSCELES_COMMON_SIDE_WITH_TWO_OWNED_EXITS_EXCLUSION_2026_11_01.md`](../../ISOSCELES_COMMON_SIDE_WITH_TWO_OWNED_EXITS_EXCLUSION_2026_11_01.md).

**Verdict:** the exact stated feature is excluded by a complete hand proof of
\(R>13/6\). All coordinate, force, torque, mean, and variance expressions were
independently derived. No gap was found. In particular the orientation reversal
in the displayed \(B\)-frame is correctly handled by the stated formula for
\(t_B\); an explicit derivation is supplied below.

This review does not assert that every remaining distinct-contact triangle has
the stated ownership pattern. The common-side and two-owned-exit hypotheses
remain essential inputs to this feature theorem.

## 1. The chart covers the full stated physical feature

The adjacent original vertices on \(A\) and \(B\) give the two unit sides of
the contact triangle. The two distinct original \(C\)-applications lie on one
actual side of length one, so their separation satisfies \(0<d\le1\).
Consequently, after a rigid chart change and reflection if necessary, the
three original points have precisely the stated coordinates, with
\(h^2+d^2/4=1\) and \(0<h<1\).

Even when \(C\)'s horizontal center is not the midpoint of its two applications,
that midpoint is strictly inside its side interval because the applications
are distinct. If \(C\) extended above the common side, \((0,h)\) would therefore
be strictly inside \(C\), contradicting its membership in the other actual
squares. Thus \(C\) is below the side; its lower side has height \(-1\), without
any horizontal-center normalization.

For \(A\), the other base contact has coordinates \(d^2/2\) along its unit
contact side and \(dh\) inward from it. Both lie strictly between zero and one:
\(0<d^2/2\le1/2\) and \(0<dh<1\). An inward choice would place that original
\(B,C\) contact in \(\operatorname{int}(A)\), causing overlap. The same reasoning
applies to \(B\). Hence the two outward frames describe every configuration
within the stated domain.

At either original application on \(A\)'s base side, every permitted supporting
force has nonpositive \(v_A\)-component. The \(A\)-to-\(C\) force has strictly
negative component \(-ad/2\). Complete unloaded translation therefore gives
the exit a positive \(v_A\)-component. Of the four assumed own-axis exits,
only \(+v_A\) is possible. This argument does not require a strict internal
singleton normal and includes the permitted endpoint/tie cases. It likewise
forces \(+v_B\) at \(B\).

## 2. Complete original forces and the two frame determinants

Summing the three full core translations gives

\[
 z_Av_A+z_Bv_B-(0,a+b)=0.
\]

Since \(h>0\), the horizontal component gives \(z_A=z_B=z>0\), and the vertical
component gives \(a+b=zd\). The original \(A\)-to-\(B\) force is consequently
\(f=(zh,a-zd/2)\).

The \(A\)-frame has \(\det(u_A,v_A)=+1\). About its original contact \(P_{AC}\),
the retained moment equation is

\[
 \det(u_A,f)+zt_A
 =\frac{ad}{2}-z+zt_A=0,
\]

so \(t_A=1-ad/(2z)\).

The \(B\)-frame has **negative** determinant:
\(\det(u_B,v_B)=-1\). Its internal force at \(P_{AB}\) is \(-f\). Directly,

\[
 \det(u_B,-f)=\frac{ad}{2}+z\left(1-\frac{d^2}{2}\right),
 \qquad
 \det(v_B+t_Bu_B,zv_B)=-zt_B.
\]

Their sum is zero, giving

\[
 t_B=1-\frac{d^2}{2}+\frac{ad}{2z}
     =1-\frac{bd}{2z},
\]

where the last identity uses \(b=zd-a\). Thus the source's \(B\)-formula has the
correct sign despite the reflected coordinate frame.

At \(C\), the original upward forces at \((-d/2,0)\) and \((d/2,0)\), and its
downward exit at \((m,-1)\), give

\[
 -\frac{ad}{2}+\frac{bd}{2}-(a+b)m=0,
 \qquad m=\frac{b-a}{2z}.
\]

All three equations determine coordinates of the **unchanged** original means.
There is no reapplication of a force at a chosen vertex or centered point.

## 3. Actual outside points and their exact coordinates

The unit-step lemma is valid for every actual outside square and original
minimum-support mean: a nonzero normal component moves inward from its
minimizing side-coordinate endpoint by at most one, while a zero component
leaves that coordinate unchanged. Therefore all three displayed \(w\)-points
belong to their unchanged outside neighbors, including repeated terminals.

With \(r=(b-a)/z\), one has \(-d<r<d\) and

\[
 t_A=h^2+\frac{rd}{4},\qquad t_B=h^2-\frac{rd}{4}.
\]

Independent substitution gives

\[
 w_A=\left(-D+\frac{rd^2}{8},\ h^3+d+\frac{rdh}{4}\right),
\]

\[
 w_B=\left(D+\frac{rd^2}{8},\ h^3+d-\frac{rdh}{4}\right),
 \qquad w_C=\left(\frac r2,-2\right),
 \qquad D=2h+\frac{d^3}{8}.
\]

Thus the manuscript's \(M\), \(V\), and \(M-w_C\) formulas follow exactly,
using \(d^2-4=-4h^2\). In particular dropping their nonnegative \(r^2\)-terms
gives the stated lower bounds \(|V|^2\ge D^2\) and
\(|M-w_C|^2\ge H^2\), with \(H=h^3+d+2\). No equal-weight or symmetric-force
assumption was made.

## 4. Variance optimization and the strict uniform lower bound

For weights \(t/2,t/2,1-t\), the exact variance decomposition is

\[
 \operatorname{Var}=t|V|^2+t(1-t)|M-w_C|^2.
\]

Because all three points lie in the original disk, their weighted squared
distance to the actual disk center is at most \(R^2\); subtracting the squared
displacement of their weighted centroid proves \(\operatorname{Var}\le R^2\).

The source's elementary bound on \(h^3\) gives
\(H\ge3+5d/8\ge3\), and \(D\le17/8<3\). Hence
\(t=(D^2+H^2)/(2H^2)\) is strictly between zero and one. Substitution produces
\(R\ge(D^2+H^2)/(2H)\) with no change in inequality direction.

The positive-square proof of \(h^3\ge1-3d^2/8\) is valid on
\(0<d^2/4\le1/4\). The function \(X^2-(13/3)X\) is increasing for \(X\ge3\).
Consequently the final calculation is exactly

\[
 \begin{aligned}
 D^2+H^2-\frac{13}{3}H
 &\ge 4-d^2+\left(3+\frac{5d}{8}\right)^2
       -\frac{13}{3}\left(3+\frac{5d}{8}\right)\\
 &=\frac{25d}{24}-\frac{39d^2}{64}\\
 &\ge\left(\frac{200}{192}-\frac{117}{192}\right)d
   =\frac{83d}{192}>0.
 \end{aligned}
\]

The last step uses \(0<d\le1\), including the endpoint \(d=1\); the strictness
comes from the expressly assumed distinct applications, not a hidden minimum
contact separation. This proves \(R>13/6\). The comparison
\(169/36-1105/256=871/2304>0\) is also exact.

## 5. Adoption boundary

The complete feature can be marked independently reviewed. The theorem keeps
all three original internal forces, all three full exits, and the actual mean
on every exit. It is uniform over outside frames, repeated terminals, and all
other actual squares. It does not cover different \(C\)-owned sides, non-owned
exits at \(A\) or \(B\), or unrelated vertex/side ownership patterns. No full
original parent or canonical inventory count changes from this review alone.
