# A hand inequality for the same-sign outer pair near a quarter turn

Let \(Q=9789/2500\), \(R=\sqrt Q\), \(p=13/200\), \(q=203/200\),
and \(\ell(a,b)=-9/100+pa+qb\). Both states \((a,b),(A,B)\)
belong to the positive outer arc

\[
 0\le b\le a,\quad 0\le B\le A,\qquad
 (a+\tfrac12)^2+(b+\tfrac12)^2
 =(A+\tfrac12)^2+(B+\tfrac12)^2=Q.
\]

Put \(\phi=\pi/2+x\), \(-7/10\le x\le7/10\). Separation on
the positive source secondary axis means

\[
 b+A\cos x+B\sin x
 \ge \frac{1+|\sin x|+\cos x}{2}.                         \tag{1}
\]

**Theorem.** Under these assumptions,

\[
 \boxed{\phi+\ell(a,b)-\ell(A,B)>\frac{157}{200}=.785.}   \tag{2}
\]

The proof below treats the entire named frame interval, without any
additional restrictions on the two states or on the center-angle gap.

## 1. A constant multiplier and two circle supports

Choose \(\lambda=39/40=.975\). Subtracting \(\lambda\) times
the nonnegative margin in (1) leaves the source functional

\[
 pa+(q-\lambda)b=pa+\frac1{25}b.
\]

As a function of \(b\), its second derivative is negative, because
\(a=\sqrt{Q-(b+1/2)^2}-1/2\) is strictly concave and \(p>0\).
Its minimum on the closed arc is therefore at an endpoint.
Those endpoints are \((a_0,0)\) and \((c,c)\), where
\(a_0=\sqrt{Q-1/4}-1/2>1.4145\) and
\(c=\sqrt{Q/2}-1/2>.899\). Direct multiplication gives

\[
 pa_0>.0919,\qquad (p+q-\lambda)c>.0919.
\]

Thus the source functional is greater than \(.0919\) everywhere.
For the target functional
\[
 (-p-\lambda\cos x)A+(-q-\lambda\sin x)B,
\]
enlarge the arc to its full circle. Its lower support bound is

\[
 \frac{p+q+\lambda(\cos x+\sin x)}2-RN(x),
\qquad
 N^2=p^2+q^2+\lambda^2+2\lambda(p\cos x+q\sin x).
\]

It follows that the cost in (2) is strictly greater than

\[
 F(x)=\frac\pi2+x+.0919+\frac{p+q+\lambda}{2}
       +\lambda\cos x+\lambda\max(\sin x,0)-RN(x).
                                                               \tag{3}
\]

## 2. Concavity on each side of zero

The circle-norm identity, obtained by twice differentiating \(N^2\),
is

\[
 N''+\frac N4
   =\frac{(p^2+q^2-\lambda^2)^2}{4N^3}\ge0.              \tag{4}
\]

The norm is positive and increases throughout \([-.7,.7]\). Indeed,
the derivative of its square has the sign of
\(-p\sin x+q\cos x\), which is at least
\(-.7p+q(1-.7^2/2)>0\).

On \([-.7,0]\), use

\[
 N\le N(0)<1.454,\qquad \cos x>.764,\qquad R<2.
\]

The two root bounds follow by squaring and the cosine bound follows
from its alternating Taylor polynomial. Equations (3) and (4) imply

\[
 F''=-\lambda\cos x-RN''
 \le-\lambda\cos x+\frac R4N
 <-.975(.764)+\frac{1.454}{2}<0.                          \tag{5}
\]

On \([0,.7]\), one has \(\cos x+\sin x\ge1\). Also \(N<1.85\):
using \(\cos x\le1\), \(\sin x<.645\), it is enough to check

\[
 p^2+q^2+\lambda^2+2\lambda(p+.645q)<1.85^2.
\]

Hence on this second interval,

\[
 F''=-\lambda(\cos x+\sin x)-RN''
 \le-\lambda(\cos x+\sin x)+\frac R4N
 <-.975+\frac{1.85}{2}<0.                                \tag{6}
\]

Each interval therefore has its minimum at an endpoint. Only
\(-.7,0,.7\) need to be checked; no differentiability of \(F\)
across zero is being asserted.

## 3. All remaining numerical comparisons

Use the rational bounds

\[
 \pi>3.14159,\quad R<1.979,\quad
 .6442<\sin(.7)<.64424,\quad
 .76484<\cos(.7)<.764844.
\]

The sine bounds follow from the alternating Taylor polynomials of
degrees seven and five; the cosine bounds follow from degrees six
and eight. The bound for \(\pi\) has the short Machin-series proof in
LOW_HIGH_ALIGNED_CONTACT_HAND_PROOF.md.

Substituting these estimates in (3) gives the following complete table.

| \(x\) | Upper \(N(x)\) | Lower \(F(x)\) |
|---|---:|---:|
| \(-7/10\) | \(9/10\) | \(477407/500000\) |
| \(0\) | \(727/500\) | \(787729/1000000\) |
| \(7/10\) | \(37/20\) | \(1102859/1000000\) |

For the first norm bound, use
\[
 N(-.7)^2
 \le p^2+q^2+\lambda^2+
         2\lambda\bigl(p(.764844)-q(.6442)\bigr)<.9^2.
\]
The other two norm bounds were proved above. Each lower \(F\)
entry is obtained by using the lower cosine, the lower nonnegative
sine where applicable, and the upper norm in (3).

All three lower values exceed \(.785\). Together with (5) and (6)
this proves (2). The optional arithmetic replay
verify_quarter_one_outer_same_hand.py checks precisely the displayed
rational comparisons. \(\square\)
