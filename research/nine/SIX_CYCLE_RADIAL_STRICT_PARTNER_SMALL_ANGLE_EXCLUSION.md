# A small radial-port angle forces a strict partner to own the return channel

Date: October 26, 2026.

**Status: accepted complete analytic local theorem and original-feature
join**, after full reviews in
REVIEW_C6_RADIAL_STRICT_SMALL_ANGLE_ROOT_2026_10_26.md and
REVIEW_C6_RADIAL_STRICT_PARTNER_SMALL_ANGLE_CERTIFICATE_REDUCTION_2026_10_26.md. No original parent gate is claimed closed.

Retain the original alternating all-side C6 with one physically radial
loaded square S, two physically unique loaded squares, and three true
unloaded degree-two side transmitters. Every force, actual mean, mean
endpoint, transmitter slider and physical square is unchanged. Work in
\[
 2\le R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-1/4}-1,\qquad r_0^2=d^2+1/4.
\tag{1}
\]
The lower endpoint is available for an actual nine-square completion
from the accepted global measure theorem, which gives strictly \(R>2\).

At either original radial inner-vertex port, reflect the complete chart
if needed to write
\[
 P=(d,1/2),\qquad G=(-\cos\beta,\sin\beta),
                     0<\beta<\pi/2.
\tag{2}
\]
Here G is the actual unit direction from S through its reserve-one
transmitter toward the unique endpoint. The physical unique endpoint
is assumed to have turn strictly greater than \(\pi/2\).

**Local theorem.** If \(\beta\le2/7\), this strict endpoint must be
type T in the accepted A/M/O/T cover: its S-incident application is its
opposite-to-circle vertex, and it genuinely owns the original return
channel. Types A, M and O are all impossible. Type T is not excluded
by this local statement.

**Low-turn consequence.** In the complementary one-radial domain where
the other unique endpoint has turn at most \(\pi/2\), if its actual
S-incident application is adjacent to its actual circle corner, then
the strict partner must be T. This removes every A, M and O partner
at once for all such original low-turn rows. No original mean is
replaced by an adjacent vertex to obtain this premise.

## 1. Uniform constants and the A and M cases

Throughout (1),
\[
                  187/200<d<61/60.
\tag{3}
\]
These are positive-square comparisons already used in the accepted
radial sources: at \(R=2\), the lower comparison has reserve
\(231/40000\); the upper comparison follows from
\((121/60)^2-1041/256=31/57600>0\).

If \(0<\beta\le2/7\), put
\[
 k=d\cos\beta-\tfrac12\sin\beta,
 \qquad w=1-k,
 \qquad h=d\sin\beta+\tfrac12\cos\beta.
\tag{4}
\]
The actual scalar products in (2) are \(P\cdot G=w-1\) and
\(\det(P,G)=h\). Elementary sine and cosine bounds give
\[
 w<1-\frac{187}{200}\frac{47}{49}+\frac17
     =\frac{2411}{9800}=:w_*<\frac14.
\tag{5}
\]
Also
\[
 h<\frac{61}{60}\beta+
       \frac12\left(1-\frac{\beta^2}{2}+\frac{\beta^4}{24}\right)
 \le\frac{27739}{36015}<\frac{39}{50}=:h_*.
\tag{6}
\]
The polynomial in (6) increases on \([0,2/7]\), since its derivative
exceeds \(61/60-1/7>0\). The last reserve is
\(39/50-27739/36015=3527/360150>0\). These are whole-interval
elementary inequalities, not sampled angle checks.

For type A, its actual S-incident application is an adjacent vertex.
The accepted near-corner lemma in
`SIX_CYCLE_ONE_RADIAL_LOW_TURN_FEATURE_COVER.md`, Section 4, gives
\(\beta>1/2\), contradicting \(\beta\le2/7\).

For type M, use its unchanged actual orthonormal own axes v,u as in
`SIX_CYCLE_ONE_RADIAL_TWO_SHARED_MEANS_STRICT_TURN_CLASSIFICATION.md`,
Sections 1--2. The S-incident mean is on its inner v-normal side;
its strict-turn other application is the opposite vertex. Write
its actual circle corner as \(z=av+bu\). The original proper
concurrence and mean give
\[
 a>b>1/2,
 \qquad P=(a-2)v+\tau b\,u,
 \qquad G=v,
 \qquad 0<\tau\le1.
\tag{7}
\]
Only this local chart is imported; no premise about the other unique
endpoint is used. In particular every genuine mean endpoint is kept.
Taking the scalar product with G in (7) and (4),
\[
              a=1+w<1+w_*<7/5<\sqrt2\le R/\sqrt2.
\tag{8}
\]
But \(a>b\) and \(a^2+b^2=R^2\) give \(a>R/\sqrt2\), a
contradiction. The rational reserve in (8) is
\(7/5-(1+w_*)=1509/9800>0\).

## 2. The entire O chart in radial-port coordinates

Type O has its actual S-incident application at the opposite vertex,
and its other application is a nonshared adjacent vertex. Choose
the actual own coordinates, and reflect the complete local chart
when necessary, so these applications are respectively
\[
 Q=(a-1,b-1),\qquad T=(a-1,b),
 \qquad a>b>1/2,\qquad a^2+b^2=R^2.
\tag{9}
\]
The original concurrence is \(q=(1-t)(a,b)\). Let
\[
 X=1-ta>0,\qquad Y=1-tb>0,\qquad
 L=\sqrt{X^2+Y^2},\qquad x=X/L,\quad y=Y/L.
\tag{10}
\]
Its actual S-to-O normal is G=(x,y), and its actual radial port
is \(P=Q-G\). Since \(a>b\), the case \(t=0\) would make
\(x=y\); this case is retained initially below and will be excluded
by the exact moment identity. For \(t>0\), \(0<x<y<1\).

The positive actual common moment fixes the sign of
\(\det(P,G)\) to be h in the matching reflected version of (2).
Therefore decomposition in the orthonormal G, JG frame gives exactly
\[
 a=1+wx+hy,\qquad b=1+wy-hx.
\tag{11}
\]
Put
\[
                         m=x+y,\qquad n=y-x.
\tag{12}
\]
Thus \(m^2+n^2=2\), and \(m>0,n\ge0\). Squaring (11),
using \(w^2+h^2=1+r_0^2-2k\) and
\(R^2-r_0^2=2d+1\), gives the exact circle identity
\[
                         \boxed{w(m+1)+hn=d.}
\tag{13}
\]

The concurrence identities in (10) also give
\[
 n=t(ay-bx)=t(n+h),\qquad
                 L=\frac{hm-nw}{h+n}.
\tag{14}
\]
If \(t=0\), then \(n=0\), \(m=\sqrt2\), and (13) would imply
\(d=w(1+\sqrt2)<w_*\,17/7<187/200<d\), a contradiction.
Consequently \(t>0\), \(0<n<1\), and \(0<x<y<1\) in the
remaining comparison. This also shows that no force-angle boundary
was silently lost at \(t=0\).

The directed return normal at T is proportional to
\((-X,1-Y)\). The assumed strict unique turn therefore says
\[
                     -X^2+Y(1-Y)<0,
 \quad\text{equivalently}\quad L>y.
\]
Substituting (14), with its positive denominator, gives
\[
                              hx>n(w+y).
\tag{15}
\]
This is the essential strict-turn input. It is not available for
an O-shaped low-turn endpoint and is not asserted there.

## 3. One whole-domain contradiction for O

Suppose \(\beta\le2/7\). Then (3),(6) give \(h<d\).
If \(w\le0\), (13) would give \(d\le hn<h<d\), impossible.
Thus
\[
                                w>0.
\tag{16}
\]

We claim \(n<3/7\). Otherwise, because
\(m=\sqrt{2-n^2}\),
\[
 \frac{x}{y}=\frac{m-n}{m+n}
 \le\frac{\sqrt{89}-3}{\sqrt{89}+3}
 <\frac{13}{25}.
\tag{17}
\]
The ratio decreases as n increases, and the last comparison uses
\(\sqrt{89}<19/2\). Equations (15)--(17) would then give
\[
             n<h\frac{x}{y}<\frac{39}{50}\frac{13}{25}<\frac37,
\]
with exact final reserve \(201/8750>0\), a contradiction.

Finally \(m+1\le1+\sqrt2<17/7\). The exact circle identity
(13), the newly proved \(n<3/7\), and (5)--(6) imply
\[
 \begin{split}
 d&<\frac{2411}{9800}\frac{17}{7}
                      +\frac{39}{50}\frac37\\
  &=\frac{187}{200}-\frac{111}{34300}
   <\frac{187}{200}<d.
 \end{split}
\tag{18}
\]
This excludes the entire O case for \(\beta\le2/7\), with no
subdivision of the force ratio, circle angle, actual concurrence
parameter, or physical contact.

## 4. Exact join to the original low-turn cover

The accepted full low-turn cover gives exactly one unique turn at most
\(\pi/2\), a strict unique partner, and
\[
                         \alpha+\beta\le\pi/4.
\tag{19}
\]
If the low-turn endpoint's original S-incident application is adjacent
to its circle corner, its actual distance to that corner is one.
The near-corner lemma gives \(\alpha>1/2\), whence
\[
          \beta<\pi/4-1/2<2/7
\]
using \(\pi<22/7\). Sections 1--3 eliminate strict partner types
A, M and O. The exhaustive strict feature cover leaves precisely T.

This applies to the two-adjacent non-owner row, to the actual adjacent
placement in either same-inner-side non-owner row, and to the actual
adjacent placement in either one-owner row of the full low-turn table.
It also applies to any original endpoint mean that itself has the
stated actual adjacent position, without replacing the mean or
changing its owner label. It does not infer that distance premise for
an arbitrary interior mean or opposite vertex.

Type T, the non-adjacent low-turn placements, both-owner mean rows,
and every outstanding physical completion requirement remain explicit.
The theorem is an entire local feature-family exclusion; no original
coarse checkbox is closed by it alone. No computational certificate,
sampled pose, angle grid, Lean compilation or CI is used.
