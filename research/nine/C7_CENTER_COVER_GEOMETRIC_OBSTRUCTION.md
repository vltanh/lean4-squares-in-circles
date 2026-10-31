# A physical boundary C7 need not have center covering radius below three-halves

**Status: complete exact existence construction; independent hand audit passed.** At

\[
 R=\frac{\sqrt{1105}}{16},\qquad Q=R^2=\frac{1105}{256},\qquad \sigma=1/\sqrt2,
\]

there is a physical seven-cycle of circle-touching, independently oriented unit squares whose centers have minimum enclosing-circle radius strictly greater than \(3/2\).

The construction is exact: its parameter is a root of an explicitly defined continuous function, whose endpoint signs are proved below by elementary inequalities. No numerical scan or numerical residual is a premise.

The resulting ring **does not admit a positive physical C7 stress**; Section 8 proves this exactly. Thus it does not refute the positive-stress C7 completion target. It does refute the stronger, unstressed covering-radius theorem. The strict center-cover piercing criterion remains valid, but a successful C7 cover argument must use positive stress or some further restriction.

## 1. One-parameter circle-touching square poses

For \(0\le t\le\tau:=\pi/6\), define

\[
 h(t)=\frac{\cos t+\sin t}{2},\qquad
 k(t)=\frac{\cos t-\sin t}{2},
\]

\[
 r(t)=\sqrt{Q-\frac12+h(t)^2}-h(t).
 \tag{1}
\]

A unit square with center \(r(t)e_\alpha\) and frame angle \(\alpha+t\) lies in \(D_R\) and touches its circle, since

\[
 r(t)^2+2r(t)h(t)+\frac12=Q.
 \tag{2}
\]

Put \(r_0=r(0)\), \(d_0=r_0-1/2\), and

\[
 L(t)=\sqrt{(r(t)-k(t))^2+h(t)^2},
 \qquad \eta(t)=\arctan\frac{h(t)}{r(t)-k(t)},
 \qquad K(t)=\frac12-r(t)\sin t.
 \tag{3}
\]

The circle-touching radius bounds give

\[
 \frac32<r_0<\frac{91}{60}=:M,
 \qquad d_0>1.
 \tag{4}
\]

The upper bound follows from \(M^2+M+1/2>Q\), as already computed in `BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md`.

Differentiating (2),

\[
 r'=-\frac{rk}{r+h}<0.
 \tag{5}
\]

Moreover

\[
                         r(t)>\frac{11}{8}
                         \quad(0\le t\le\tau).
 \tag{6}
\]

It is enough to check the last endpoint. At \(r=11/8\) and \(t=\tau\), the left side of (2) is

\[
 \frac{197+44\sqrt3}{64}
 <\frac{137}{32}
 =\frac{1096}{256}<Q,
\]

using \(\sqrt3<7/4\). This proves (6).

## 2. Exact adjacent contact angles

For \(p,q\in\{0,t\}\), define

\[
 g(p,q)
 =p+\eta(q)+\arcsin\frac{K(p)}{L(q)},
 \tag{7}
\]

using the principal arcsine. The formula is continuous throughout the parameter interval. Indeed \(|K(p)|<1\), while \(L(q)\ge L(0)>1\); the latter monotonicity is proved just below.

Place the first square at center \((r(p),0)\), frame angle p, and the next at center \(r(q)e_{g(p,q)}\), frame angle \(g(p,q)+q\). The next square's lower-left vertex, expressed in its radial frame, is

\[
                         (r(q)-k(q),-h(q)).
\]

In the first square's side frame, equation (7) places this vertex at

\[
                (X(p,q),K(p)),
 \qquad X(p,q)=\sqrt{L(q)^2-K(p)^2}>0.
 \tag{8}
\]

Thus it lies on the first square's upper supporting line. We verify that it lies on the actual side and that this line separates the two physical squares.

First,

\[
 \frac{d}{dt}L(t)^2
 =\frac{2r\,[r(h-k)+1/2]}{r+h}>0.
 \tag{9}
\]

The first square's side interval is

\[
       r(p)\cos p-\frac12\le X\le r(p)\cos p+\frac12.
\]

After adding \(K(p)^2\) and squaring its positive endpoints, these two requirements become

\[
 r(p)^2+\frac12-2r(p)h(p)
 \le L(q)^2
 \le r(p)^2+\frac12+2r(p)k(p).
 \tag{10}
\]

They hold in every case needed:

* For p=q, they follow from h>=k>=0.
* For p=0,q=t, the lower bound is (9). The upper bound is \(L(t)^2<Q\), since \(Q-L(t)^2=2r(t)\cos t>0\).
* For p=t,q=0, the lower bound equals \(2r(t)^2+1-Q\), which decreases with t and equals \(L(0)^2\) at zero. The upper bound exceeds \(r(t)^2+1/2>2\), whereas \(L(0)^2<(M-1/2)^2+1/4<2\).

All side inclusions are strict for t>0, except for the common limiting case t=0.

The relative frame angle

\[
                         \Delta=g(p,q)+q-p
\]

lies in \((0,\pi/2)\). One direct verification uses the increasing sine branch in (7):

* For p=0,q=t, the defining contact expression is negative at g=0 and positive at \(g=\pi/2-t\), the latter value being \(r(t)\cos t-1>0\) by (6).
* For p=t,q=0, that expression is negative at g=t, because \(r(t)\sin t<1\), and positive at \(g=t+\pi/2\).
* For p=q=t, it is negative at g=0 and positive at \(g=\pi/2\); those values are \(-1\) and \(r(t)(\cos t+\sin t)-1\), respectively.

Consequently the vertex in (8) is the next square's minimum-support vertex in the first square's upper-side normal. Equations (8)--(10) are therefore actual physical contacts, with disjoint interiors. For t>0, each is a side-interior/vertex contact with the unique normal equal to the first square's upper-side normal.

## 3. Closing the seven-cycle

Use relative tilts

\[
                         (0,t,0,t,0,t,t).
 \tag{11}
\]

The successive center gaps prescribed by (7) close after one turn exactly when

\[
 F(t):=3g(0,t)+3g(t,0)+g(t,t)=2\pi.
 \tag{12}
\]

We prove that F has a root in \((0,\tau)\).

### 3.1. The first endpoint is above one full turn

At t=0,

\[
 g(0,0)=2\arctan\frac1{2r_0-1}.
\]

Since \(r_0<M=91/60\),

\[
 \frac1{2r_0-1}>\frac{30}{61}>\frac{49}{100}.
\]

Let \(\zeta=\arctan(49/100)\). We have \(\pi/12<\zeta<\pi/6\). Furthermore, writing \(z=49/100\),

\[
 \sin(7\zeta)
 =\frac{z(7-35z^2+21z^4-z^6)}{(1+z^2)^{7/2}}<0,
\]

because \(z^2>6/25\), \(z^4<3/50\), and hence the bracket is less than \(-7/50\). Since \(7\zeta\in(7\pi/12,7\pi/6)\), this forces \(7\zeta>\pi\). Therefore \(g(0,0)>2\pi/7\), and

\[
                              F(0)>2\pi.
 \tag{13}
\]

### 3.2. The second endpoint is below one full turn

Set

\[
                         A=\arctan\frac43,
 \qquad B=\arctan\frac98.
\]

At \(t=\tau=\pi/6\), we claim

\[
             g(0,\tau)<A,\qquad
             g(\tau,\tau)<A,\qquad
             g(\tau,0)<B.
 \tag{14}
\]

For the defining contact expression

\[
 f_{p,q}(x)=(r(q)-k(q))\sin(x-p)-h(q)\cos(x-p)-K(p),
\]

the positive sign at a proposed upper bound implies that bound exceeds g(p,q), because both angles are on the same increasing sine branch. Here \(\eta(q)<\pi/4\), while the trial angles A,B lie in \((\pi/4,\pi/3)\), so that branch condition holds directly.

For p=0,q=\(\tau\), substitution of \(\sin A=4/5\), \(\cos A=3/5\) reduces \(f_{0,\tau}(A)>0\) to

\[
                 r(\tau)>\frac{9+7\sqrt3}{16}.
\]

This follows from \(r(\tau)>11/8>4/3\) and \(\sqrt3<7/4\), since \((9+7\sqrt3)/16<85/64<4/3\).

For p=q=\(\tau\), the same substitution reduces positivity to

\[
                       r(\tau)(1+2\sqrt3)>6.
\]

It follows from \(r(\tau)>11/8\) and \(\sqrt3>17/10\).

Finally, after multiplication by \(2\sqrt{145}\), \(f_{\tau,0}(B)>0\) becomes

\[
 d_0(9\sqrt3-8)-4\sqrt3-\frac92
              +(r(\tau)-1)\sqrt{145}>0.
\]

Using d_0>1, \(r(\tau)>11/8\), and \(\sqrt{145}>12\), its left side exceeds \(5\sqrt3-8>0\). This proves (14).

Consequently \(F(\tau)<4A+3B<2\pi\). For the final strict comparison, A,B both lie between \(\pi/4\) and \(\pi/3\), and

\[
 (3+4i)^4(8+9i)^3=1090328-45321i.
\]

Thus the sine of \(4A+3B\in(7\pi/4,7\pi/3)\) is negative, which forces \(4A+3B<2\pi\). Hence

\[
                              F(\tau)<2\pi.
 \tag{15}
\]

By continuity and (13)--(15), choose any exact root

\[
                         t_*\in(0,\pi/6),\qquad F(t_*)=2\pi.
 \tag{16}
\]

Use (11), the radii (1), and successive contact gaps (7) to define the seven square poses.

## 4. Nonneighbor squares are disjoint

Every consecutive pair is a physical circle-touching contact pair by Section 2. The pairwise angular estimates from `CIRCLE_CONTACT_ANGULAR_ORDER.md` therefore apply to each pair separately: its positive center gap lies between \(\pi/5\) and \(2\pi/5\).

At the root (16), the seven gaps sum to \(2\pi\). Any nonneighbor pair has minor center-angle separation greater than \(2\pi/5\), since both circular paths between them use at least two gaps. Every center radius exceeds \(5/4\). Therefore their center distance is greater than

\[
                         \frac52\sin\frac\pi5>\sqrt2.
\]

The last comparison follows from \(\sin^2(\pi/5)=(5-\sqrt5)/8\), or by squaring \(61>25\sqrt5\). The two circumscribed disks of radius \(1/\sqrt2\) are disjoint. Thus the nonneighbor unit squares are disjoint and do not touch.

The complete physical touching graph is exactly C7, and all seven bodies touch \(\partial D_R\).

## 5. The three radial centers surround the origin

Put

\[
                            J(t)=g(0,t)+g(t,0).
\]

The three radial bodies, at positions 0,2,4 in (11), have center angles

\[
                              0,\quad J(t_*),\quad2J(t_*).
 \tag{17}
\]

We need \(\pi/2<J(t_*)<\pi\). The upper bound follows from the relative-frame bounds in Section 2:

\[
 g(0,t)<\pi/2-t,\qquad g(t,0)<t+\pi/2.
\]

Here is a uniform lower bound for both terms on \([0,\pi/6]\).

First, the contact expression at g=\(\pi/4\) for g(0,t) is

\[
 \sigma(r(t)-\cos t)-\frac12<0,
\]

because \(r(t)\le M\), \(\cos t\ge\sqrt3/2>17/20\), and hence \(r(t)-\cos t<2/3<\sigma\). Thus \(g(0,t)>\pi/4\).

For g(t,0), first note the useful bound

\[
                         r(t)\le r_0-\frac14\sin t.
 \tag{18}
\]

Indeed, subtracting the two circle equations gives

\[
 r_0-r(t)
 =\frac{r(t)(\cos t+\sin t-1)}{r_0+r(t)+1}.
\]

For \(t\le\pi/6\),

\[
 \frac{\cos t+\sin t-1}{\sin t}
 =1-\tan(t/2)\ge\sqrt3-1>\frac57,
\]

while (4), (6) give

\[
 \frac{r_0+r(t)+1}{4r(t)}
 <\frac14+\frac{M+1}{4(11/8)}
 =\frac{467}{660}<\frac57.
\]

This proves (18), with its limiting interpretation at t=0.

Set \(s=\sin t\), \(c=\cos t\). The contact expression at g=\(\pi/4\) for g(t,0) is

\[
 \sigma(r_0-1)c+(r(t)-\sigma r_0)s-\frac12.
\]

By (18), it is at most

\[
 A_0c+B_0s-\frac{s^2}{4}-\frac12,
 \qquad A_0=\sigma(M-1)<\frac38,
 \qquad B_0=M(1-\sigma)<\frac9{20}.
\]

The two simple bounds use \(\sigma<18/25\) and \(\sigma>12/17\), respectively. Since \(c\le1-s^2/2\), the expression is at most

\[
 A_0+B_0s-\left(\frac14+\frac{A_0}{2}\right)s^2-\frac12
 \le A_0+\frac{B_0^2}{1+2A_0}-\frac12
 <\frac38+\frac{(9/20)^2}{1+3/4}-\frac12
 =-\frac{13}{1400}<0.
\]

The penultimate bound is valid because the displayed function increases with A_0 and B_0 throughout these ranges. Hence \(g(t,0)>\pi/4\) as well.

We have proved

\[
                              \frac\pi2<J(t_*)<\pi.
 \tag{19}
\]

The three cyclic gaps in (17) are \(J,J,2\pi-2J\), all strictly less than \(\pi\). Their triangle is acute and contains the origin in its interior. Its cyclic graph-gap partition is \((2,2,3)\).

## 6. The center covering radius exceeds three-halves

All three centers in (17) have exactly the same radius

\[
                       r_0=\frac{\sqrt{1041}}{16}-\frac12>\frac32.
\]

Their circumcenter is the origin, and their acute triangle has minimum enclosing-circle radius r_0. Equivalently, take positive barycentric weights with \(\sum\lambda_j C_j=0\), \(\sum\lambda_j=1\). For any proposed disk center z,

\[
 \sum\lambda_j|C_j-z|^2=r_0^2+|z|^2\ge r_0^2.
\]

No disk of radius less than r_0 can contain the three centers. Therefore the minimum enclosing-circle radius of all seven centers is greater than \(3/2\).

## 7. What this counterexample does and does not say

It disproves a purely geometric center-cover theorem for arbitrary boundary C7 rings at Q. It is compatible with the separately proved center-diameter bound below three: a planar set can have diameter below three while requiring covering radius above three-halves.

No two-square completion is asserted. The center-cover piercing criterion is sufficient, not necessary, for capacity one. Most importantly, the next section shows that this family is not positively stressed, so the positive-stress covering route remains open.

## 8. The constructed rings have no positive physical C7 stress

For t=t_*>0, every contact is side-interior/vertex, with its unique normal the outgoing side normal of the preceding body. Consider the tilted bodies at positions 1 and 5 in (11). Both have relative tilt t and a radial predecessor. Their incoming relative frame increment is the same

\[
                            \Delta=g(0,t)+t\in(0,\pi/2).
\]

In either tilted body's own frame, its unique circle corner is

\[
                 z=(a,-b),
 \qquad a=r(t)\cos t+\frac12,
 \qquad b=r(t)\sin t+\frac12.
\]

Its incoming contact point is \((a-1,-b)\), its incoming force normal is \((\sin\Delta,\cos\Delta)\), and its outgoing normal is \(e_y\). If the incoming and outgoing positive force magnitudes are \(\mu_-\), \(\mu_+\), and its circle multiplier is \(\lambda\ge0\), translation balance gives

\[
 \mu_-\sin\Delta=2\lambda a,
 \qquad
 \frac{\mu_+}{\mu_-}=\cos\Delta+\frac ba\sin\Delta=:D>0.
\]

In particular its circle load is positive. Torque about the origin, with outgoing contact first coordinate X, gives

\[
 \mu_+X
 =\mu_-\bigl[(a-1)\cos\Delta+b\sin\Delta\bigr].
\]

Eliminating the magnitudes forces

\[
                         X=a-\frac{\cos\Delta}{D}.
 \tag{20}
\]

This value depends only on the tilted body and its radial predecessor. It must therefore be identical at positions 1 and 5.

But the successor at position 1 is radial, whereas the successor at position 5 is tilted. Their actual outgoing contact coordinates from (8) are

\[
                  X(t,0)=\sqrt{L(0)^2-K(t)^2},
 \qquad          X(t,t)=\sqrt{L(t)^2-K(t)^2}.
\]

By (9), \(L(t)>L(0)\), so \(X(t,t)>X(t,0)\). This contradicts (20). Hence no positive physical C7 stress exists on these rings. \(\square\)

## 9. The obstruction persists at strictly smaller containing radii

The failure of the unstressed center-cover statement is not confined to
\(R^2=Q\). There is \(\varepsilon>0\) such that every

\[
                         Q-\varepsilon<q\le Q
\]

admits the same kind of counterexample in \(D_{\sqrt q}\), still with no
positive physical C7 stress.

To prove this without selecting a numerical root, restore the squared
radius as a parameter and write

\[
 r_q(t)=\sqrt{q-\frac12+h(t)^2}-h(t),
\]

with \(L_q,\eta_q,K_q,g_q,F_q\) defined by the same formulas as before.
At \(q=Q\), the strict endpoint inequalities (13) and (15) allow fixed
numbers

\[
                  0<t_-<t_+<\pi/6,
 \qquad F_Q(t_-)>2\pi>F_Q(t_+).
\]

All formulas are continuous in \((q,t)\) near the compact interval
\(\{Q\}\times[t_-,t_+]\). The arcsine arguments stay strictly between
minus one and one there. The strict side-interior inclusions, relative
frame bounds, physical contact conditions and bounds
\(\pi/2<J_Q(t)<\pi\) established above have positive uniform margins
on this compact interval. The same holds for \(r_Q(0)>3/2\). Therefore,
after decreasing \(\varepsilon\) if needed, all those strict properties
and the two opposite signs of \(F_q(t_\pm)-2\pi\) persist for
\(Q-\varepsilon<q\le Q\). We also choose
\(Q-\varepsilon>17/4\), so every such radius remains in the declared
research window.

For each such q, the intermediate value theorem supplies
\(t_q\in(t_-,t_+)\) with \(F_q(t_q)=2\pi\). The seven consecutive
contacts then close. The angular-order bounds and the nonneighbor
separation argument of Section 4 apply unchanged, yielding an actual
physical C7. Its three radial centers still surround the origin and
have common radius \(r_q(0)>3/2\), so their minimum enclosing-circle
radius exceeds three-halves. Finally, the torque contradiction in
Section 8 persists: the contact types are unchanged, and the exact
identity (9), valid also with q in place of Q, gives
\(L_q(t_q)>L_q(0)\).

Thus even the strictly subcritical version of the unstressed
center-cover implication is false. Positive stress or another genuine
restriction remains necessary for a covering-radius proof. \(\square\)
