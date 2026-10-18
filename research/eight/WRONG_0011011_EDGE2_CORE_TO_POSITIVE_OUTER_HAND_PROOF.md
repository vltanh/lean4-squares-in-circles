# 0011011: the whole negative core-to-positive outer edge-2 transition

## Theorem and data

Let \(Q=9789/2500=3.9156\) and \(\gamma=17953/20000=.89765\).
For the negative core source and positive outer target on edge 2,
every retained separating axis and every angle
\[
 \pi/2-.7\le\phi\le\pi/2+.7
\]
has corrected cost strictly greater than \(\gamma\).
The source may lie on either part of the core boundary. Reflected
reversal gives the corresponding edge-6 family.

Use
\[
 a_c=7/12,\quad d_c=1/2+\sqrt2/24,\quad
 d=\sqrt{Q/2}-1/2,\quad a_0=\sqrt{Q-1/4}-1/2.
\]
The source own-frame center is \((a,+b)\), where
\[
 a=a_c,\quad 0\le b\le1/2,
\]
or
\[
 a=1/2+\sqrt{1/144-(b-1/2)^2},\quad 1/2\le b\le d_c.
\]
The target own-frame center is \((A,-B)\), where
\[
 A=A(B)=\sqrt{Q-(B+1/2)^2}-1/2,\quad0\le B\le d.
\]
The source and target labels are respectively
\[
 .00125+hb,\qquad V(B)=-.01025A+.16031B+.63457AB,
 \quad h=1.03981.
\]
Thus
\[
 C=\phi-.00125-hb-V(B).
 \tag{1}
\]
Set \(s=\sin\phi,\ c=\cos\phi,\ W=(1+s+|c|)/2\).
The four possible separating margins are
\[
\begin{array}{c|l}
1&-b+As-Bc-W\\
2&-ac-bs+A-W\\
3&as-bc-B-W\\
4&a-Ac-Bs-W.
\end{array}
\tag{2}
\]
This note proves all four cases on the whole angle interval. Unlike
the preceding companion family, it needs no imported aligned strip.

## 1. One rational upper tangent for the outer label

Write
\[
 r=\frac{B+1/2}{A+1/2},\qquad A'=-r,\qquad
 r'=\frac Q{(A+1/2)^3}.
\]
Then
\[
 V'=.01025r+.16031+.63457(A-Br),
\]
\[
 V''=-1.26914r+(.01025-.63457B)r'.
 \tag{3}
\]
On the whole outer arc, \(r>.261\), \(r'<1.5\). Consequently
\[
 V''<-1.26914(.261)+.01025(1.5)<0.
\]
At the diagonal \(V'(d)=.17056>0\). Hence \(V\) is increasing and
strictly concave, and \(V(B)\le V(d)<.6481\).

At \(B_*=.5725\), exact radical comparisons give
\[
 V'(B_*)<p=.670579666,\qquad
 V(B_*)-B_*V'(B_*)<k_0=.118433769.
\]
The true tangent majorizes the concave function. Since \(B\ge0\),
rounding both tangent coefficients upward proves the uniform bound
\[
 V(B)\le k_0+pB.
 \tag{4}
\]
All numbers in (4) are rational.

The core center norm is at most \(\sqrt2d_c<.8\). The outer center
norm is at most \(a_0<1.415\). To see the latter,
\(A^2+B^2=Q-.5-A-B\), while \(A+B\) increases from \(a_0\).

For every axis and every \(\phi\ge2.13\), (1) already gives
\[
 C\ge2.13-.00125-hd_c-.6481>.8994>\gamma.
 \tag{5}
\]
We may use (5) whenever convenient.

## 2. Two impossible axes and a side reduction

Axis 3 is impossible for all angles: its projection
\(as-bc\) is at most the core norm, while \(W\ge1\) and \(B\ge0\).

Axis 4 is impossible below the quarter angle, since \(c\ge0\)
and its projection is at most \(a\le a_c<1\).

For axis 1, its necessary inequality implies
\[
 b\le As-Bc-W\le\sqrt{A^2+B^2}-1
       \le a_0-1<.415.
 \tag{6}
\]
Thus the source is automatically on the core side.
Increasing \(b\) to contact lowers the cost and remains within that
side. At contact, the cost is
\[
 F(B,\phi)=
 \phi-.00125+hW-hA\sin\phi+hB\cos\phi-V(B).
 \tag{7}
\]

## 3. Axis 1 below the quarter angle

### 3.1. The whole early interval \(\phi\le1.2\)

The necessary inequality \(A\sin\phi-B\cos\phi\ge W\) has left-hand
margin strictly decreasing in \(B\) and strictly increasing in
\(\phi\) on the lower half. The two fixed comparisons
\[
 a_0\sin1-\frac{1+\sin1+\cos1}{2}<0,
\]
\[
 A(.254)\sin1.2-.254\cos1.2
             -\frac{1+\sin1.2+\cos1.2}{2}<0
\]
therefore imply
\[
 \phi>1,\qquad B<.254
 \tag{8}
\]
for any feasible early state.

The contact derivative of (7) is
\[
 F_B=h(r\sin\phi+\cos\phi)-V'(B).
\]
Because \(r\) increases in \(B\), while \(V'\) decreases, and because
\(r(.254)\sin\phi+\cos\phi\) decreases for \(\phi\ge1\),
\[
 F_B\le h\{r(.254)\sin1+\cos1\}-V'(.254)<0.
 \tag{9}
\]
At each feasible angle, increase \(B\) until the contact source
coordinate in (6) reaches zero. This is the largest feasible \(B\):
the margin decreases strictly in \(B\), and it is negative by
\(B=.254\). Equation (9) proves that this move decreases the cost.

The zero-source boundary obeys
\[
 (A-.5)\sin\phi-(B+.5)\cos\phi=.5.
 \tag{10}
\]
Put
\[
 S=(A-.5)\cos\phi+(B+.5)\sin\phi>0.
\]
Using (10) and the outer circle gives
\[
 S^2=Q-2A-.25\ge Q-2a_0-.25=(a_0-.5)^2.
\]
Thus \(S>.914\), while \(A+.5>1.829\) and \(\cos\phi<.541\)
on the early boundary. Implicit differentiation of (10) gives
\[
 \phi'(B)=\frac{r\sin\phi+\cos\phi}{S}
 =\frac{1+\cos\phi/S}{A+.5}
 <\frac{1+.541/.914}{1.829}<.871.
 \tag{11}
\]
But \(V'(B)\ge V'(.254)>.941\). The boundary cost
\(\phi(B)-.00125-V(B)\) therefore strictly decreases with \(B\).
The boundary angle increases with \(B\); its least cost in the
early interval is consequently attained at \(\phi=1.2\).
Its coordinate there is still below .254, so
\[
 C>1.2-.00125-V(.254)>.957>\gamma.
 \tag{12}
\]
This proves the entire early axis-1 interval, including zero
coordinates and any original source that was described using the
closed side/corner join.

### 3.2. The interval \(1.2\le\phi\le\pi/2\)

Insert the tangent (4) into (7). The full-circle support inequality
\[
 \alpha A+\beta B\ge-\frac{\alpha+\beta}{2}
                     -\sqrt Q\sqrt{\alpha^2+\beta^2}
 \tag{13}
\]
gives
\[
 F_-(\phi)=\phi-.00125-k_0+\frac{h+p}{2}
             +h\sin\phi-\sqrt Q\,N_-(\phi),
\]
\[
 N_-^2=h^2+p^2-2hp\cos\phi.
 \tag{14}
\]
For \(N^2=A+B\cos\phi+C\sin\phi\), direct differentiation gives
\[
 N''+\frac N4=\frac{A^2-B^2-C^2}{4N^3}.
 \tag{15}
\]
Here the numerator is \((h^2-p^2)^2>0\).
The function \(N_-\) increases on this interval, and the fixed
comparison
\[
 h\sin1.2-\frac{\sqrt Q}{4}N_-(\pi/2)>0
\]
therefore implies \(F_-''<0\) throughout it.
The endpoint comparisons are
\[
 F_-(1.2)>.9007,\qquad F_-(\pi/2)>.89778.
 \tag{16}
\]
Concavity proves \(C>\gamma\) on the whole remaining lower range.

## 4. Axis 1 above the quarter angle

Set \(x=\phi-\pi/2\in[0,.7]\). The same contact and support
calculation gives
\[
 F_+(x)=\pi/2+x-.00125-k_0+\frac{h+p}{2}
       +h(\sin x+\cos x)-\sqrt Q\,N_+(x),
\]
\[
 N_+^2=h^2+p^2+2hp\sin x.
 \tag{17}
\]
Identity (15) still applies. Since
\(N_+\le h+p\), \(\sin x+\cos x\ge1\), and
\[
 h-\frac{\sqrt Q}{4}(h+p)>0,
\]
we have \(F_+''<0\) everywhere. At \(x=0\) the value agrees with
the second endpoint in (16); at the other endpoint,
\[
 F_+(.7)>1.387.
\]
Thus the whole upper axis-1 range is proved.

## 5. Axis 2 below the quarter angle

A corner source is impossible. Indeed, if \(b\ge.5\) and \(a\ge d_c\),
its separating inequality requires
\[
 A\ge W+a\cos\phi+b\sin\phi
   \ge .5+(d_c+.5)\cos\phi+\sin\phi.
 \tag{18}
\]
The final expression is concave on the lower interval; it equals
1.5 at the quarter endpoint and is greater than 1.5 at the other
endpoint. This contradicts \(A\le a_0<1.415\).

Hence \(a=a_c\). Eliminating the source coordinate gives
\[
 b\le\frac{A-.5}{\sin\phi}-\frac12-\frac{13}{12}\cot\phi.
\]
Insert this upper bound and (4) into the cost, and use (13). We obtain
\[
 G_-(\phi)=\phi-.00125-k_0+\frac{h+p}{2}
 +\frac{h(1+\frac{13}{12}\cos\phi)
       -\sqrt Q\sqrt{h^2+p^2\sin^2\phi}}{\sin\phi}.
 \tag{19}
\]
Section 7 proves \(G_->\gamma\) on the entire lower interval.

## 6. Axis 2 above the quarter angle

With \(x=\phi-\pi/2\), put \(u=\sin x,v=\cos x\).
The source bound \(a\le a_c\) makes the following a necessary
inequality for both side and corner:
\[
 b\le\frac{A+a_cu-W}{v}.
\]
As in Section 5, (4) and full-circle support give
\[
 G_+(x)=\pi/2+x-.00125-k_0+\frac{h+p}{2}
 +\frac{h(1-\frac1{12}\sin x)
       -\sqrt Q\sqrt{h^2+p^2\cos^2x}}{\cos x}.
 \tag{20}
\]
The second polynomial below proves \(G_+>\gamma\) on \(0\le x\le.7\).
The relaxed coordinate need not itself lie on the core boundary:
only its necessary upper bound is used.

## 7. Two fixed squared polynomials

Let \(\pi_-=3.141592653589793238<\pi\), and put
\[
 K=\pi_-/2-.00125-k_0+(h+p)/2-\gamma.
\]
Let \(C_{10},C_8,S_{11},S_9\) denote the usual alternating Taylor
polynomials of the indicated degree for cosine and sine.
On \(0\le x\le.7\),
\[
 0<C_{10}\le\cos x\le C_8,\qquad
 0\le S_{11}\le\sin x\le S_9\le.7.
\]
Also \(K-.7>.69\). Define
\[
 A_-=C_{10}(K-x)+h+\frac{13h}{12}S_{11},
 \qquad
 A_+=C_{10}(K+x)+h-\frac h{12}S_9,
\]
\[
 P_\pm=A_\pm^2-Q\{h^2+p^2C_8^2\}.
 \tag{21}
\]
Both numerators are positive: \(A_->h\) and
\(A_+\ge h(1-.7/12)>0\). The Taylor directions in (21) consequently
show that \(P_->0\) implies (19) \(>\gamma\), with
\(x=\pi/2-\phi\), and that \(P_+>0\) implies (20) \(>\gamma\).

The sums of absolute values of negative terms of degree above eight,
evaluated at .7, are strictly below .000274 and .00001 respectively.
Therefore
\[
 \widehat P_-=[P_-]_{\le8}-.000274,\qquad
 \widehat P_+=[P_+]_{\le8}-.00001
 \tag{22}
\]
are lower bounds for (21). On the single whole interval \([0,.7]\),
their nine Bernstein coefficients have these strict rational
lower bounds:

| Polynomial | Coefficients, in order |
|---|---|
| \(\widehat P_-\) | .000397, .05458, .07950, .08343, .07559, .06439, .05602, .05418, .06095 |
| \(\widehat P_+\) | .000661, .39201, .76842, 1.10743, 1.38425, 1.57465, 1.65928, 1.62777, 1.47923 |

The convention is
\[
 P(.7t)=\sum_{j=0}^8p_j\binom8j t^j(1-t)^{8-j}.
\]
Every displayed lower bound is positive. Thus both complete
primary-axis inequalities follow on their closed whole intervals.
These are two explicit algebraic positivity identities, not a
subdivision or sampling assertion.

## 8. Axis 4 above the quarter angle

The direct bound (5) covers \(\phi\ge2.13\).
For the remaining angles, \(x=\phi-\pi/2<.56\).
Using \(a\le a_c\), \(A\le a_0\), and \(B\ge0\), the separating
margin is bounded above by
\[
 a_c-.5+(a_0-.5)\sin x-\frac12\cos x.
\]
This increases with \(x\), and its value at .4 is negative.
Hence feasibility requires \(x>.4\).

The same axis further implies
\[
 B\le(a_0-.5)\tan x+\frac1{12}\sec x-\frac12
 \le(a_0-.5)\tan .56+\frac1{12}\sec .56-\frac12<.18.
\]
Because \(V\) increases and \(V(.18)<.174\),
\[
 C>\pi/2+.4-.00125-hd_c-.174>1.214>\gamma.
\]
This completes the last possible axis for all core source states.

## 9. Completeness and exact arithmetic

Axis 3 is impossible everywhere. Axis 4 is impossible on the lower
half and excluded in Section 8 on the upper half. Sections 3--4 cover
all of axis 1; Sections 5--7 cover all of axis 2. No angle strip,
source endpoint, corner, or side case remains.

The companion checker performs 63 fixed exact comparisons. It
reconstructs the Taylor and squared polynomials, checks the two
negative-tail allowances and all 18 printed coefficient bounds,
and verifies the scalar radical and trigonometric comparisons.
Integer rational arithmetic, certified square-root brackets, and
alternating series suffice. No optimization output enters this proof.
