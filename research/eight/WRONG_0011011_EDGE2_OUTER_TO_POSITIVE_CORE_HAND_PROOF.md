# 0011011: the whole negative outer-to-positive core edge-2 transition

## Theorem and dependencies

For a negative outer source and a positive core target on edge 2,
every retained separating axis and every angle
\[
 \pi/2-.7\le\phi\le\pi/2+.7
\]
has corrected cost \(C>\gamma=.89765\).
This covers the target core side and corner and, by reflected reversal,
the corresponding edge-6 family.

Two previously proved results are used explicitly:

1. The aligned mixed-quarter theorem gives \(C>.89777\) at
   \(\phi=\pi/2\).
2. The edge-2 mixed-quarter strip theorem covers the entire closed strip
   \(|\phi-\pi/2|\le.02\).

Outside that strip the present proof gives complete continuous
inequalities. Its new arithmetic consists of 55 fixed rational
comparisons, including two degree-eight rows with nine positive
coefficients each. No sampled bound enters the proof.

Use
\[
 Q=3.9156,\quad a_c=7/12,\quad
 d=\sqrt{Q/2}-1/2,\quad d_c=1/2+\sqrt2/24,\quad
 a_0=\sqrt{Q-1/4}-1/2.
\]
The source has
\[
 a=a(b)=\sqrt{Q-(b+1/2)^2}-1/2,\quad 0\le b\le d.
\]
The target is on \(A=a_c,\ 0\le B\le1/2\), or on the core corner.
The actual own-frame centers are \((a,+b)\), \((A,-B)\).
The labels and cost are
\[
 L(b)=.02478+.93015b+.02363b^2-.11055ab,\qquad
 C_3^+(B)=-.01449+gB,\quad g=1.04240,
\]
\[
 C=\phi+.01449-L(b)-gB .
\tag{1}
\]
Writing \(s=\sin\phi,c=\cos\phi,W=(1+s+|c|)/2\), the four margins are
\[
\begin{array}{c|l}
1&-b+As-Bc-W\\
2&-ac-bs+A-W\\
3&as-bc-B-W\\
4&a-Ac-Bs-W.
\end{array}
\tag{2}
\]

## 1. Label chords and elementary radial bounds

The source label increases and is convex:
\[
 L'>.773,\qquad
 L''=.04726+.11055(2r+br')>0,\qquad
 r=(b+1/2)/(a+1/2).
\]
Its endpoint chords give the following three exact upper bounds:
\[
\begin{array}{c|c}
\text{source range}&\text{upper chord}\\ \hline
0\le b\le.5&L(b)\le.02478+.8085b\\
0\le b\le.7&L(b)\le.02478+.8281b\\
0\le b\le d&L(b)\le.02478+.853b .
\end{array}
\tag{3}
\]
The two restricted chord slopes are verified at their right endpoints.
For the full arc the exact slope is \(.93015-.08692d<.853\).

The core center norm is at most
\(1/\sqrt2+1/12=\sqrt2\,d_c<.8\).
The outer center norm is at most \(a_0<1.415\): from the circle,
\(a^2+b^2=Q-.5-a-b\), and \(a+b\) increases with \(b\).
We also have \(.899<d<.9\).

These facts already exclude axis 1 for every angle, since
\(As-Bc\) is at most the core norm and \(W\ge1\).
Axis 2 is impossible on the lower half, where \(c\ge0\).

## 2. Axis 2 on the upper half

Write \(x=\phi-\pi/2\in[0,.7]\), \(u=\sin x,v=\cos x\).
Axis 2 gives
\[
 b\le\frac{a_0u+a_c-W}{v}
     =(a_0-.5)\tan x+\frac1{12}\sec x-\frac12.
\]
Using the full chord in (3) and \(B\le d_c\), its cost is at least
\[
 F_2(x)=\pi/2+x-.01029-gd_c+.4265
          -.853(a_0-.5)\tan x-\frac{.853}{12}\sec x.
\tag{4}
\]
This scalar is concave on \([0,.7]\), since \(\tan x\) and \(\sec x\)
have nonnegative second derivatives there, and the latter's is
strictly positive. Its endpoints satisfy
\[
 F_2(0)>1.33,\qquad F_2(.7)>1.35.
\]
Thus every axis-2 state is excluded. The possibly negative relaxed
upper bound for \(b\) simply makes the original axis infeasible; it
does not invalidate the lower expression (4).

## 3. Axis 3 on the lower half

Every axis-3 target is on the core side, for its constraint gives
\[
 B\le as-bc-W\le\sqrt{a^2+b^2}-1
       \le a_0-1<.415<1/2.
\tag{5}
\]
This observation holds on both angle halves.
Because the cost decreases with \(B\), increase \(B\) to equality in
(5)'s original separating inequality.

### 3.1. Source coordinate \(b\le.5\)

Use \(q=.8085\) from (3). Subtract \(g\) times the separating margin
from the corresponding lower cost. The full outer-circle support
\[
 \alpha a+\beta b\ge-(\alpha+\beta)/2
                         -\sqrt Q\sqrt{\alpha^2+\beta^2}
\]
gives the scalar bound
\[
 F_-(\phi;q)=\phi-.01029+\frac{g+q}{2}
             +g\sin\phi-\sqrt Q\,N(\phi),
\]
\[
 N^2=g^2+q^2-2gq\cos\phi .
\tag{6}
\]
For \(\ell=\pi/2-.7\le\phi\le\pi/2\), \(N\) increases and
\[
 N''+N/4=\frac{(g^2-q^2)^2}{4N^3}>0.
\tag{7}
\]
The fixed comparison
\[
 g\sin\ell-\frac{\sqrt Q}{4}N(\pi/2)>0
\]
therefore makes (6) strictly concave on this entire interval.
Its endpoints are
\[
 F_-(\ell;.8085)>.982,\qquad
 F_-(\pi/2;.8085)>.9179 .
\tag{8}
\]
This excludes every state in the stated source range.

### 3.2. Source coordinate \(b\ge.5\)

At contact,
\[
 B=(a-.5)\sin\phi-(b+.5)\cos\phi-.5 .
\tag{9}
\]
Since \(B\ge0\), (9) implies \(a\ge1\).
The derivative at fixed source is
\[
 B_\phi=(a-.5)\cos\phi+(b+.5)\sin\phi .
\]
This is a concave trigonometric function of \(\phi\) with positive
coefficients. At the right endpoint it is \(b+.5\ge1\); at the left it
is at least \(.5\cos\ell+\sin\ell>1\).
Hence \(B_\phi\ge1\) everywhere. The cost derivative is
\[
 C_\phi=1-gB_\phi\le1-g<0.
\tag{10}
\]
Increasing \(\phi\) to the quarter angle decreases the cost.
The contact coordinate increases and, by (5), remains below .415, so
no target boundary is encountered. The aligned theorem gives a
strict bound .89777 at the endpoint. This completes the lower axis 3.

## 4. Axis 3 on the upper half

The closed strip \(0\le x\le.02\) is already proved.
For \(.02\le x\le.7\), use the full chord \(q=.853\) in (3).
The same support calculation now gives
\[
 F_+(x)=\pi/2+x-.01029+\frac{g+q}{2}
       +g(\sin x+\cos x)-\sqrt Q\,N_+(x),
\]
\[
 N_+^2=g^2+q^2+2gq\sin x .
\tag{11}
\]
Identity (7), with the angle shifted, still applies.
Moreover \(N_+\le g+q\) and \(\sin x+\cos x\ge1\).
The scalar is therefore strictly concave, since
\[
 F_+''<-g+\frac{\sqrt Q}{4}(g+q)<0.
\]
Both endpoints satisfy
\[
 F_+(.02)>.8999,\qquad F_+(.7)>1.272.
\tag{12}
\]
This proves the entire remaining upper axis-3 range, including any
zero-coordinate contact or change of contact branch. No continuation
argument on that upper zero-coordinate boundary is needed.

## 5. Axis 4 on the lower half

First, a core-corner target is impossible. If \(B\ge.5\), \(A\ge d_c\),
the required source coordinate would satisfy
\[
 a\ge W+A\cos\phi+B\sin\phi
 \ge.5+(d_c+.5)\cos\phi+\sin\phi .
\]
The final expression is concave on the lower interval and is at least
1.5 at both endpoints, contradicting \(a\le a_0<1.415\).

Thus \(A=a_c\), and the contact coordinate is
\[
 B=\frac{a-.5}{\sin\phi}-\frac12-\frac{13}{12}\cot\phi .
\tag{13}
\]
As in axis 3, increasing \(B\) to this contact lowers the cost.
For \(B<.5\),
\[
 W+a_c\cos\phi+B\sin\phi-(1+B)
 =\frac{13}{12}\cos\phi-(B+.5)(1-\sin\phi)\ge0.
\]
Consequently \(B\le a-1\le a_0-1<.415\), so this contact remains on
the core side.

### 5.1. Source coordinate \(b\ge.7\)

Here \(a\le a(.7)<1.074\).
The derivative of (13) satisfies
\[
 B_\phi-\frac1g=
 \frac{13/12-1/g+(1/g)\cos^2\phi-(a-.5)\cos\phi}
      {\sin^2\phi}.
\]
Completing a square in \(\cos\phi\) bounds its numerator below by
\[
 \frac{13}{12}-\frac1g-\frac{g(.574)^2}{4}>0.
\tag{14}
\]
Thus \(B_\phi>1/g\), and the contact cost strictly decreases as the
angle increases toward \(\pi/2\).
The contact coordinate stays nonnegative and below .415.
The aligned theorem again gives the endpoint bound .89777.

### 5.2. Source coordinate \(b\le.7\)

Use \(q=.8281\) in the second chord of (3).
Multiplying the separating inequality by \(g/\sin\phi\) cancels the
target coordinate in the cost. Full-circle support then gives
\[
 G_-(\phi;q)=
 \phi-.01029+\frac{g+q}{2}
 +\frac{g(1+\frac{13}{12}\cos\phi)
        -\sqrt Q\sqrt{g^2+q^2\sin^2\phi}}{\sin\phi}.
\tag{15}
\]
Section 7 proves \(G_->.89765\) on the whole lower interval with a
single degree-eight polynomial. This completes every lower axis-4
case.

## 6. Axis 4 on the upper half

Again the closed \(.02\) strip is already proved.
For \(.02\le x\le.7\), the uniform core bound \(A\le a_c\) gives the
necessary inequality
\[
 B\le\frac{a+a_c\sin x-W}{\cos x}.
\tag{16}
\]
This is valid on both the side and corner; it does not assert that
the relaxed coordinate belongs to the core boundary.

Use the full chord \(q=.853\) and (16), followed by circle support.
The cost is bounded below by
\[
 G_+(x;q)=
 \pi/2+x-.01029+\frac{g+q}{2}
 +\frac{g(1-\frac1{12}\sin x)
        -\sqrt Q\sqrt{g^2+q^2\cos^2x}}{\cos x}.
\tag{17}
\]
The second polynomial in Section 7 proves \(G_+>.89765\) throughout
this interval.

## 7. Two explicit squared polynomial inequalities

All the constants in this section are rational. Let
\[
 \pi_-=3.141592653589793238<\pi,\qquad
 K_q=\pi_-/2-.01029+(g+q)/2-\gamma .
\]
Use the alternating Taylor polynomials
\[
 C_{10}=\sum_{j=0}^5\frac{(-1)^jx^{2j}}{(2j)!},\quad
 C_8=\sum_{j=0}^4\frac{(-1)^jx^{2j}}{(2j)!},
\]
\[
 S_{11}=\sum_{j=0}^5\frac{(-1)^jx^{2j+1}}{(2j+1)!},\quad
 S_9=\sum_{j=0}^4\frac{(-1)^jx^{2j+1}}{(2j+1)!}.
\tag{18}
\]
On \(0\le x\le.7\),
\[
 0<C_{10}\le\cos x\le C_8,\qquad
 0\le S_{11}\le\sin x\le S_9\le.7 .
\]
The coefficients \(K_q-x\) and \(K_q+x\) are positive.

For the lower case put \(q=.8281,\ x=\pi/2-\phi\), and define
\[
 A_-(x)=C_{10}(K_q-x)+g+\frac{13g}{12}S_{11}.
\]
For the upper case put \(q=.853\), and define
\[
 A_+(x)=C_{10}(K_q+x)+g-\frac g{12}S_9.
\]
Both are positive: \(A_->g\), and
\(A_+\ge g(1-.7/12)>0\).
For the corresponding sign and value of \(q\), set
\[
 P_\pm=A_\pm^2-Q\{g^2+q^2C_8^2\}.
\tag{19}
\]
The exact Taylor directions ensure that \(P_\pm>0\) implies,
respectively, \((15)>\gamma\) or \((17)>\gamma\).
There is no sign ambiguity in taking square roots because \(A_\pm>0\).

Write \([P]_{\le8}\) for the terms of degree at most 8.
The total absolute value of the negative higher-degree terms,
evaluated at \(x=.7\), is strictly below the stated allowance:
\[
 \text{lower allowance } .00031,\qquad
 \text{upper allowance } .000011 .
\]
Thus the following degree-eight polynomials are lower bounds for
the full polynomials in (19):
\[
 \widehat P_-=[P_-]_{\le8}-.00031,\qquad
 \widehat P_+=[P_+]_{\le8}-.000011.
\tag{20}
\]

Their nine Bernstein coefficients have the following strict rational
lower bounds, in order:

| Polynomial and whole interval | All coefficient lower bounds |
|---|---|
| \(\widehat P_-\), \([0,.7]\) | .03216, .09189, .12506, .14048, .14758, .15443, .16617, .18482, .21039 |
| \(\widehat P_+\), \([.02,.7]\) | .03108, .44049, .83611, 1.19488, 1.49153, 1.70162, 1.80557, 1.79252, 1.66077 |

The convention is
\[
 P(l+(r-l)t)=\sum_{j=0}^8p_j\binom8j t^j(1-t)^{8-j}.
\]
All displayed lower bounds are positive. Equations (18)--(20)
therefore prove the required scalar bounds on their entire intervals,
including both endpoints.

## 8. Completeness and arithmetic

Axis 1 is universally impossible. Axis 2 is impossible below the
quarter angle and excluded by (4) above it. Sections 3--4 cover both
halves for axis 3, and sections 5--7 cover both halves for axis 4.
The only imported neighborhoods are the explicitly stated closed
\(.02\) strip and aligned endpoint theorem, both already proved for
the full mixed edge-2 domain.

The exact checker reconstructs all Taylor and squared polynomials,
checks the two tail allowances and all 18 displayed coefficients,
and verifies the stated scalar radical and trigonometric comparisons.
Its 55 comparisons use integer rational arithmetic, certified square
root brackets, and alternating series. No search result or finite
sampling assertion is part of this whole-family theorem.
