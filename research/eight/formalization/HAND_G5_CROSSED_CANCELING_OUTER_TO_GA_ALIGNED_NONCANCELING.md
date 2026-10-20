# A crossed canceling outer owner reduces to a GA-aligned noncanceling owner

## 1. Scope and the unchanged anchors

Put
\[
 Q=\frac{9789}{2500},\qquad p=\frac{50}{49},\qquad
 S_0=2\sqrt{Q-1}-3.
\tag{1}
\]
Retain a normal-sign hard necessary cycle with circles at most
\(q\le Q\), true core avoidance, sorted nonnegative own-frame
magnitudes, and real frame spread at most \(7/10\). The normal
signs are positive at H,A,T and negative at G,B,D. Either E
sign is allowed. Retain
\[
 GA=0,\quad BT=2,\quad HG=2,\quad TD\in\{0,2\},
 \quad DE\in\{2,3\},\quad EH\in\{0,1\}.
\tag{2}
\]
Assume that AB has already been aligned exactly:
\[
 \theta_A=\theta_B=\rho,\qquad b_A+b_B=1,
 \qquad \theta_T\le\rho\le\theta_G.
\tag{3}
\]
The branch considered here is
\[
                     \theta_H<\rho,\qquad b_A\ge\frac12.
\tag{4}
\]

**Reduction.** Every feasible system satisfying (1)--(4) has a
descendant at the same q with
\[
                 \theta_G'=\rho>\theta_T,
\]
and with an actual HG0 witness. All H,A,B,T,D,E coordinates
and frames are unchanged. In particular, the original five
anchors H,A,B,D,E and all inherited separate A/B circle losses
are retained. Only G is replaced. This joins the GA-aligned
crossed noncanceling branch; this note does not claim that the
subsequent common-frame clamp has already been proved.

The reflected statement applies to a crossed TD0 side with
the large middle tangent at B. The signed-E statement below
makes that reflection legitimate for every mixed-owner pair.

## 2. The endpoint estimate also holds with either E sign

The endpoint theorem in
[the all-mixed-owner intermediate-order note](HAND_G5_GLOBAL_INTERMEDIATE_ORDER_WITH_ALL_MIXED_OWNERS.md)
proves, when E has negative signed tangent,
\[
 b_H+b_D-p(\theta_H-\theta_D)+S_0<2.
\tag{5}
\]
Its proof uses only H,D,E and the two actual mixed witnesses.
The same statement holds with positive E tangent by the
following exact reflection of that three-state subsystem.

Write the signed tangent of E as \(y_E\), and set
\(\delta=\theta_E-\theta_D\),
\(\epsilon=\theta_H-\theta_E\). The four possible
projections, before subtracting their widths, are
\[
\begin{array}{c|l}
 DE2&a_D\cos\delta+b_D\sin\delta-y_E\\
 DE3&a_D+a_E\sin\delta-y_E\cos\delta\\
 EH0&y_E+a_H\cos\epsilon+b_H\sin\epsilon\\
 EH1&a_H+a_E\sin\epsilon+y_E\cos\epsilon.
\end{array}
\tag{6}
\]
Exchange H and D, negate every frame, and replace \(y_E\)
by \(-y_E\). Then
\[
 \delta'=\epsilon,\quad \epsilon'=\delta,\quad
 DE2\longleftrightarrow EH0,\quad
 DE3\longleftrightarrow EH1.
\tag{7}
\]
Every projection and width in (6) is preserved. The two
endpoint magnitudes are exchanged, all circle and true-core
conditions are preserved, and both \(b_H+b_D\) and
\(\theta_H-\theta_D\) are unchanged. Applying the already
proved negative-E estimate to this reflected triple proves
(5) for either E sign.

The same extension gives \(\theta_G>\theta_T\) for the
full hard cycle with either E sign: the middle-path and
zero-charge join in Section 6 of the cited note does not
use E at all. Only its endpoint estimate needed extension.

## 3. Lower G to the common frame using the full HG2 composite

Translate the common frame to zero. Write
\[
 \theta_G=t\ge0,\quad \theta_H=-r<0,\quad
 \theta_T=-u\le0,\quad h=t+r,
\]
and put
\[
 P=a_A-\frac12,\quad Y=b_A+\frac12,\quad
 V(t)=P\cos t-Y\sin t,\quad U(t)=P\sin t+Y\cos t.
\tag{8}
\]
The GA0 inequality is
\[
                         V(t)\ge b_G+\frac12.
\tag{9}
\]
In particular \(a_A\ge1\). Since \(b_A\ge1/2\),
\[
 q\ge\frac{13}{4},\qquad
 P\le\sqrt{Q-1}-1<\frac{177}{250},\qquad Y\ge1.
\tag{10}
\]
The strict square reserve for the upper bound is
\((427/250)^2-(Q-1)=26/15625>0\).

For the actual H, define
\[
 S(h)=(a_H-\tfrac12)\sin h+(b_H-\tfrac12)\cos h,
\quad
 U_H(h)=(a_H-\tfrac12)\cos h-(b_H-\tfrac12)\sin h.
\tag{11}
\]
Adding HG2 and GA0 eliminates \(b_G\) and gives exactly
\[
                            V(t)+S(t+r)\ge1.
\tag{12}
\]
We prove that decreasing t preserves this entire composite,
with a uniform strict gain.

On any feasible portion of (12),
\(S\ge1-V\ge1-P>73/250\). Put
\(m=\cos h+\sin h\), \(n=\cos h-\sin h>0\).
The actual H circle gives
\[
 (S+m)^2+(U_H+n)^2\le Q,
\]
and sorting gives \(U_H+n>0\). Therefore
\[
 U_H<\sqrt{Q-(m+73/250)^2}-\sqrt{2-m^2}.
\tag{13}
\]
The expression on the right increases with m for
\(1\le m\le\cos(7/10)+\sin(7/10)\): after positive
squaring its derivative sign is exactly
\[
 \frac Q2>\left(1+\frac{73}{250m}\right)^2,
\]
which follows already at \(m=1\), with reserve
\(36067/125000\). At \(h=7/10\), alternating Taylor
bounds give
\[
 m>\frac{176}{125},\qquad n>\frac{119}{1000},\qquad
 \sqrt{Q-(17/10)^2}<\frac{1013}{1000}.
\]
The last squared reserve is \(569/10^6\). Thus (13)
implies the simple whole-interval bound
\[
                         U_H<\frac{447}{500}.
\tag{14}
\]

Along the decreasing-t segment, (9) gives \(V\ge1/2\).
Since \(U'=V\), it follows that \(U\ge U(0)=Y\ge1\).
Consequently, wherever (12) holds,
\[
 \frac{d}{dt}\{V(t)+S(t+r)\}
                   =-U(t)+U_H(t+r)<-\frac{53}{500}.
\tag{15}
\]
A first-boundary argument now proves (12) on the whole
segment down to \(t=0\): at any boundary where its left
side equals one, decreasing t moves strictly into the
feasible side. The condition \(V\ge1/2\) also persists,
since V increases as t decreases.

At every point of this path choose
\[
 b_G'=\max\{0,\tfrac12-S(t+r)\},\qquad a_G'=\frac7{12}.
\tag{16}
\]
Then HG2 holds, and (9) follows from (12) and \(V\ge1/2\).
Moreover
\[
 0\le b_G'\le V-\frac12\le P-\frac12<\frac{26}{125}.
\]
The replacement is sorted and satisfies the true core. Its
corner circle is bounded by
\[
 (13/12)^2+(177/250)^2<\frac{13}{4}\le q.
\tag{17}
\]
The entire path remains in the original frame interval and
changes no other state. It ends with G at the common frame.
If \(u=0\), this descendant would have \(G=T\), contrary
to the signed-E extension of the global intermediate-order
theorem in Section 2. Hence every surviving descendant has
\(u>0\).

## 4. At GA alignment the H tangent is larger than the G tangent

Write \(g=b_G\) at the endpoint of Section 3. Thus
\[
 0\le g\le a_A-1<\frac{26}{125},\qquad
 g+a_H\sin r+b_H\cos r\ge\frac{1+\cos r+\sin r}{2}.
\tag{18}
\]
We claim
\[
                              b_H>g.
\tag{19}
\]
Suppose instead that \(b_H\le g\). For fixed r in
\([0,7/10]\), the maximum H projection at tangent b is
\[
 \left(\sqrt{Q-(b+1/2)^2}-\frac12\right)\sin r+b\cos r.
\]
It increases in b on the sorted arc: its derivative is
\(\cos r-\{(b+1/2)/\sqrt{Q-(b+1/2)^2}\}\sin r
\ge\cos r-\sin r>0\).
This permits the following three elementary captures.

First, \(b_H>37/250\). Otherwise evaluate the H projection
at \(b=37/250=.148\), and use
\[
 a_Q(37/250)-\frac12<\frac{87}{100},\qquad
 (187/100)^2+(81/125)^2-Q=\frac{301}{250000}>0.
\]
The width-subtracted upper bound increases with r, and at
\(r=7/10\) it is less than
\[
 -\frac{73}{250}+\frac{87}{100}\frac{6443}{10000}
                     -\frac{44}{125}\frac{478}{625}
                =-\frac{3343}{5000000}<0.
\tag{20}
\]
Here \(a_Q(b)=\sqrt{Q-(b+1/2)^2}-1/2\),
\(\sin(.7)<.6443\), and \(\cos(.7)>.7648\).
This contradicts (18).

Second, \(r>33/50\). Since \(b_H\le g<26/125\),
use
\[
 a_Q(26/125)-\frac12<\frac{106}{125},\qquad
 (231/125)^2+(177/250)^2-Q=\frac{12}{15625}>0.
\]
For \(r\le33/50\), the corresponding increasing upper
bound is at most
\[
 -\frac{73}{250}+\frac{106}{125}\frac{1533}{2500}
                     -\frac{73}{250}\frac{7899}{10000}
                 =-\frac{6643}{2500000}<0,
\tag{21}
\]
using \(\sin(.66)<.6132\), \(\cos(.66)>.7899\).

Third, \(g>37/200\). Otherwise \(b_H\le37/200\), and
\[
 a_Q(37/200)-\frac12<\frac{857}{1000},\qquad
 (1857/1000)^2+(137/200)^2-Q=\frac{1037}{500000}>0.
\]
At \(r=7/10\), the width-subtracted upper bound is less than
\[
 -\frac{63}{200}+\frac{857}{1000}\frac{6443}{10000}
                      -\frac{63}{200}\frac{478}{625}
                 =-\frac{37469}{10000000}<0.
\tag{22}
\]
All four trigonometric enclosures in (20)--(22) follow from
the alternating sine polynomial of degree five and cosine
polynomial of degree six at the two displayed rational
arguments. No angle subdivision is used.

## 5. The opposite hard contact contradicts those three captures

From \(g>37/200\) and GA alignment,
\(a_A>237/200\). The two square reserves
\[
 (519/500)^2+(337/200)^2-Q=\frac{1069}{10^6}>0,
\]
\[
 (173/100)^2+(481/500)^2-Q=\frac{343}{125000}>0
\]
therefore give, in order,
\[
 b_A<\frac{269}{500},\qquad b_B>\frac{231}{500},
 \qquad a_B-\frac12<\frac{73}{100}.
\tag{23}
\]
The exact opposite BT2 contact then implies
\[
 b_T+\frac12
       <\frac{73}{100}\cos u-\frac{481}{500}\sin u.
\tag{24}
\]
The right side decreases with u. At \(u=1/4\), its
degree-four upper cosine and degree-three lower sine put it
below \(1/2\), with reserve \(1257/40960\). Thus
\(0\le u<1/4\).

Define
\[
 f(u)=\frac{73}{100}\cos u-\frac{481}{500}\sin u
                                  -\frac12+pu.
\]
On the entire interval \([0,1/4]\),
\[
 f''(u)\le-\frac{73}{100}\left(1-\frac{(1/4)^2}{2}\right)
                     +\frac{481}{500}\frac14
             =-\frac{7467}{16000}<-\frac9{20}.
\]
Since \(f(0)=23/100\) and
\(f'(0)=p-481/500=1431/24500\), completing the square gives
\[
 b_T+pu<f(u)
 \le\frac{23}{100}+\frac{10}{9}\left(\frac{1431}{24500}\right)^2
 <\frac{47}{200}.
\tag{25}
\]
The final reserve is \(18149/15006250>0\).

The all-sign TD zero charge, dropping its nonnegative extra
term, gives
\[
 b_T+b_D\ge1-p(\theta_D-\theta_T).
\tag{26}
\]
Combining this with the actual mixed endpoint estimate (5)
yields
\[
                     b_H-b_T+p(r-u)<1-S_0.
\tag{27}
\]
But (20)--(22) and (25) imply
\[
 b_H-b_T+p(r-u)
 >\frac{37}{250}+\frac{50}{49}\frac{33}{50}-\frac{47}{200}
 =\frac{293}{500}+\frac{23}{49000}.
\tag{28}
\]
On the other hand \(S_0>207/500\), since
\((Q-1)-(1707/1000)^2=1751/10^6>0\). Therefore
\(1-S_0<293/500\), contradicting (27). This proves (19).

## 6. Lift only G and select its actual HG0 witness

Keep the endpoint tangent g and frame \(\rho\), and replace
only its primary by
\[
                         a_G'=\sqrt{q-(g+1/2)^2}-\frac12.
\tag{29}
\]
Because \(b_H>g\) and the actual H circle is at most q,
\(a_G'>a_H\). Also \(b_A\ge1/2>g\), so the actual
A circle gives \(a_G'>a_A\ge1\). Hence this G is sorted,
satisfies the true core, and has circle exactly q.
Neither aligned GA0 nor HG2 depends on its primary, so both
remain feasible.

At the positive crossed HG error r, the two exact projections
satisfy
\[
 P_{HG0}-P_{HG2}
  =(a_G'-a_H)\sin r+(b_H-g)(1-\cos r)>0.
\tag{30}
\]
Thus HG0 is an actual feasible witness, with strict slack.
This is the claimed GA-aligned noncanceling descendant.
All six other states are exactly the ones from the start of
this note; in particular neither middle circle was lifted,
and any separate inherited A/B loss is unchanged.

The proof uses an exact two-contact derivative, a fixed
endpoint reflection, three rational captures, and one
whole-interval concavity estimate. The rational comparisons
are reproducible by ordinary arithmetic. No sampled angle
mesh, numerical acceptance premise, Lean run or CI result is
used.
