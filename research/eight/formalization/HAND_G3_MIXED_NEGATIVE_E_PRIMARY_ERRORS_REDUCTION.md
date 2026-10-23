# Negative E-primary total: two local reductions and the complete fixed A/T regime

## 1. Local geometry and scope

Put
\[
 Q=\frac{9789}{2500},\qquad h=\frac7{10},\qquad
 a_0=\sqrt{Q-\frac14}-\frac12,\qquad
 c_0=\sqrt{Q/2}-\frac12.
\tag{1}
\]
D and H are fixed sorted outer Q states, with tangent signs
negative and positive respectively. E has nonpositive tangent
and lies on its true-core boundary. Write its magnitudes as
\((a,b)\), so that
\[
 a=a_C(b)=
 \begin{cases}
  7/12,&0\le b\le1/2,\\
  \displaystyle\frac12+\sqrt{\frac1{144}-(b-\frac12)^2},
       &\displaystyle\frac12\le b\le\frac12+\frac1{12\sqrt2}.
 \end{cases}
\tag{2}
\]
Its actual frame has signed adjacent errors
\[
 d=\theta_E-\theta_D,\qquad r=\theta_H-\theta_E,
 \qquad |d|,|r|\le h.
\tag{3}
\]
Retain DE3 and EH1, whose exact projections are
\[
 P_3=a_D+a\sin d+b\cos d,
 \qquad P_1=a_H+a\sin r-b\cos r,
\tag{4}
\]
with threshold \(W(t)=(1+\cos t+|\sin t|)/2\).

There are two reductions when the errors have opposite signs
and negative sum:

1. For \(d=-n<0<r=p<n\), moving only E toward H gives a
   necessary descendant with the actual EH0 witness and a
   remaining negative DE3 error. E is flat core at that endpoint.
2. For \(r=-n<0<d=p<n\), if the actual EH0 witness is not
   already feasible, moving only E toward D gives a necessary
   descendant with DE aligned, hence the actual DE2 witness,
   and a remaining negative EH1 error. E stays flat core.

All other states, frames, and chosen inequalities are fixed.
The E frame stays between its original position and the indicated
fixed endpoint. Each positive and negative variation decreases by
the same amount, and the sum d+r stays fixed. The E circle stays
below Q. These are reductions of the consecutive necessary system;
no claim about nonneighbor contacts is needed or used.

Sections 2--5 prove the reductions. Section 6 joins them to the
audited E stresses and removes every E-owner/error choice when the
A/T primary alternatives are nonpositive.

## 2. Two flat-core entry facts

### 2.1 A genuine negative EH1 error

Suppose EH1 is feasible at \(-n<0\) and the actual EH0 witness
is not feasible. Then
\[
              a=\frac7{12},\qquad 0\le b<\frac{39}{250},
                                \qquad n<\frac14.
\tag{5}
\]
This includes b=0. To see it directly, put
\[
 K=a+\frac12,\quad D=b+\frac12,\quad
 X=a_H+\frac12,\quad Z=b_H+\frac12,\quad q=\tan(n/2).
\]
The two projections have exactly the form in Section 3 of
[the negative-A primary entry comparison](HAND_G3_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_FLAT_CORE.md),
with \((a_G,b_G,a_A,y_A)=(a_H,b_H,a,b)\).
Its contact vector and positive-dot-product argument use only
\(b\ge0\), sorting, and \(n<h<\pi/4\). Consequently
\[
 Q>1+K^2+D^2+2(D\cos n+K\sin n)
                              \ge K^2+(D+1)^2.
\tag{6}
\]
If \(D\ge1\), the last expression is at least 5, impossible.
Thus b<1/2 and the true core is flat, with K=13/12.
The same two exact comparisons then give (5):
\[
 \left(\frac{13}{12}\right)^2
          +\left(1+\frac{82}{125}\right)^2-Q
                    =\frac{781}{2250000}>0,
\tag{7}
\]
and
\[
 \begin{split}
 &1+\left(\frac{13}{12}\right)^2+\frac14
       +\left(1-\frac{n^2}{2}\right)
       +\frac{13}{6}\left(n-\frac{n^3}{6}\right)-Q
          \bigg|_{n=1/4}\\
 &\hspace{45mm}=\frac{6137}{480000}>0.
 \end{split}
\tag{8}
\]
The trigonometric expression in (6), with D replaced by 1/2,
increases on \([0,h]\), as proved in the cited comparison.

### 2.2 Core E at an actual EH0 witness is flat

At any signed EH0 error r its feasibility gives
\[
 b\le a_H\cos r+b_H\sin r-W(r)
                  \le\sqrt{a_H^2+b_H^2}-1\le a_0-1<.415<\frac12.
\tag{9}
\]
For the penultimate inequality, the sum a_H+b_H increases along
the sorted outer arc from its minimum a_0. Hence
\(a_H^2+b_H^2=Q-a_H-b_H-1/2\le a_0^2\).
Thus any core E with an actual EH0 witness is flat, regardless
of the DE owner or either error sign.

## 3. Negative DE and positive EH: descent on the actual core

Assume \(d=-n\), \(r=p\), with \(0<p<n\le h\).
Move E toward H by a parameter \(\tau\):
\[
                   n_\tau=n-\tau,\qquad p_\tau=p-\tau.
\tag{10}
\]
Initially keep b fixed. The EH1 margin decreases strictly until
it first reaches contact, since its derivative with respect to
\(p_\tau\) is
\[
                     (a-\tfrac12)\cos p_\tau
                           +(b+\tfrac12)\sin p_\tau>0.
\tag{11}
\]
The negative-DE margin increases at fixed b: its derivative
with respect to \(\tau\) is
\[
             (a+\tfrac12)\cos n_\tau+(b-\tfrac12)\sin n_\tau>0.
\tag{12}
\]
Here \(a>1/2\), b\(\ge0\), and \(\tan n_\tau<1\).
If \(p_\tau=0\) before contact, EH is aligned and both of its
owners coincide; the reduction is complete.

At an EH1 contact, follow its exact implicit curve on (2).
Write
\[
 v=-a_C'(b)\in[0,1],\qquad
 \beta=\frac{db}{dp}
   =\frac{(a-\tfrac12)\cos p+(b+\tfrac12)\sin p}
          {\cos p+v\sin p}>0.
\tag{13}
\]
Thus b decreases as p decreases. The curve is smooth across
b=1/2, where v=0, and remains sorted. The shifted circle
value does not increase: on the flat portion its derivative
with respect to b is \(2(b+1/2)>0\), while on the curved
portion
\[
 \frac{d}{db}\{(a+\tfrac12)^2+(b+\tfrac12)^2\}
        =2\{b+\tfrac12-v(a+\tfrac12)\}=2(1-v)\ge0.
\tag{14}
\]
In the last identity use
\(b-va=(1-v)/2\), which follows directly from (2).

It remains to check the negative-DE inequality along the contact
curve. Its margin is
\[
                 M=a_D-\frac12-(a+\frac12)\sin n
                                      +(b-\frac12)\cos n.
\tag{15}
\]
Set \(x=\tan n\), \(y=\tan p\), so \(0\le y<x<1\).
Using \(db/d\tau=-\beta\), direct differentiation gives
\[
 \frac{1+vy}{\cos n}\frac{dM}{d\tau}
  =1-\frac{1-v}{2}(x+y)+(b-va)(x-y)-vxy.
\tag{16}
\]
On the flat portion, v=0 and b\(\ge0\), so the right side is
at least \(1-(x+y)/2>1-x>0\). On the curved portion it is
\[
                           1-y\{(1-v)+vx\}\ge1-y>0.
\tag{17}
\]
Thus the DE margin improves strictly throughout the contact
motion. The process reaches either \(p=0\) or the tangent floor
b=0; its implicit curve cannot fail before these boundaries
because the denominator in (13) stays positive.

## 4. The zero-tangent boundary supplies an actual EH0 witness

At b=0, the true-core primary is a=7/12. If EH1 is at contact
at a positive error p, then, with \(k_0=1/12\),
\[
 a_H=\frac12+\frac12\cos p-k_0\sin p,
 \qquad X:=a_H+\frac12=1+\frac12\cos p-k_0\sin p.
\tag{18}
\]
Put
\[
                   Y=b_H+\frac12,
                   Z_*=1+k_0\cos p+\frac12\sin p.
\]
The exact identity
\[
 \begin{split}
 X^2+Z_*^2
   &=\frac{325}{144}+\frac76\cos p+\frac56\sin p\\
   &\le\frac{325}{144}+\frac{\sqrt{74}}6
      <\frac{541}{144}<Q,
 \end{split}
\tag{19}
\]
uses \(\sqrt{74}<9\), and the final reserve is
\[
                            Q-\frac{541}{144}=\frac{14279}{90000}>0.
\tag{20}
\]
Since H is outer, \(X^2+Y^2=Q\), so \(Y>Z_*\). Substitution
in the actual EH0 projection gives
\[
       a_H\cos p+b_H\sin p-W(p)=\sin p\,(Y-Z_*)>0.
\tag{21}
\]
Hence EH0 is feasible at this same endpoint. If b was already
zero while EH1 had slack, keep b=0 until its first contact or
until p=0; (12) still preserves DE, and the same argument applies.

Both possible endpoints of Sections 3--4 therefore have an
actual EH0 witness and a still negative DE3 error. Equation (9)
also shows directly that their core E is flat. This proves the
first local reduction in Section 1, including the curved-core
starting case.

## 5. Positive DE and genuine negative EH: a growing flat-core gap

Now assume \(d=p>0\), \(r=-n\), with \(p<n\), and assume the
actual EH0 witness is not initially feasible. Section 2 gives
\(a=7/12\), \(b<39/250\), and \(p<n<1/4\).
Put
\[
 P_D=a_D-\frac12,
 \quad P_H=a_H-\frac12,
 \quad K=\frac{13}{12},
 \quad k_0=\frac1{12}.
\tag{22}
\]
Here \(0<P_D,P_H<.915\). The two exact inequalities (4) are
equivalent to
\[
 L(p):=\frac12-P_D\sec p-k_0\tan p\le b
       \le U(n):=-\frac12+P_H\sec n-K\tan n.
\tag{23}
\]
Move E toward D, reducing p and n by the same \(\tau\in[0,p]\).
Both \(L(p-\tau)\) and \(U(n-\tau)\) increase. More strongly,
their gap increases strictly:
\[
 \begin{split}
 \frac{d}{d\tau}\{U(n-\tau)-L(p-\tau)\}
  ={}&K\sec^2(n-\tau)-P_H\sec(n-\tau)\tan(n-\tau)\\
     &-P_D\sec(p-\tau)\tan(p-\tau)-k_0\sec^2(p-\tau)\\
  >{}&\frac{13}{12}-\frac{183}{100}\frac{25}{93}
                           -\frac1{12}\frac{100}{93}
                       =\frac{140}{279}>\frac12.
 \end{split}
\tag{24}
\]
For the bounds used here, \(0\le t<1/4\) gives
\(\cos t>31/32\), and
\[
 (31/32)^2-.93=\frac{217}{25600}>0.
\]
Thus \(\sec^2t<100/93\) and
\(\sec t\tan t=\sin t/\cos^2t<25/93\).

Choose the new tangent by the continuous formula
\[
                b_\tau=\max\{b_{\rm initial},L(p-\tau)\}.
\tag{25}
\]
It remains below U because the initial gap is nonnegative,
U increases, and the gap in (24) increases. It remains on the
flat core, since
\[
 L(p-\tau)\le L(0)=1-a_D\le1-c_0<.101<\frac{39}{250}.
\tag{26}
\]
The elementary lower bound \(c_0>.899\) follows by squaring,
with reserve \(Q/2-(1.399)^2=599/10^6>0\).
In particular \(b_\tau<.156<1/2\), and its shifted circle
is strictly below Q. At \(\tau=p\), DE is aligned and its
two owners coincide; the retained EH1 error equals \(-(n-p)<0\).
This proves the second local reduction in Section 1.

If EH0 was already feasible before this construction, no motion
is needed: select that actual witness and retain the positive
DE3 error. That alternative is treated separately by the positive
E-primary stress, not by an unsupported negative-E endpoint claim.

## 6. All E owners in the nonpositive A/T-primary regime

Consider a G0--G2 boundary necessary system at Q with outer
H, G, B and D of tangent signs positive, negative, negative,
negative. E is nonpositive and either outer or true core.
Keep BT2 and either HG owner. Allow

* GA2 at any error, or GA3 at a nonpositive error;
* AB0 at any error, or AB2 at a nonpositive error;
* TD0 at any error, or TD2 at a nonpositive error;
* either DE2 or DE3, and either EH0 or EH1, at arbitrary errors.

Assume the captured global total-variation condition
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+\le h.
\tag{27}
\]
Then
**this entire necessary-system class is impossible.**

If E is outer, Section 4 of
[the outer-E witness comparison](HAND_G3_OUTER_E_NEGATIVE_PRIMARY_WITNESS_COMPARISON.md)
already proves the conclusion: every nonpositive primary supplies
an actual secondary witness, and the remaining positive primaries
are covered by Section 6 of
[the signed E-primary stress](HAND_G3_COMBINING_THE_TWO_E_PRIMARY_ERRORS.md).
That same signed stress excludes core E whenever there is one
nonnegative E primary, or two E primaries with nonnegative total.
Its proof uses just the necessary inequalities and captured
variation, so it also applies after any owner selection below.

It remains to consider core E with at least one negative primary.
If both E edges are already secondary, the previously proved
negative-A/T fixed stress applies without any E-kind assumption.
For a single negative EH1, either EH0 is already feasible, or
(5) gives a flat core. For a single negative DE3 with EH0,
(9) gives a flat core. These flat cases are excluded by
[the negative flat-core E stress](HAND_G3_NEGATIVE_FLAT_CORE_E_FIXED_STRESS_EXCLUSION.md).

For two primary E edges with negative total, if both errors are
nonpositive, either select an already feasible EH0 and use (9),
or use (5). In both cases the same flat-core stress excludes
the necessary system. If the signs are opposite, Sections 3--4
reduce negative DE/positive EH to a single negative DE with EH0.
Section 5 reduces positive DE/genuine negative EH to a single
negative EH with aligned DE2. If the latter EH0 was already
feasible, it instead leaves just one positive DE primary, covered
by the signed E stress.

Each constructed E path retains the other five inequalities,
the four required outer circles, both signs and radial kinds of
A/T, and every A/T error. It preserves the signed total and
reduces positive and negative variation together. Its final
stress therefore uses the same captured domain and no new G1
or packing premise. This completes the finite case split.

Positive A-primary alternatives and positive TD2 remain outside
this theorem's stated A/T regime. The E conclusion itself has no
remaining owner, error-sign, or frame-order restriction.
