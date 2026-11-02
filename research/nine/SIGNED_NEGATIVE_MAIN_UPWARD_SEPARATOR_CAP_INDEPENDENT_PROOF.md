# A signed main-orientation cap with an upward physical separator

November 2, 2026. Independent hand derivation for the proposed signed cap.
All constants and scalar ranges are explicit. This is a conditional physical
pair theorem, not a full-mask exclusion. No Lean, Lake, or CI.

Put

\[
 Q=1105/256,\quad r=\sqrt Q,\quad
 a=46,\quad b=27/2,\quad k=207/16,\quad T=211/4.
\]

Let M and B be two physical unit squares with disjoint open interiors,
both contained in the closed Q-disk. Fix coordinates with e=(1,0).
Assume the original M-frame has the signed form

\[
 u_M=(\alpha,-\beta),\quad v_M=(\beta,\alpha),\qquad
 \alpha\ge\beta\ge0,\quad\alpha^2+\beta^2=1.
\]

Assume there is an **actual owned physical separating normal**

\[
 n=(c,s),\quad s\ge0,\quad c^2+s^2=1,
 \qquad n\cdot(c_B-c_M)\ge h_M(n)+h_B(n),
\]

where n is parallel to a side axis of M or B. The existence of this
upward normal is a premise; the ordering of the two center heights alone
does not establish it.

Define

\[
 \tau_-(M)=(a-k)\beta-a(1-\alpha).
\]

**Theorem.** Under these exact hypotheses,

\[
 a[-e\cdot c_M-h_M(e)]
 +b[-e\cdot c_B-h_B(e)]+\tau_-(M)\le T. \tag{1}
\]

The inequality is strict if the containing disk has radius less than r.
The penalty is nonnegative: writing z=beta/(1+alpha), one has
z<=sqrt(2)-1<1/2, so
tau_-=beta[(a-k)-az]>=(a/2-k)beta>=0.

## 1. Physical support reduction and all orientation candidates

For any square S, let h_S(w) be its centered support function. Apply
disk support to the two vectors -ae-kn and -be+kn and use the displayed
physical separator. The load without tau in (1) is at most

\[
 H(c)-P_M-P_B,
\]

where

\[
 \begin{split}
 L_a(c)&=\sqrt{a^2+k^2+2akc},\\
 L_b(c)&=\sqrt{b^2+k^2-2bkc},\\
 H(c)&=r[L_a(c)+L_b(c)],\\
 P_M&=a h_M(e)+h_M(ae+kn)+k h_M(n),\\
 P_B&=b h_B(e)+h_B(be-kn)+k h_B(n).
 \end{split} \tag{2}
\]

The physical inequalities are strict at subcritical radius because
L_a+L_b>0. It remains to prove P_M-tau_-+P_B>=H-T.

For reference, the bounding-rectangle reduction for an arbitrary square
in the accepted physical two-square cap gives the three candidates

\[
 \begin{split}
 E_w(t)&=w+k[\sqrt{1-t^2}+\max(t,0)],\\
 N_w(t)&=\begin{cases}
 k+w(t+\sqrt{1-t^2}),&t\ge0,\\
 k+w\sqrt{1-t^2},&-k/w\le t\le0,\\
 w(\sqrt{1-t^2}-t),&t\le-k/w,
 \end{cases}\\
 D_w(t)&=\begin{cases}
 L+wk\sqrt{1-t^2}/L,&t\ge-k/w,\\
 w(w+kt+k\sqrt{1-t^2})/L,&t\le-k/w,
 \end{cases}
 \quad L=\sqrt{w^2+k^2+2wkt}.
 \end{split} \tag{3}
\]

Thus P_B>=min(E_b(-c),N_b(-c),D_b(-c)); if B owns n,
then P_B=N_b(-c). These formulas retain both original physical owners.

For the signed M-frame put alpha=cos(phi), beta=sin(phi),
0<=phi<=pi/4. Between the projection sign changes, P_M is linear in
cos(phi),sin(phi). The support triangle inequality gives

\[
 P_M\ge2a h_M(e)=a(\alpha+\beta).
\]

Consequently the second derivative of P_M-tau_- on each such interval is

\[
 -P_M+a\alpha+(a-k)\beta\le-k\beta\le0. \tag{4}
\]

Its minimum occurs at an endpoint. The vector ae+kn has angle between
0 and arcsin(k/a)<pi/4; it cannot be parallel to an interior axis of
the negative folded M-frame, whose axis angles are -phi and pi/2-phi.
The complete candidate list is therefore:

1. phi=0: the aligned M-frame, with tau_-=0, covered by the original cap;
2. phi=pi/4: the negative diagonal frame, treated in Section 4;
3. n parallel to an M-axis, treated in Sections 2 and 3.

No diagonal ae+kn candidate lies in the interior of the signed frame
range. If M owns n, only the third candidate is needed. If B owns n,
the first two and the third candidate at its sign-change points suffice.

The elementary identities used below are

\[
 H(0)=T+a+b+2k,\qquad H'(0)=k/2,\qquad H''(c)<0,
\]

and hence

\[
 H(c)\le H(0)+(k/2)c. \tag{5}
\]

## 2. M owns n: the complete nonnegative-c arc

For beta>0, an upward normal owned by the negative folded M-frame has
either 0<=c<=1/sqrt(2), or -1<=c<=-1/sqrt(2). The aligned case beta=0
is already covered by the inherited cap; this explicitly includes its
additional upward normal n=(1,0), which lies outside those two arcs.
On the first arc,
alpha=s and beta=c, and there is an exact cancellation

\[
 N_a(c)-\tau_-=a+k+kc. \tag{6}
\]

Because c<=1/sqrt(2)<k/b=23/24, the three B candidates reduce to

\[
 b+ks,\qquad k+bs,\qquad L_b+bk s/L_b.
\]

Using (5), the first two reserves are at least

\[
 k[c/2-(1-s)],\qquad (k/2)c-b(1-s). \tag{7}
\]

They are nonnegative, and positive when c>0. Indeed,
(1-s)/c<=sqrt(2)-1<1/2 and also sqrt(2)-1<23/48=k/(2b).
At c=0 both displayed expressions vanish.

For the third B candidate it is enough to show

\[
 L_b+bk s/L_b-(b+k)+(k/2)c>0. \tag{8}
\]

If 0<=c<=1/16, then 18<L_b<19 and s>99/100. In fact,
L_b(1/16)^2-18^2=243/64>0 and
19^2-L_b(0)^2=2911/256>0. Therefore

\[
 L_b+bk s/L_b-(b+k)
 >18+\frac{99bk}{1900}-(b+k)=\frac{40311}{60800}>0.
\]

For 1/16<=c<=1/sqrt(2), use AM-GM to bound the left side of (8) below by

\[
 f(c)=2\sqrt{bk}(1-c^2)^{1/4}+(k/2)c-(b+k).
\]

This is concave. Extend the interval to [1/16,5/7], since
1/sqrt(2)<5/7. Both endpoints are positive by the following rational table.
Each radical lower bound is verified by squaring positive quantities.

| c | lower bound on s | lower bound on sqrt(bk s) | resulting lower bound on f(c) |
|---|---:|---:|---:|
| 1/16 | 99/100 | 657/50 | 3159/12800 |
| 5/7 | 69/100 | 439/40 | 149/1120 |

The squared-root reserves are 20007/80000 and 199/3200 respectively.
Concavity completes (8) and the entire nonnegative-c arc.

## 3. M owns n: the complete negative-c arc

Write t=-c in [1/sqrt(2),1], with s=sqrt(1-t^2). Now alpha=t,
beta=s, and

\[
 N_a(-t)-\tau_-=a+ks. \tag{9}
\]

The tangent at c=-1 gives a convenient common bound. One has

\[
 H(-1)=r(a+b),\qquad
 H'(-1)=rk\left(\frac a{a-k}-\frac b{b+k}\right)
 <\frac{142443}{6016}<24.
\]

The first strict inequality uses r<133/64. Concavity therefore gives

\[
 H(-t)\le r(a+b)+24(1-t). \tag{10}
\]

Also 1-t<=s/2, because t>=1/sqrt(2)>3/5. Define

\[
 C=T+a+b+k-r(a+b)>\frac{197}{128}>0. \tag{11}
\]

For E_b(t)=b+k(s+t), equations (9)-(10) give reserve at least

\[
 C+2ks-(k+24)(1-t)
 \ge C+\frac{3k-24}{2}s>0.
\]

For N_b(t)=k+b(s+t), the reserve is at least

\[
 C+(b+k)s-(b+24)(1-t)
 \ge C+(b/2+k-12)s>0.
\]

For D_b(t)=L_b+bk s/L_b, note that L_b>24 throughout this arc:
using t>7/10 gives L_b^2-24^2>23229/1280>0. Its derivative with
respect to t is bk/L_b<8, so

\[
 L_b\ge b+k-8(1-t),\qquad bk/L_b\ge bk/(b+k)=621/94>6.
\]

The reserve is consequently at least

\[
 C+(k+6)s-32(1-t)\ge C+(k-10)s>0.
\]

This covers all three B-frame candidates on the entire negative arc,
including the endpoint s=0.

## 4. B owns n: the complete negative-diagonal M candidate

For alpha=beta=1/sqrt(2), put m=max(|c|,s). Direct support evaluation gives

\[
 P_M-\tau_-=a+\frac{k}{\sqrt2}(1+c+m). \tag{12}
\]

The remaining reserve is

\[
 F_{45}(c)=T-H(c)+a+\frac{k}{\sqrt2}(1+c+m)+N_b(-c).
\]

### 4.1. The interval -1<=c<=1/sqrt(2)

For c<=0, the tangent (5) gives the lower bound

\[
 k\left[\frac{1+c+m}{\sqrt2}-1-\frac c2\right]
 +b(s-c-1). \tag{13}
\]

For c>=0 the last term is instead b(s-1). On each of the three
intervals separated by -1/sqrt(2) and 0, these expressions are concave:
after choosing m=-c or m=s, their only nonlinear term is a positive
multiple of sqrt(1-c^2). Their four endpoint values are

| c | lower-bound endpoint value |
|---|---|
| -1 | k(1/sqrt(2)-1/2)>0 |
| -1/sqrt(2) | k(3/(2sqrt(2))-1)+b(sqrt(2)-1)>0 |
| 0 | k(sqrt(2)-1)>0 |
| 1/sqrt(2) | (b+k/2)/sqrt(2)-b>153/320>0 |

The last comparison uses 1/sqrt(2)>7/10. This proves F_45>0 on this
whole interval.

### 4.2. The interval 1/sqrt(2)<=c<=23/24

Weighted Cauchy gives the uniform upper bound

\[
 (L_a+L_b)^2\le(a+b)^2(1+k^2/(ab))
 <(a+b)^2\frac{263}{207}<\left(\frac{336}{5}\right)^2.
\]

Here k^2<168, ab=621, and the final squared reserve is
369313/20700>0. Since r<25/12, one obtains H(c)<140.

In the present interval, m=c and N_b(-c)=k+bs. The penalty sum

\[
 a+\frac{k}{\sqrt2}(1+2c)+k+bs
\]

is concave and exceeds 89 at both endpoints. At c=1/sqrt(2), use
1/sqrt(2)>7/10 to obtain reserve 221/160 above 89. At c=23/24,
use the same inequality and sqrt(47)>34/5; the reserve above 89
is 113/640. Therefore

\[
 F_{45}(c)>T+89-140=7/4>0.
\]

### 4.3. The interval 23/24<=c<=1

Here N_b(-c)=b(c+s). Since bc>=k,

\[
 L_a\le a+k,\qquad
 L_b=\sqrt{(bs)^2+(bc-k)^2}\le bs+bc-k,
\]

and hence H(c)<=r[a+b(c+s)]. Using c+s<3/2, r<25/12,
1/sqrt(2)>7/10, and 1+2c>=35/12, it follows that

\[
 \begin{split}
 F_{45}(c)
 &>T-\frac{13}{12}(a+3b/2)+\frac{7k}{10}\frac{35}{12}\\
 &=\frac{2839}{384}>0.
 \end{split}
\]

This finishes the complete negative-diagonal candidate, all original
owners, and all signed frame endpoints. Together with the inherited
aligned cap and the concavity reduction, it proves (1).

## 5. Scope for the weak-outer mask

The theorem strengthens the endpoint penalty only for an actual upward
owned separator paired with the stated negative M chirality. It may be
reflected with the entire physical coordinate system. A separate caller
must establish this signed pairing; a center-height comparison is not a
substitute. No fixed mask is closed by this local theorem alone.

The small rational comparisons in the proof are independently reconstructed
by `computer_assisted/extraction_search_signed_cap_arithmetic.py`. The
displayed concavity and monotonicity arguments supply continuous-domain
coverage; arithmetic output is not being substituted for a missing cover.
