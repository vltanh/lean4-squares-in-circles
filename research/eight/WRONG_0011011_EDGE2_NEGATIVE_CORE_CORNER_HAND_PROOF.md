# 0011011: the complete negative outer-to-core-corner edge-2 transition

## Theorem

Let the source be an outer state with negative sign on edge 2, and
let the target be a core **corner** state with negative sign on role 3.
For every retained separating axis and every
\[
 \pi/2-.7\le\phi\le\pi/2+.7,
\]
the corrected cost satisfies
\[
 \phi-L(b)+C_3^-(A,B)>.89765.
\tag{1}
\]
All constants are the exact rational labels from
\`wrong_0011011_labels.json\`. This note covers the entire core corner,
including its join with the side and its diagonal endpoint. The
core-side target away from the join is outside this particular theorem.

The proof uses three explicit polynomial inequalities on one interval,
five short monotonicity intervals, and fixed endpoint comparisons.
The companion checker makes 82 exact rational comparisons. It does
not perform a minimizing search or an adaptive subdivision.

Set
\[
 Q=3.9156,\quad c=7/12,\quad d_C=1/2+1/(12\sqrt2),\quad
 d=\sqrt{Q/2}-1/2.
\]
The outer state obeys
\[
 a=\sqrt{Q-(b+1/2)^2}-1/2,\qquad0\le b\le d,
\]
and the core corner obeys
\[
 (A-1/2)^2+(B-1/2)^2=1/144,\qquad
 1/2\le B\le d_C,\quad A\ge B.
\]
The labels are
\[
\begin{aligned}
 L(b)&=.02478+.93015b+.02363b^2-.11055ab,\\
 C_3^-(A,B)&=.22042-.34492A+.98439B-.05334B^2.
\end{aligned}
\tag{2}
\]
The actual own-frame centers are \((a,+b)\) and \((A,+B)\), since both
signs are negative.

## 1. The late-angle part and two impossible axes

The outer label increases and is convex along the outer arc:
\[
 L'>.773,\qquad L''=.04726+.11055(2r+br')>0,
 \quad r=(b+1/2)/(a+1/2).
\]
Its maximum is at the diagonal and satisfies
\[
 L(d)<.79091.
\]
The core label increases along the corner. At the join it is
\[
 C_3^-(c,1/2)>.49807.
\]
Consequently every pair with \(\phi\ge1.191\), regardless of its axis,
has cost
\[
 >1.191-.79091+.49807=.89816>.89765.
\tag{3}
\]

It remains to consider
\[
 \pi/2-.7\le\phi\le1.191<\pi/2.
\tag{4}
\]
Write \(s=\sin\phi,c_\phi=\cos\phi\), and
\(W=(1+s+c_\phi)/2\).
Axis 1 would require
\(-b+As+Bc_\phi\ge W\). Every core center has norm less than .8,
while \(W\ge1\), so this is impossible.
Axis 2 would require
\(-ac_\phi-bs+A\ge W\), also impossible since \(A<.584<W\).
Thus only axes 3 and 4 remain.

## 2. Axis 3: a whole-interval chord/support bound

Convexity of \(L\) bounds it above by its outer-arc endpoint chord:
\[
 L(b)\le .02478+.853b.
\tag{5}
\]
Indeed its true chord slope is
\(.93015-.08692d<.853\).
Since \(A\le7/12\), \(B<.559\), the target has the lower affine bound
\[
 C_3^-(A,B)\ge c_-+.9545B,\qquad
 c_-:=.22042-.34492(7/12).
\tag{6}
\]
Here \(.98439-.05334(.559)>.9545\).

Axis 3 is
\(as-bc_\phi+B-W\ge0\).
Subtract .9545 times it from the lower cost furnished by (5)--(6).
The standard outer-circle support
\[
 xa+yb\ge-(x+y)/2-\sqrt Q\sqrt{x^2+y^2}
\]
then gives
\[
 F(\phi)=\phi+c_--.02478+\frac{.9545+.853}{2}
             +.9545\sin\phi-\sqrt Q\,N(\phi),
\]
\[
 N^2=.9545^2+.853^2-2(.9545)(.853)\cos\phi.
\tag{7}
\]
The norm is positive and increasing, and
\[
 N''+N/4=\frac{(.9545^2-.853^2)^2}{4N^3}>0.
\]
Thus on (4),
\[
 F''\le-.9545\sin(\pi/2-.7)
           +\frac{\sqrt Q}{4}N(1.191)<0.
\]
Both endpoint values of (7) exceed .96. Concavity therefore proves
(1) for every axis-3 state in (4).

## 3. Axis 4: an exact contact lower bound

The separating inequality is
\[
 a\ge h(B):=W+A(B)c_\phi-Bs.
\tag{8}
\]
Put \(u=a+1/2\) and \(t=\sqrt{Q-u^2}\).
The negative outer label, continued as a function of \(u\), is exactly
\[
 M(u)=.369499372+.02363u^2-.055275u
             -(.961795-.11055u)t.
\tag{9}
\]
For a physical state, \(M(a+1/2)=-L(b)\).
Its derivatives are
\[
\begin{aligned}
 M'&=.04726u-.055275+.11055t+
             \frac{(.961795-.11055u)u}{t},\\
 M''&=.04726-\frac{.22110u}{t}
             +\frac{Q(.961795-.11055u)}{t^3},\\
 M'''&=\frac{3Q(.961795u-.11055Q)}{t^5}.
\end{aligned}
\tag{10}
\]
For \(u\ge1.33\) through the physical axial endpoint, these are
respectively positive, positive, and positive. The third sign is
immediate; the first two follow by their values at 1.33 and
monotonicity. Thus \(M\) is increasing and convex.

For the contact in (8),
\[
 u(B,\phi):=h(B)+1/2
 =1+(A(B)+1/2)c_\phi-(B-1/2)s.
\tag{11}
\]
It decreases in both \(B\) and \(\phi\). On (4) and the full corner,
\[
 1.33<u<1.7.
\tag{12}
\]
The endpoint comparisons proving (12) are the diagonal at 1.191 and
the join at \(\pi/2-.7\).

Even when \(h(B)<d\), (9) is defined and increasing between the contact
height and the actual outer state. Therefore (8) gives the valid
lower bound
\[
 f(B,\phi):=\phi+M(u(B,\phi))+C_3^-(A(B),B).
\tag{13}
\]
No unphysical contact is being assumed to occur: the continued contact
is used only to lower the cost.

## 4. Reducing the core coordinate to two endpoint curves

Write
\[
 w=(B-1/2)/(A-1/2),\qquad 0\le w\le1.
\]
Then
\[
 A'=-w,\qquad A''=-12(1+w^2)^{3/2},\qquad
 u_B=-wc_\phi-s.
\]
In particular \(u_B^2\le1+w^2\), by Cauchy--Schwarz.
Differentiating (13) twice in \(B\) gives
\[
 f_{BB}=M''u_B^2+
           (M'c_\phi-.34492)A''-.10668.
\tag{14}
\]

### 4.1. The early range through \(\phi=1.1\)

Both \(M'\) and \(M''\) increase with \(u\).
In each row below bound \(M''\) using the join at the left endpoint,
and bound \(\delta:=M'c_\phi-.34492\) using the diagonal at the right
endpoint. Monotonicity of (11) and of \(\cos\phi\) gives the bounds
throughout the indicated closed interval.

| Angle interval | \(M''\) is below | \(\delta\) is above |
|---|---:|---:|
| \([\pi/2-.7,.95]\) | 2.57 | .339 |
| \([.95,1.03]\) | 1.90 | .209 |
| \([1.03,1.07]\) | 1.47 | .150 |
| \([1.07,1.085]\) | 1.32 | .129 |
| \([1.085,1.1]\) | 1.27 | .109 |

Every row satisfies \(M''<12\delta\). Equations (14) and
\(u_B^2\le1+w^2\) therefore imply \(f_{BB}<0\).
The entire early corner has its minimum at the join or diagonal.

### 4.2. A bounded-convexity estimate after \(\phi=1.1\)

On \(1.1\le\phi\le1.13\), the same endpoint estimates give
\[
 M''<1.213,\qquad \delta>.0697.
\]
For \(z=\sqrt{1+w^2}\ge1\), (14) gives
\[
 f_{BB}<z^2(1.213-12(.0697)z)-.10668<1.
\tag{15}
\]
Indeed the expression in \(z\) decreases for \(z\ge1\), since
\(2(1.213)<36(.0697)\), and its value at 1 is below 1.

On \(1.13\le\phi\le1.191\), the endpoint bounds instead give
\[
 M''<1.127,\qquad\delta>-.0054.
\]
As \(|A''|\le24\sqrt2<34\), (14) yields
\[
 f_{BB}<2(1.127)+34(.0054)-.10668<3.
\tag{16}
\]

For a function on an interval of length \(\ell\) satisfying \(f''\le K\),
subtracting \(KB^2/2\) makes it concave. Endpoint interpolation gives
\[
 f(B)\ge\min(f_{\rm left},f_{\rm right})-K\ell^2/8.
\tag{17}
\]
Our core-corner length is less than .059. Thus (15)--(17) reduce both
later ranges to the same two endpoint curves, with explicit losses
less than \(.059^2/8\) or \(3(.059)^2/8\).

## 5. One positive-curvature proof for both endpoint curves

For the join use \(A_*=13/12,B_*=0\); for the diagonal use
\(A_*=d_C+1/2,B_*=d_C-1/2\). Write
\[
 u=1+A_*\cos\phi-B_*\sin\phi,\quad
 K=A_*^2+B_*^2>1.12479.
\]
The endpoint cost is
\[
 H(\phi)=\phi+M(u)+C_3^-(A_C,B_C),
\tag{18}
\]
with the constant target state equal to that endpoint.
Here
\[
 u''=-(u-1),\qquad (u')^2=K-(u-1)^2,
\]
so
\[
 H''=M''[K-(u-1)^2]-M'(u-1).
\tag{19}
\]
Since \(M''>0\), replacing \(K\) by \(K_0=1.12479\) lowers this bound.

The following explicit polynomials prove \(H''>.4\) on the **whole**
interval \(1.33\le u\le1.7\).
Set
\[
 q_2=Q-u^2,\quad J=K_0-(u-1)^2,\quad
 k=.11055,\quad V=.961795,\quad z=.02363,
\]
\[
\begin{aligned}
 E={}&(V-ku)\{QJ-u(u-1)q_2\}
             -2kuJq_2-k(u-1)q_2^2,\\
 B_0={}&2zJ-(u-1)(2zu-k/2),\\
 A_0={}&.4-B_0,\qquad
 P=E^2-A_0^2q_2^3.
\end{aligned}
\tag{20}
\]
Substitution of (10) into (19) gives
\(H''\ge B_0+E/q_2^{3/2}\).
Since \(E,A_0,P>0\), equation (20) implies \(H''>.4\).

For a polynomial on \([l,h]\), its Bernstein coefficients are defined
by
\[
 P(l+(h-l)t)=\sum_{j=0}^n b_j\binom nj t^j(1-t)^{n-j}.
\]
Positive coefficients prove positivity on the entire closed interval.
The following lists are strict rational lower bounds for **every**
coefficient on \([1.33,1.7]\):

- \(E\), degree 5:
  \(1.6639,\ 1.3858,\ 1.1359,\ .9266,\ .7658,\ .6529\).
- \(A_0\), degree 2:
  \(.3544,\ .3645,\ .3875\).
- \(P\), degree 10:
  \(1.5254,\ 1.2197,\ .9677,\ .7662,\ .6102,\ .4933,\
    .4088,\ .3495,\ .3091,\ .2822,\ .2642\).

These are just three polynomial identities and twenty positive
coefficients; there is no interval partition in this curvature step.

## 6. Fixed endpoint comparisons and assembly

Strong convexity gives, for each reference \(r\),
\[
 H(\phi)\ge H(r)-H'(r)^2/.8.
\tag{21}
\]
The following fixed comparisons use only rational root brackets and
alternating sine/cosine series:

| Curve | Reference | Lower value | Derivative bound | Completed consequence |
|---|---:|---:|---:|---:|
| diagonal | 1.049 | .8977757 | \(|H'|<.000123\) | \(H>.89777\) |
| join | 1.16 | .900224 | \(|H'|<.00029\) | \(H>.9002\) |

Also,
\[
 H_{\rm diag}(1.1)>.89849,\qquad H_{\rm diag}'(1.1)>0,
 \qquad H_{\rm diag}(1.13)>.89958.
\tag{22}
\]
The positive curvature makes the diagonal curve increasing after 1.1.

For the early range through 1.1, section 4.1 reduces the corner to
endpoints, and (21) gives a cost above .89777.
For \(1.1\le\phi\le1.13\), equations (17) and (22) give
\[
 f>.89849-.059^2/8>.89765.
\]
For \(1.13\le\phi\le1.191\), they give
\[
 f>.89958-3(.059)^2/8>.89765.
\]
This completes axis 4 on (4). Section 2 completed axis 3 there;
the other axes are impossible; section 1 handles every later angle
independently of its axis. The full stated transition (1) is proved.

## Arithmetic convention

All decimals are exact rationals. The checker verifies the rational
enclosure
\(3.141592653589793238<\pi<3.141592653589793239\) from Machin's identity.
Each of its finitely many square-root brackets is checked by integer
squaring, and each trigonometric bracket is an alternating Taylor
bound. Its tables print the exact endpoint bounds and exact polynomial
coefficients used above. No computational search assertion occurs
among the mathematical premises.
