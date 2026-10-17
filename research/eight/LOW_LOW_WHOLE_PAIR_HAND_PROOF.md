# The entire low/low frame-pair entry by hand

This proves the whole \(L/L\) entry of the four-type frame table,
with target \(.91\). It is valid for all relative frame angles and all
retained separating axes, before assuming frame concentration.

## 1. Domain and elementary bounds

Set
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 u=.403875,\quad v=1.089065,\quad \beta=.18.
\]
All displayed decimals denote exact rational numbers. Both positive
states \((a,b)\), \((A,B)\) lie on
\[
 (a+\tfrac12)^2+(b+\tfrac12)^2=Q,
 \qquad 0\le b/a\le\tfrac14.
\]
Write the arc endpoints as \((a_0,0)\) and \((a_1,b_1)\), where
\[
 a_0=\sqrt{Q-1/4}-1/2,\qquad b_1=a_1/4,
 \qquad \frac{17}{16}a_1^2+\frac54a_1+\frac12=Q.
\]
The positive marker is
\[
 L(a,b)=u(a-a_0)+vb,\qquad L_1=L(a_1,b_1).
\]
Direct substitution and squaring give the rational brackets
\[
 a_0\in(a_0^-,a_0^+)=(1.41457,1.41458),
 \quad a_1\in(a_1^-,a_1^+)=(1.29874,1.29875),              \tag{1}
\]
\[
 b_1\in(b_1^-,b_1^+)=(.324685,.3246875),
 \qquad L_1\in(L_1^-,L_1^+)=(.30681,.30683).               \tag{2}
\]
Along this arc,
\[
 a'(b)=-r(b),\quad
 r(b)=\frac{b+1/2}{a+1/2}\in
 \left[\frac1{2a_0+1},.46\right),\qquad a''(b)<0.
\]
Consequently
\[
 0\le L\le b,\qquad L\le L_1<.30683.                     \tag{3}
\]
For the first upper bound, \(L(0)=0\), and
\(L'=v-ur\le v-u/(2a_0^++1)<1\). Positivity and
monotonicity follow from \(v>u\). The brackets in (2) follow from
\(u(a_1^--a_0^+)+vb_1^->.30681\) and the reverse upper comparison.

Give the source and target signs \(\sigma,\tau\in\{-1,1\}\).
Their signed tangent angles are \(\alpha_s=\sigma\arctan(b/a)\)
and \(\alpha_t=\tau\arctan(B/A)\). Suppose their positive directed
center gap satisfies \(\delta>19/25\), and put
\[
 \phi=\delta+\alpha_t-\alpha_s,\qquad
 h(\phi)=\frac{|\cos\phi|+|\sin\phi|-1}{2}.
\]
Since \(|\alpha_s|,|\alpha_t|\le\arctan(1/4)<1/4\), we have
\(\phi>.26>0\). The cost to bound is
\[
 \mathcal C=\phi-\beta h(\phi)+\sigma L(a,b)-\tau L(A,B).
\]

**Theorem.** If one of the retained SAT axes separates the squares, then
\[
 \boxed{\mathcal C>\frac{91}{100}.}                        \tag{4}
\]

It suffices to treat the source secondary and source negative-primary
axes. Reflection followed by reversal of the ordered pair preserves the
cost, changes the signs to \((-\tau,-\sigma)\), and exchanges the
source and target axes. This covers the two retained target axes as well.
The earlier common-point and backward-axis lemmas supply the retained-axis
reduction in the exterior seven-cycle.

For \(\phi\ge\pi/2\), (3), \(h<.21\), and
\(\pi>3.14159\) already give
\[
 \mathcal C>\pi/2-2(.30683)-.18(.21)>.9193>.91.             \tag{5}
\]
Thus assume from now on \(0\le x:=\phi\le\pi/2\), and write
\[
 s=\sin x,\quad c=\cos x,\quad
 h=(s+c-1)/2,\qquad W=1+h.
\]
The two source separators are
\[
 \sigma b+As-\tau Bc\ge W,                               \tag{6}
\]
\[
 a-Ac-\tau Bs\ge W.                                     \tag{7}
\]
All subtractions of a separator below use a nonnegative multiplier, so
they give valid lower bounds for the cost.

## 2. All signs on the secondary axis

### 2.1. Positive target

Use the following two choices, according to the source sign:

| \(\sigma\) | Multiplier \(\lambda\) | Source loss \(\varepsilon\) | Cut \(z\) |
|---:|---:|---:|---:|
| +1 | .945 | .00002 | .96 |
| -1 | 1 | 0 | 1.1 |

After subtracting \(\lambda\) times the margin in (6), the source
contribution is \(\sigma(L-\lambda b)\ge-\varepsilon\).
For the positive source, \(L-\lambda b\) is concave along the
arc and its endpoint values are zero and
\(L_1-\lambda b_1>-.00002\). For the negative source use \(L\le b\).
The target functional is
\[
 ua_0-(u+\lambda s)A+(\lambda c-v)B.                       \tag{8}
\]
Its full-circle lower support gives
\[
 \begin{split}
 \mathcal C\ge G_{\lambda,\varepsilon}(x)
 &=x+.09+ua_0+\frac{u+v+\lambda}{2}-\varepsilon
              +(\lambda-.09)s-.09c-RN_\lambda(x),\\
 N_\lambda^2&=u^2+v^2+\lambda^2+2\lambda(us-vc).
 \end{split}                                               \tag{9}
\]
Section 4 proves \(G_{\lambda,\varepsilon}>.91\) on
\([0,z]\) by one degree-eight polynomial row for each choice.

For \(x\ge z\), the target functional (8) decreases with \(B\).
Indeed its derivative is at most
\[
 .46u+\lambda(.46\sin x+\cos x)-v.
\]
The parenthesized expression decreases on \([z,\pi/2]\), because
\(\sin z>.46\cos z\); its derivative is
\(.46\cos x-\sin x\), itself strictly decreasing there.
The upper Taylor bounds at the two cuts give
\[
 .46u+\lambda(.46\sin z+\cos z)-v<0.
\]
Thus the minimum of (8) is its last endpoint. This gives
\[
 \mathcal C\ge E_{\lambda,\varepsilon}(x):=
 x-\varepsilon-L_1+\frac{\lambda+\beta}{2}
 +\left(\frac{\lambda-\beta}{2}+\lambda b_1\right)c
 +\left(\frac{\lambda-\beta}{2}-\lambda a_1\right)s.       \tag{10}
\]
Section 4 proves \(E_{\lambda,\varepsilon}>.91\) on
\([z,\pi/2]\) by one degree-six polynomial row for each choice.
This covers both source signs with a positive target.

### 2.2. Negative target, either source sign

Take \(\lambda=.96\) and \(\varepsilon=.013\). For a positive
source, concavity gives \(L-\lambda b\ge\min(0,L_1-\lambda b_1)
>-.013\). For a negative source, (3) gives
\(-L+\lambda b\ge-.04b>-.013\). The target functional is now
\[
 -ua_0+(u-\lambda s)A+(v-\lambda c)B.
\]
Its \(B\) coefficient is positive. Its minimum is therefore at an
arc endpoint: if the \(A\) coefficient is nonnegative, use concavity;
if it is negative, the functional increases with \(B\).
With \(d_\lambda=(\lambda-\beta)/2\), the resulting two bounds are
\[
 \begin{split}
 A_\lambda(x)&=x-\varepsilon+\frac{\lambda+\beta}{2}
                  +d_\lambda c+(d_\lambda-\lambda a_0)s,\\
 B_\lambda(x)&=x-\varepsilon+L_1+\frac{\lambda+\beta}{2}
                +(d_\lambda-\lambda b_1)c
                +(d_\lambda-\lambda a_1)s.
 \end{split}                                               \tag{11}
\]
The lower polynomial for \(A_\lambda-.91\) is the last row in
Section 4. For \(B_\lambda\), its positive cosine coefficient and
negative sine coefficient give the simpler estimate
\[
 B_\lambda'(x)\ge
 1-(d_\lambda-\lambda b_1)-(\lambda a_1-d_\lambda)
 =1-\lambda(a_1-b_1)>0.
\]
The rational brackets already imply this strict inequality. At zero,
\[
 B_\lambda(0)=-\varepsilon+L_1+\lambda-\lambda b_1>.94211>.91.
\]
Therefore both endpoint bounds exceed \(.91\), finishing the
entire secondary axis.

## 3. All signs on the negative-primary axis

The separator (7) does not depend on \(\sigma\). For either target
sign, it is therefore enough to prove the negative-source case; a positive
source adds \(2L(a,b)\ge0\) to the same feasible pair.

### 3.1. Positive target

First, \(0\le x\le1.3\) is impossible. The left side of (7) is
at most \(a_0-a_1c\), so separation would require
\[
 N(x):=a_0-.5-(a_1+.5)c-.5s\ge0.
\]
The function \(N\) is convex on this interval, so its maximum
occurs at an endpoint. Both \(N(0)\) and \(N(1.3)\) are
negative, using (1) and the lower sine/cosine Taylor polynomials.

For \(1.3\le x\le\pi/2\), subtract \(\lambda=.9\) times
the margin in (7). The source and target functionals, apart from their
canceling constants, are
\[
 -(u+\lambda)a-vb,
 \qquad(-u+\lambda c)A+(\lambda s-v)B.
\]
They both decrease along their low arcs: their derivatives are bounded
above by \((u+\lambda)(.46)-v<0\) and
\(u(.46)+\lambda-v<0\), respectively. Thus both minima are
at the last endpoint. It follows that
\[
 \begin{split}
 \mathcal C\ge P(x):={}&x-2L_1+\frac{\lambda+\beta}{2}-\lambda a_1\\
 &+\left(\frac{\lambda-\beta}{2}+\lambda a_1\right)c
  +\left(\frac{\lambda-\beta}{2}+\lambda b_1\right)s.
 \end{split}                                               \tag{12}
\]
Both trigonometric coefficients are positive, hence \(P''<0\)
on the interval. Its minimum is at an endpoint. With the rational
brackets and Taylor bounds, \(P(1.3)>.91\) and
\(P(\pi/2)>.98>.91\). No interior angle estimate is needed.

### 3.2. Negative target

For \(x\ge1.3\), simply use
\[
 \mathcal C\ge x-L_1-\beta h>1.3-.30683-.18(.21)>.91.
\]
For \(0\le x\le1.3\), take \(\lambda=5/4\). The source
functional is again minimized at the last endpoint, since
\((u+\lambda)(.46)<v\). The target functional has positive
\(A\) coefficient \(u+\lambda c\), so it is concave along the
arc and its minimum is at one of the two endpoints. Consequently
\[
 \mathcal C\ge\min\{P_a(x),P_b(x)\},
\]
where, with \(d_\lambda=(\lambda-\beta)/2\),
\[
 \begin{split}
 P_a(x)&=x-L_1+\frac{\lambda+\beta}{2}-\lambda a_1
                    +(d_\lambda+\lambda a_0)c+d_\lambda s,\\
 P_b(x)&=x+\frac{\lambda+\beta}{2}-\lambda a_1
             +(d_\lambda+\lambda a_1)c+(d_\lambda-\lambda b_1)s.
 \end{split}                                               \tag{13}
\]
All sine and cosine coefficients are positive. Each function is concave,
so only \(0\) and \(1.3\) must be checked. The four rational lower
endpoint values all exceed \(.91\). This finishes both target signs
and therefore the entire negative-primary axis.

## 4. Five explicit polynomial rows

Here are all polynomial comparisons used in Section 2. Define
\[
 S_3=x-x^3/6,\quad S_5=x-x^3/6+x^5/120,
\]
\[
 C_4=1-x^2/2+x^4/24,\qquad
 C_6=1-x^2/2+x^4/24-x^6/720.
\]
On \([0,11/7]\), the standard alternating bounds give
\(S_3\le\sin x\le S_5\) and
\(C_6\le\cos x\le C_4\).

For each of the two \((\lambda,\varepsilon,z)\) choices in Section
2.1, put
\[
 \begin{split}
 T_{\lambda,\varepsilon}(x)={}&x+.09+ua_0^-
       +\frac{u+v+\lambda}{2}-.91-\varepsilon
                        +(\lambda-.09)S_3-.09C_4,\\
 V_\lambda(x)={}&u^2+v^2+\lambda^2
                         +2\lambda(uS_5-vC_6),\\
 F_{\lambda,\varepsilon}(x)={}&T_{\lambda,\varepsilon}^2-QV_\lambda.
 \end{split}                                               \tag{14}
\]
On the corresponding interval \([0,z]\), \(T>0\): indeed
\(S_3\ge0\), \(C_4\le1\), and its remaining constant minus
\(.09\) exceeds \(.88\). Also \(V_\lambda\ge N_\lambda^2\).
Thus \(F>0\) proves \(G_{\lambda,\varepsilon}>.91\) after
squaring two nonnegative sides. This step introduces no extraneous root.

For the endpoint bounds (10), define
\[
 J_{\lambda,\varepsilon}(x)=x-\varepsilon-L_1^+
       +\frac{\lambda+\beta}{2}-.91
 +\left(\frac{\lambda-\beta}{2}+\lambda b_1^-\right)C_6
 +\left(\frac{\lambda-\beta}{2}-\lambda a_1^+\right)S_5.
                                                               \tag{15}
\]
Its cosine coefficient is positive and its sine coefficient negative,
so it is a lower bound for \(E_{\lambda,\varepsilon}-.91\).

Finally, for the axial bound in (11), with \(\lambda=.96\),
\(\varepsilon=.013\), \(d_\lambda=.39\), define
\[
 Z(x)=x-\varepsilon+\frac{\lambda+\beta}{2}-.91
                    +d_\lambda C_6+(d_\lambda-\lambda a_0^+)S_5.
                                                               \tag{16}
\]
This is a lower bound for \(A_\lambda-.91\).

For a polynomial \(P\) on \([l,r]\), use the Bernstein expansion
\[
 P(l+(r-l)t)=\sum_{j=0}^n B_j\binom nj t^j(1-t)^{n-j}.
\]
If all \(B_j>0\), then \(P>0\) on the entire closed interval.
The following are lower bounds for all the coefficients. Every listed
integer is divided by \(10^7\). The degree-six polynomial \(Z\)
is expressed in the degree-seven Bernstein basis.

| Polynomial | Interval | Degree | Lower coefficient numerators |
|---|---|---:|---|
| \(F_{.945,.00002}\) | \([0,.96]\) | 8 | 548963, 881234, 1045788, 1108067, 1109559, 1060273, 933679, 665095, 154640 |
| \(J_{.945,.00002}\) | \([.96,11/7]\) | 6 | 87880, 36707, 21718, 62261, 175975, 377007, 673722 |
| \(F_{1,0}\) | \([0,1.1]\) | 8 | 1543096, 1962322, 2150549, 2208476, 2188950, 2081340, 1802756, 1198887, 57531 |
| \(J_{1,0}\) | \([1.1,11/7]\) | 6 | 139832, 92446, 78059, 105371, 182135, 314616, 506922 |
| \(Z\) | \([0,11/7]\) | 7 | 370000, 441843, 284387, 76501, 25367, 329670, 1131139, 2454431 |

All 40 coefficients are positive. Since \(\pi/2<11/7\), these
five fixed rows cover the required angle intervals.

The coefficient conversion itself is finite rational arithmetic. If
\(P(x)=\sum p_jx^j\), the coefficient of \(t^k\) after the
interval substitution is
\[
 q_k=\sum_{j=k}^n p_j\binom jk l^{j-k}(r-l)^k,
\quad\text{and}\quad
 B_k=\sum_{j=0}^kq_j\frac{\binom kj}{\binom nj}.
\]
These formulas reproduce every displayed lower integer without a root
solver or domain subdivision. The optional replay
verify_low_low_whole_pair_hand.py checks those 40 coefficients and
36 strict rational scalar comparisons, including every primary-axis
endpoint and support monotonicity condition.

## 5. Coverage

The large-frame estimate (5) covers all signs and axes. On the remaining
interval, Sections 2.1--2.2 cover all four secondary-axis sign patterns;
Sections 3.1--3.2 cover all four negative-primary patterns. Reflection
and order reversal cover the retained target axes. All intervals include
their endpoints, and either valid axis may be used in a separating-axis
tie. Hence (4) holds on the entire low/low pair domain. \(\square\)
