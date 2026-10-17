# Ten mixed zero-quarter contact families for the word 0010111

Status: hand proof of the ten complete regimes listed below. This is a component of the short wrong-word argument; the entire seven-role pair table is not asserted here.

The proof uses elementary monotonicity, the support of a circle, one concavity identity, and 68 fixed rational comparisons. It contains no adaptive interval cover and no numerical-minimum premise. The companion exact BigInt checker is verify_short_wrong_mixed_zero_hand.js. Its reported cost lower bounds are consequences of the displayed analytic reductions.

## 1. Geometry, labels, and the exact scope

Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 d=\sqrt{Q/2}-\frac12,\quad
 d_C=\frac12+\frac{\sqrt2}{24},\quad
 a_0=\sqrt{Q-\frac14}-\frac12.
\]
An outer state has coordinates \(a\ge b\ge0\) and
\[
 (a+\tfrac12)^2+(b+\tfrac12)^2=Q.
\]
Thus \(0\le b\le d\) and \(a=a(b)=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12\).
A core state is on the boundary at clearance \(1/12\):
\[
 a=\frac7{12},\ 0\le b\le\frac12,
 \qquad\hbox{or}\qquad
 (a-\tfrac12)^2+(b-\tfrac12)^2=\frac1{144},\
 a\ge b\ge\frac12.
\]
In particular \(a\ge d_C\), \(b\le d_C\), and the primary coordinate is nonincreasing as \(b\) increases.

A signed label is
\[
 \ell_i(a,\sigma b)=c_i+p_i a+\sigma q_i b.
\]
All coefficients below are exactly those of 0010111_affine_hand_candidate_v1.json; each terminating decimal is an exact rational.

For a directed edge, let \(\phi\) be the target frame angle minus the source frame angle. In a zero-quarter edge, \(|\phi|\le7/10\). Write
\[
 W(\phi)=\frac{1+|\sin\phi|+|\cos\phi|}{2},\qquad
 C=\phi+\ell_{\rm source}-\ell_{\rm target}.
\]
This note proves \(C>449/500=.898>17953/20000\) for the following regimes.

| Group | Original edge and kinds | Original signs | Separating axis | Angle range |
|---|---|---|---|---|
| A1 | 1: C to O | -- | source \(+f\) | whole \([-.7,.7]\) |
| A2 | 3: C to O | -- | source \(+f\) | whole \([-.7,.7]\) |
| A3 | 0: O to C | ++ | target \(+f\) | whole \([-.7,.7]\) |
| A4 | 3: O to C | ++ | target \(+f\) | whole \([-.7,.7]\) |
| B1 | 0: O to C | +- | source \(+f\) | \([-.7,0]\) |
| B2 | 0: C to O | +- | target \(+f\) | \([-.7,0]\) |
| B3 | 1: O to C | +- | source \(+f\) | \([-.7,0]\) |
| B4 | 1: C to O | +- | target \(+f\) | \([-.7,0]\) |
| B5 | 3: O to C | +- | source \(+f\) | \([-.7,0]\) |
| B6 | 3: C to O | +- | target \(+f\) | \([-.7,0]\) |

Here the word's zero edges are exactly 0, 1, 3. Reflection followed by reversal leaves \(\phi\) unchanged and sends the source and target labels to the negatives of the old target and source labels. A coefficient triple \((c,p,q)\) becomes \((-c,-p,q)\), and signs reverse. This turns A3/A4 into C--O source-\(+f\) cases, and B2/B4/B6 into O+-C source-\(+f\) cases. The transformations preserve the cost exactly.

The useful coarse bounds are
\[
 .8992140<d<.8992141,\qquad .5589<d_C<.559,\qquad
 a_0>1.414,\qquad R<2.
 \tag{1.1}
\]

## 2. All four negative-core to negative-outer families

After the stated reflection/reversal, write the core label as \(c_s-gb\) and the outer label as \(c_t+pA-qB\). The cost is
\[
 C=\phi+c_*-gb-pA+qB,\qquad c_*=c_s-c_t,
\]
and the source-\(+f\) separation inequality is
\[
 -b+A\sin\phi+B\cos\phi\ge W(\phi).
 \tag{2.1}
\]

The exact coefficient rows are:

| Row | \(c_*\) | \(p\) | \(q\) | \(g\) |
|---|---:|---:|---:|---:|
| A1 | -.11418 | .09133 | .88074 | .62095 |
| A2 | .07943 | .19335 | .76744 | .62750 |
| A3 | -.25648 | 0 | .94766 | .62095 |
| A4 | -.94615 | -.51554 | 1.19909 | .58829 |

### 2.1. Feasibility forces \(\phi>.3024\)

For \(\phi\le0\), the left side of (2.1) is at most \(B\le d<1\), whereas \(W\ge1\). Hence \(\phi>0\). On \([0,.7]\), \(\cos\phi>\sin\phi\), so the maximum of \(A\sin\phi+B\cos\phi\) along the outer arc is at \(A=B=d\): its derivative with respect to \(B\) is at least \(\cos\phi-\sin\phi>0\). Therefore (2.1) implies
\[
 (d-\tfrac12)(\sin\phi+\cos\phi)\ge\frac12.
\]
The left side is increasing on this interval. The single rational Taylor comparison
\[
 (d-\tfrac12)(\sin(.3024)+\cos(.3024))<\frac12
 \tag{2.2}
\]
proves the claim.

### 2.2. A concave lower envelope removes both state variables

Choose \(\lambda\ge g\) and subtract \(\lambda\) times the nonnegative SAT margin in (2.1). The remaining core term is \((\lambda-g)b\ge0\). The outer term has coefficients
\[
 -p-\lambda\sin\phi,\qquad q-\lambda\cos\phi.
\]
Enlarging its arc to its full circle gives
\[
 C\ge F_\lambda(\phi)
 =\phi+c_*+\frac{\lambda+p-q}{2}
  +\lambda(\sin\phi+\cos\phi)-R N(\phi),
 \tag{2.3}
\]
where
\[
 N^2=p^2+q^2+\lambda^2+
       2\lambda(p\sin\phi-q\cos\phi).
 \tag{2.4}
\]
Let \(L=\sqrt{p^2+q^2}\). The elementary norm identity
\[
 N''+\frac N4=\frac{(L^2-\lambda^2)^2}{4N^3}\ge0
\]
and \(N\le L+\lambda\), \(R<2\), \(\sin\phi+\cos\phi\ge1\), imply
\[
 F_\lambda''\le-\lambda+\frac{R N}{4}
 <-\lambda+\frac{\lambda+L}{2}<0
 \tag{2.5}
\]
whenever \(\lambda>L\). All multipliers in the next table satisfy \(\lambda>g\) and \(\lambda>L\). Thus only the two endpoints of each displayed interval need comparison.

| Row | Interval | \(\lambda\) | Left endpoint lower bound | Right endpoint lower bound |
|---|---|---:|---:|---:|
| A1 | [.3024,.6] | 1.48 | .898082891 | .933939892 |
| A1 | [.6,.7] | 2 | 1.015375055 | .992066344 |
| A2 | [.3024,.7] | 1.463 | .898073945 | .932576398 |
| A3 | [.3024,.6] | 1.443 | .898083147 | .914307860 |
| A3 | [.6,.7] | 2 | 1.017405583 | .990208615 |
| A4 | [.4,.7] | 1.6 | .909737777 | .930376146 |

Every displayed lower bound is a rational obtained by outward root brackets and alternating Taylor bounds at that fixed endpoint. Formula (2.5), not a subdivision of the state space, extends the bounds over the whole intervals.

### 2.3. The remaining A4 interval [.3024,.4]

Use \(\lambda=1.19\). Its outer secondary coefficient is
\(q-\lambda\cos\phi\ge q-\lambda>0\).
For any real primary coefficient and a nonnegative secondary coefficient, the minimum of a linear function on this outer arc is at its axial or diagonal endpoint. Indeed, if the primary coefficient is nonnegative the function is concave in \(B\); if it is negative its derivative is positive.

The two lower envelopes are
\[
 F_{\rm diag}(\phi)
 =\phi+c_*+(q-p)d+
  \lambda\{\tfrac12-(d-\tfrac12)(\sin\phi+\cos\phi)\},
\]
\[
 F_{\rm ax}(\phi)
 =\phi+c_*-p a_0+\frac\lambda2+
   \frac\lambda2\cos\phi-\lambda(a_0-\tfrac12)\sin\phi.
\]
The first is increasing because its derivative exceeds \(1-.4\lambda>0\). The second is decreasing on the stated interval:
\[
 F_{\rm ax}'<1-\lambda(.914)(.92)<0,
\]
using \(a_0-\tfrac12>.914\), \(\cos(.4)>.92\).
The fixed comparisons are
\[
 F_{\rm diag}(.3024)>.898080923,\qquad
 F_{\rm ax}(.4)>.902330108.
\]
This completes all four A regimes.

## 3. All six mixed (+,-) negative-angle families

After reflection/reversal where stated, put \(\phi=-x\), \(x\ge0\), and let the outer source label be \(c_s+p a+q b\), the core target label \(c_t-gB\). Then
\[
 C=-x+c_*+p a+q b+gB,
 \qquad
 b-A\sin x+B\cos x\ge \frac{1+\sin x+\cos x}{2}.
 \tag{3.1}
\]
The exact rows are:

| Row | \(c_*\) | \(p\) | \(q\) | \(g\) | Method |
|---|---:|---:|---:|---:|---|
| B1 | .14041 | 0 | .94766 | .62095 | two endpoints |
| B2 | -.21286 | .13422 | 1.03828 | 1.08816 | monotone envelope |
| B3 | -.05550 | 0 | .99940 | 1.13855 | monotone envelope |
| B4 | .28271 | -.09133 | .88074 | .62095 | explicit contact |
| B5 | -.72700 | .51554 | 1.19909 | 1.04073 | monotone envelope |
| B6 | .27632 | -.19335 | .76744 | 1.04729 | monotone envelope |

### 3.1. Feasibility gives the uniform short interval

The core projection \(-A\sin x+B\cos x\) increases with \(B\) and is at most \(d_C(\cos x-\sin x)\). Since \(b\le d\), feasibility implies
\[
 d-\tfrac12+(d_C-\tfrac12)\cos x-(d_C+\tfrac12)\sin x\ge0.
 \tag{3.2}
\]
Its left side is strictly decreasing for \(0\le x\le.7\). At
\[
 h=.44152
\]
one fixed Taylor comparison makes it negative (by more than \(5\cdot10^{-6}\)). Hence \(0\le x<h\). We may use \(\cos x>.9\).

### 3.2. Four rows have an increasing envelope

For B2, B3, B5, B6 choose
\[
 \lambda(x)=g/\cos x.
\]
Subtracting \(\lambda\) times the SAT margin leaves the core functional \(\lambda\sin x\,A\), at least \(\lambda\sin x\,d_C\). For B2, B3, B6, the outer functional
\[
 p a+(q-\lambda)b
\]
is minimized at \(a=b=d\), since
\[
 \lambda\ge g>q-\min(p,0).
 \tag{3.3}
\]
For B5 the secondary coefficient is nonnegative because
\(g/.9<q\). Hence the outer endpoint rule applies. Its diagonal endpoint is the smaller one, as follows from the single comparison
\[
 (p+q-g)d<p a_0.
 \tag{3.4}
\]
The diagonal value only decreases when \(\lambda\) increases.

We obtain the same envelope in all four cases:
\[
 F(x)=-x+c_*+(p+q)d+\frac g2+
       g(\tfrac12-d)\sec x+g(\tfrac12+d_C)\tan x.
 \tag{3.5}
\]
Set \(s=\sin x\). Its derivative is
\[
 F'=-1+g\frac{(\tfrac12+d_C)-(d-\tfrac12)s}{1-s^2}.
\]
The quotient exceeds 1 because
\[
 s^2-(d-\tfrac12)s+(d_C-\tfrac12)
 \ge d_C-\tfrac12-\frac{(d-\tfrac12)^2}{4}
 >.0589-\frac{.4^2}{4}>0.
\]
Each of the four \(g\)'s is greater than 1. Thus \(F'>0\). Only \(x=0\) remains, where
\[
 F(0)=c_*+(p+q)d+g(1-d).
\]
The fixed lower bounds for B2, B3, B5, B6 respectively are
\[
 .951139714,\qquad .957924362,\qquad
 .919710358,\qquad .898101904.
 \tag{3.6}
\]

### 3.3. Row B1 has no interior minimum

Use the constant multiplier \(\lambda=q=.94766\). The source functional vanishes. Since \(\lambda\cos h>g\), the remaining core functional has a nonnegative primary coefficient and a negative secondary coefficient; its minimum is at \(A=B=d_C\). Thus
\[
 C\ge F(x)=-x+c_*+g d_C+\frac\lambda2+
 \lambda(\tfrac12-d_C)\cos x+
 \lambda(\tfrac12+d_C)\sin x.
 \tag{3.7}
\]
Here \(F'''<0\) for \(0\le x\le h\), and
\[
 F'(0)=-1+\lambda(\tfrac12+d_C)>0.
\]
Therefore the concave function \(F'\), starting positive, can cross zero at most once and only from positive to negative. The minimum of \(F\) is at an endpoint. The two rational lower bounds are
\[
 F(0)>.905463428,\qquad F(h)>.898108834.
 \tag{3.8}
\]

### 3.4. Row B4 reduces exactly to the core diagonal contact

In B4, \(p<0\), so \(f(b)=p a(b)+q b\) satisfies \(f'(b)>q>0\).
At fixed core state the cost is minimized by reducing \(b\) until (3.1) is an equality. Along that equality,
\[
 b=W(x)+A(B)\sin x-B\cos x.
\]
This value is positive even at the largest possible \(B=d_C\), and decreases with \(B\). Increasing the core transverse coordinate while remaining on contact changes the cost at rate
\[
 g+f'(b)\{A'(B)\sin x-\cos x\}
 \le g-q\cos x<0.
 \tag{3.9}
\]
This holds on both core side and corner, and across their common endpoint. A feasible contact therefore attains its minimum at \(A=B=d_C\).

Put
\[
 b(x)=\frac12+(\frac12+d_C)\sin x+
                    (\frac12-d_C)\cos x,\qquad
 Y(x)=\sqrt{Q-(b(x)+\tfrac12)^2}.
\]
The exact reduced cost is
\[
 H(x)=-x+.28271-.09133(Y(x)-\tfrac12)
                         +.88074 b(x)+.62095 d_C.
 \tag{3.10}
\]
The formula is well defined through \(x=h\), even though the endpoint used to extend the interval has \(b(h)\) slightly larger than the actual outer diagonal. This harmless extension will only be used for a lower bound.

We prove \(H'<0\) throughout by one strong-concavity comparison. Write
\(f(b)=p a(b)+q b\), with \(p=-.09133,q=.88074\). The identities
\[
 b''=\frac12-b,\quad b'''=-b',\quad
 f''=\frac{-pQ}{Y^3},\quad
 f'''=\frac{-3pQ(b+\frac12)}{Y^5}
\]
give
\[
 H'''=b'\{f'''(b')^2+3f''b''-f'\}.
 \tag{3.11}
\]
On \([0,h]\), the following coarse rational bounds hold:
\[
 .95<b',\quad
 (b')^2<1.06^2+.059^2,\quad
 b''<.059,\quad b<.8993,\quad Y>1.399,\quad f'>.88.
\]
For example \(b<.8993\) is a single endpoint comparison; the root bound follows from
\(Q-1.3993^2>1.399^2\).
Consequently the expression in braces in (3.11) is less than
\[
 \frac{3(.092)(4)(1.4)}{1.399^5}
       (1.06^2+.059^2)
 +\frac{3(.092)(4)}{1.399^3}(.059)-.88.
\]
Multiplying this negative upper bound by .95 gives a number below \(-1/2\). Hence \(H'''<-1/2\).

At the single rational reference point \(r=.14\), outward root brackets and Taylor bounds prove
\[
 H'(r)<-.0055,\qquad |H''(r)|<.005.
\]
Taylor's inequality applied to the strongly concave function \(H'\) now gives, for every \(x\),
\[
 H'(x)\le H'(r)+H''(r)(x-r)-\frac14(x-r)^2
 \le-.0055+.005^2<0.
 \tag{3.12}
\]
Therefore \(H\) is decreasing. Its last fixed comparison is
\[
 H(h)>.898108332.
 \tag{3.13}
\]
This proves B4, and completes all ten regimes.

## 4. Exact arithmetic and the remaining proof interface

The checker uses exact rational BigInt arithmetic. For each displayed rational angle \(0\le t\le.7\), it encloses sine and cosine between their alternating Taylor sums ending at indices 7 and 8. Positive square roots are enclosed by rational decimal endpoints whose squares are checked exactly. There are 68 strict fixed comparisons.

The interval arguments in Sections 2 and 3 are analytic concavity, monotonicity, or contact contractions. The rational comparisons only evaluate their finitely named endpoints or a single derivative reference point. They do not stand in for a global optimization argument.

The note closes exactly the ten regimes in the first table. Other sign/axis regimes of the 0010111 candidate table remain separate obligations. In particular, this component alone does not prove exclusion of the word or closure of the unrestricted eight-square theorem.

