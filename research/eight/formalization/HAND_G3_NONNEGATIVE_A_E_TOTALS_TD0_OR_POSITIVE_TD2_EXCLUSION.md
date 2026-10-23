# Two nonnegative primary totals with TD0 or nonnegative TD2

## 1. Original scope and the two retained totals

Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad h=\frac7{10},
 \quad L=\frac16,\quad d=h-L=\frac8{15},
 \quad \eta=\frac{293}{1000},
\]
\[
 a_0=\sqrt{Q-\frac14}-\frac12,\qquad
 c_0=\sqrt{Q/2}-\frac12,\qquad
 \sigma=R\sqrt{1+\eta^2}-\frac{1+\eta}{2}.
\tag{1}
\]
Retain an original G0--G2 boundary cycle at Q, its four sorted
outer states H,G,B,D, and their signed tangents respectively
positive, negative, negative and negative. E is nonpositive.
A and T may have either sign and either radial kind; E may be
outer or true core. Retain BT2 and either HG0 or HG2. The actual
errors obey
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+\le h.
\tag{2}
\]
No frame order is assumed.

The **A-primary total a** has the following precise meaning.
Retain GA2 or GA3 and AB0 or AB2. If both are secondary, put
a=0. If exactly one is primary, its actual error is a and is
nonnegative. If both GA3 and AB2 are primary, their individual
errors may have either sign, and their sum a is nonnegative.

Define the **E-primary total e** in the same way from DE2/DE3
and EH0/EH1: zero if both are secondary, the nonnegative actual
error if there is one primary, or the nonnegative signed sum
of the two primary errors if there are two.

**Theorem.** There is no such original cycle with either

* TD2 of nonnegative error z, with a,e nonnegative as above; or
* TD0 of arbitrary error, with a,e nonnegative as above.

The theorem permits opposite signs within each selected primary
pair. It retains BT2. Negative A total, negative E total, and a
negative TD2 error are not assertions of this theorem.

The proof uses the existing signed A/E charge comparisons, two
explicit continuous weight families, and twelve intrinsic scalar
endpoints. The two weight domains are a whole triangle and a whole
rectangle. Their polynomial bounds use coefficient sums on those
entire domains; there is no subdivision or state enumeration.

## 2. The support charge is subadditive

For sorted circle support write
\[
 S(f,g)=\max_{0\le b\le c_0}
 \left\{f\left(\sqrt{Q-(b+\tfrac12)^2}-\tfrac12\right)+gb\right\},
\]
\[
 W(t)=\frac{1+\cos t+|\sin t|}{2},\qquad
 j(t)=W(t)-1-S(\sin t,1-\cos t),\quad 0\le t\le h.
\tag{3}
\]
The signed comparison theorems
[for A](HAND_G3_COMBINING_THE_TWO_A_PRIMARY_ERRORS.md) and
[for E](HAND_G3_COMBINING_THE_TWO_E_PRIMARY_ERRORS.md) give the
pointwise extra charges
\[
                              l j(a),\qquad j(e)
\tag{4}
\]
when the two A weights are l and the two E weights are one.
For a single primary the same statement follows by inserting
the corresponding virtual zero argument. For two primaries it
is the proved signed half-angle comparison. No new actual owner
is selected in (4).

We will also use
\[
                    j(a)+j(e)\ge j(a+e),\qquad a,e\ge0,
                    \quad a+e\le h.
\tag{5}
\]
Here is a proof that does not assume global concavity of j.
Put
\[
 b_0=\sqrt{Q-\frac14},\qquad
 \alpha_0=2\arctan\frac1{2b_0}.
\]
The exact support formula is
\[
 j(t)=
 \begin{cases}
 \frac{\cos t-1}{2}+(\frac12-a_0)\sin t,&t\le\alpha_0,\\
 \sin t-2R\sin(t/2),&t\ge\alpha_0.
 \end{cases}
\tag{6}
\]
Its values and first derivatives agree at the transition. The
already proved lower cut is \(\alpha_0>1/2\). Also
\[
 b_0>\frac{19}{10},\qquad
 \alpha_0<\frac1{b_0}<\frac{10}{19}<\frac8{15}.
\tag{7}
\]

Let \(F(t)=tj'(t)-j(t)\). On the axis formula,
\(F'(t)=tj''(t)\), while
\(j''=-\tfrac12\cos t+(a_0-\tfrac12)\sin t\) is strictly
increasing on \([0,8/15]\). Thus F first decreases and then
increases, with either phase possibly empty. If \(v=8/15\),
alternating Taylor bounds and \(a_0-1/2<.915\) give
\[
\begin{split}
 F(v)&\le\tfrac12\{1-C_6(v)-vS_7(v)\}
                  +.915\{S_9(v)-vC_6(v)\}\\
 &= -\frac{19224100649008}{908224365234375}<-\frac1{50}.
\end{split}
\tag{8}
\]
Here \(C_n,S_n\) denote the ordinary degree-n cosine and sine
Taylor polynomials. Since F(0)=0, this proves F<0 up to the
actual transition. On the second formula in (6),
\[
                  j''(t)=\sin(t/2)\{R/2-2\cos(t/2)\}<0.
\]
Hence F continues to decrease. Therefore j(t)/t is strictly
decreasing on \((0,h]\). Applying that ratio comparison at
a and e proves (5), including zero arguments by continuity.
Both formulas in (6) also show j(t)<0 for t>0.

## 3. The actual force sum and its variation domain

First retain TD2 with z nonnegative, and put
\[
                   \theta=a+z,\qquad \delta=\theta+e.
\tag{9}
\]
Equation (2) implies \(0\le\delta\le h\), because the positive
parts of each selected signed pair sum to at least its
nonnegative signed total.

Choose weights \((k,l,l,m,c,1,1)\) in cyclic order, where
\[
                        m=m(z)=c(\cos z+\eta\sin z).
\tag{10}
\]
After the A/E comparisons (4) and the established TD2 support
comparison, the remaining ordinary angular arguments have
signed sum \(-\delta\). Their positive and negative variations
P,N satisfy
\[
                       N=P+\delta,\qquad
                       0\le P\le h-\delta,\quad N\le h.
\tag{11}
\]
Deleted arguments are inserted only as virtual zeros in the
existing circle blocks. This is the same algebraic enlargement
as in the singleton-block concentration proof; it does not
assert a new configuration or reapply a marker estimate.

Write full shifted-circle support as
\[
                  \overline S(f,g)=R\sqrt{f^2+g^2}-\frac{f+g}{2}.
\]
We use the weaker full support at D throughout the new large-total
estimates. The resulting baseline is
\[
\begin{split}
 B(z)={}&k+2l+m+cW(z)+2-c\sigma\sin z\\
 &-\overline S(1,k)-\overline S(l,k)
        -\overline S(l,m)-\overline S(1,c).
\end{split}
\tag{12}
\]
The ordinary pairs are
\[
 H:(k,1),\qquad G:(k,l),\qquad
 B:(\min(l,m),\max(l,m)).
\tag{13}
\]
For an ordered pair \(p\le q\), put
\[
 V_{p,q}(t)=q(\cos t-1)
   -R\{\sqrt{p^2+q^2-2pq\sin t}-\sqrt{p^2+q^2}\}.
\tag{14}
\]

The three-block concentration and balanced-envelope lemmas in
[the split theorem](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_SPLIT_CONCAVITY.md)
apply at total \(\delta\), rather than \(\theta\), provided
\[
 \frac23\le k\le\frac{17}{20},\quad
 k\le c\le2,\quad k\le l\le\frac32k,\quad
 \frac9{10}\le\frac cl\le\frac{11}{10},
\]
\[
 \frac{p_i}{q_i}\ge\frac23,
       \qquad\frac{q_{\max}}{q_{\min}}\le\frac65.
\tag{15}
\]
They remove every same-block or separated saturation alternative
on the whole variation domain (11). Thus feasibility would force
\[
             B(z)+lj(a)+j(e)+\min_{i=H,G,B}V_i(\delta)\le0.
\tag{16}
\]
The proof of this reduction uses \(q_H=1\), and hence
\(q_{\max}\ge1\); it does not assume \(q_{\min}\ge1\).

For fixed \(\theta,e,k,l,c\), every alternative in (16) is
concave in the A/TD split \(a+z=\theta\). Indeed its B-dependent
part is either
\[
 H_0(m)=\tfrac32m-R\sqrt{l^2+m^2}
\]
or
\[
 H_\delta(m)=\tfrac32m+\max(l,m)(\cos\delta-1)
                   -R\sqrt{l^2+m^2-2lm\sin\delta}.
\tag{17}
\]
The cited proof makes both functions concave and increasing for
\(m/l\le23/20\), uniformly for every \(0\le\delta\le h\).
Its remaining second derivative is at most
\[
       c\{-\tfrac12\cos z+.916\sin z\}
          +l\{-\tfrac12\cos a+.92\sin a\}<0,
\tag{18}
\]
using a+z≤h and (15). The extra j(e) is constant in this split.
Consequently it suffices to prove the six alternatives at
\[
             (a,z)=(\theta,0)\quad\hbox{or}\quad(0,\theta).
\tag{19}
\]
We call these the A and T endpoints respectively. The index
H,G,B records the single ordinary block retaining the negative
total \(\delta\); it is not a partition of states or angles.

## 4. Small total and the two new weight domains

If \(\delta\le L\), choose the existing low weights at total
\(\delta\) from Section 2 of
[the complete two-positive-error theorem](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_COMPLETE_SCALAR_EXCLUSION.md).
They have l>1. By (5) and j(e)≤0,
\[
                    lj(a)+j(e)\ge l\{j(a)+j(e)\}
                                      \ge lj(a+e).
\tag{20}
\]
The actual z and the virtual A total a+e sum to \(\delta\).
The already certified low split theorem therefore gives the
contradiction. For this inherited low estimate retain its exact
sorted D support, rather than weakening it to full support.

It remains to treat \(\delta\ge L\). There are two explicit
continuous families.

### 4.1 The triangle with \(\theta\ge L\)

Put \(t=\theta-L\), so
\[
                   t\ge0,\quad e\ge0,\quad t+e\le d.
\tag{21}
\]
Choose
\[
\begin{split}
 k&=.6692+.5218t-.5956t^2+.4216t^3+.28e,\\
 l&=1+.0175t-1.0932t^2+1.278t^3+.25e,\\
 c&=1.0163-.0209t-1.1486t^2+1.4069t^3+.25e.
\end{split}
\tag{22}
\]
All decimals here and below are exact rationals. Their whole-domain
bounds are
\[
 .6692\le k<.849,\qquad .88<l<1.134,
       \qquad .878<c<1.15,
\]
\[
 k<l<\tfrac32k,\quad k<c,
       \qquad .9l<c<1.1l.
\tag{23}
\]
Here are exact ways to check the bounds without locating extrema
numerically. Since the weights are affine in e, their extrema
reduce to e=0 and e=d−t. The upper k polynomial on that second
edge, centered at t=.3, has negative quadratic coefficient after
the cubic remainder is bounded on |t−.3|≤.3; its retained
curvature is \(1121/12500\). Completing the square gives k<.849.
The upper l and c edge derivatives are convex quadratics and
negative at both endpoints, so their maxima are their left
endpoints. The one-variable coefficient lower bounds for l and c
are respectively .880138 and .878532.

For the four remaining differences, the whole-triangle coefficient
lower bounds defined in Section 7 give
\[
 l-k>.015,\quad c-k>.007,\quad c-.9l>.08,
                                      \quad1.1l-c>.078.
\tag{24}
\]
Also
\[
 \tfrac32k-l=.0038+.7652t+.1998t^2-.6456t^3+.17e>0,
\]
since \(.7652-.6456d^2>0\).

For every split 0≤z≤θ, the function cos z+η sin z has its
minimum at one of the two endpoints. Its maximum is at most
\(\sqrt{1+\eta^2}\). Thus
\[
 \frac23<\frac ml<\frac{23}{20},\qquad m\ge k.
\tag{25}
\]
For the lower bound on m/k, define
\[
 m_-(\theta)=c\{C_{10}(\theta)+\eta S_{11}(\theta)\}.
\]
The two edge polynomials m_-−k decrease in t: their derivative
coefficient upper bounds are below −.37. Their shared right
endpoint exceeds .0084. Together with c>k this proves m≥k.
For the ratio bounds in (25), it is enough to use
\(.9\cos h>.9(.7648)>2/3\) and
\(1.1\sqrt{1+\eta^2}<23/20\).

The largest q-coefficient is at most max(1,l,m), and the smallest
is min(1,l). If l≤1, (25) and l>.88 give their ratio below 6/5.
If l≥1, use
\[
 m\le1.15\sqrt{1+\eta^2}<1.2,
 \qquad 1.2^2-1.15^2(1+\eta^2)=.0039646975>0.
\tag{26}
\]
This verifies all hypotheses (15).

We will use one common upper B coefficient,
\[
                        q_*=l+.15(d-t).
\tag{27}
\]
It dominates l, the A-endpoint coefficient c, and the T-endpoint
coefficient m(θ). For c, the exact difference is
\[
 q_*-c=.0637-.1116t+.0554t^2-.1289t^3.
\]
Its derivative is at most
\(-.1116+.1108d=-1969/37500<0\), and its value at t=d is
\(12947/33750000>0\). Thus q_*>c on the entire triangle.
For m(θ), put
\(m_+=c(C_{12}(\theta)+\eta S_9(\theta))\).
The difference q_*−m_+ is affine in e. At e=0 and e=d−t,
its centered quadratic lower bounds at t=.2, with the entire
higher-degree tail absorbed into the quadratic coefficient,
give respectively lower bounds .00478 and .00160 after one
completed square. Thus q_*≥max(l,m(θ)) throughout (21).

### 4.2 The rectangle with \(\theta\le L\le\delta\)

Put
\[
                 x=L-\theta\in[0,L],\qquad
                 y=\delta-L\in[0,d],\qquad e=x+y.
\tag{28}
\]
Choose the linear family
\[
 k=.6692+.18x+.28y,\qquad
 l=1+.25(x+y),\qquad c=1.0163+.25(x+y).
\tag{29}
\]
In particular 2/3<k<.85, 1≤l<1.2, k<c<1.2, and
\[
       l-k=.3308+.07x-.03y>0,
       \qquad\tfrac32k-l=.0038+.02x+.17y>0.
\tag{30}
\]
Here c/l lies between 1 and 1.0163. Since z≤θ≤L,
\(c\le m(z)\le c(\cos\theta+\eta\sin\theta)\), so the B
pair is already ordered as (l,m). Its ratio exceeds 2/3.
For its largest coefficient one can set y=d and use the
one-variable polynomial
\[
 (1.1913-.25\theta)\{C_{12}(\theta)+\eta S_9(\theta)\},
                         \qquad0\le\theta\le L.
\tag{31}
\]
Its coefficient upper bound is less than 1.196. Hence
q_min=1 and q_max<1.196<6/5. This verifies (15) also on the
whole rectangle (28).

## 5. Polynomial lower charges and exact norm numerators

Use the positive rational upper bounds
\[
 \overline R=1.978787508,
 \quad\overline a=1.414575672,
 \quad\overline\sigma=1.415477291.
\tag{32}
\]
Their required square comparisons are
\[
 \overline R^2>Q,\qquad
 (\overline a+\tfrac12)^2>Q-\tfrac14,\qquad
 (\overline\sigma+\tfrac{1+\eta}{2})^2>Q(1+\eta^2).
\]
For any angle u put
\[
                   J(u)=\frac{C_{10}(u)-1}{2}
                                +(\tfrac12-\overline a)S_9(u).
\tag{33}
\]
For the triangle family use
\[
                 j_\theta^-=J(\theta)-.086t^4,
                    \qquad j_e^-=J(e)-.002e^4.
\tag{34}
\]
The first is the published quartic lower support envelope.
For the second, e≤d. Above the actual support transition,
the loss from the axis formula is at most
\[
                        \frac{Re(e-\frac12)^2}{8}.
\]
The ratio \((e-1/2)^2/e^3\) increases on [1/2,h]. At e=d,
\[
                 .002-\frac{\overline R(d-\frac12)^2}{8d^3}
                                      >.000188>0.
\tag{35}
\]
Below the transition the subtracted term is harmless.

For the rectangle family use
\[
                          j_\theta^-=J(\theta),
                       \qquad j_e^-=J(e)-.029e^4.
\tag{36}
\]
Now θ≤L is entirely on the axis branch. The same loss estimate
for e≤h is paid by
\[
                 .029-\frac{\overline R(h-\frac12)^2}{8h^3}
                           =\frac{2653123}{17150000000}>0.
\tag{37}
\]

The following formulas define all twelve polynomials explicitly.
Set
\[
 s=S_{11}(\delta),\qquad v=C_{10}(\delta)-1.
\tag{38}
\]
For the A endpoint let \(M=c\), and for the T endpoint let
\[
                         M=c\{C_{12}(\theta)+\eta S_9(\theta)\}.
\tag{39}
\]
Define the polynomial nonradical parts
\[
\begin{split}
 A_A&=2k+3l+3c+3+l j_\theta^-+j_e^-,\\
 A_T&=2k+3l+3+
 c\{1+2C_{10}(\theta)
             +(\tfrac32\eta+\tfrac12-\overline\sigma)S_9(\theta)\}
                 +j_e^-.
\end{split}
\tag{40}
\]
The coefficient of S_9 in the second line is negative, as required
for a lower bound. Start with the four polynomials
\[
        P_H=1+k^2,\quad P_G=k^2+l^2,\quad
        P_B=l^2+M^2,\quad P_D=1+c^2.
\tag{41}
\]
For scalar index H,G,B respectively, replace just that polynomial by
\[
                P_H-2ks,\qquad P_G-2kls,
                                      \qquad P_B-2lMs.
\tag{42}
\]
Also add to A_X respectively
\[
                         v,\qquad lv,\qquad q_Xv,
\tag{43}
\]
where q_X=q_* for the triangle and q_X=M for the rectangle.
Thus the last coefficient is an upper bound for max(l,m) at
the relevant endpoint. Since v≤0, its use is in the lower-bound
direction.

The four P polynomials bound the actual squared norm forces from
above. This is immediate for H,G,D. For B, both at zero angle
and at the retained negative angle, the squared norm increases
with its second coefficient: m/l>2/3>sin δ. Thus replacing m
by M≥m in (39), then sin δ by the lower S_11, is legitimate.
There is no separate collection of the E circle: it has already
been used once, in j(e).

We now specify four positive polynomial masses. In either domain
let \([P]_{\le3}\) mean terms of total degree at most three in
the native variables (t,e) or (x,y), let P_0=P(0,0), and put
\[
 w=\frac{[P]_{\le3}-P_0}{P_0},\qquad
 r=\rho\left[1+\frac w2-\frac{w^2}{8}+\frac{w^3}{16}\right]_{\le3}.
\tag{44}
\]
The constants ρ are exact rationals given by the following rule.
For the ordinary H and G norms use 1.203257512; for D use
1.425785990. For the ordinary B norm use 1.425785990 at the
A endpoint and 1.451171531 at the T endpoint. At the one replaced
norm in (42), use 1.107155480 for H or G, 1.302177104 for A/B,
and 1.325511353 for T/B.

No approximation property of (44) is used. The masses are simply
explicit positive polynomials in the elementary inequality
\(\sqrt P\le(P+r^2)/(2r)\). Their whole-domain lower bounds are
\[
             r>.71\quad\hbox{on the triangle},\qquad
             r>.77\quad\hbox{on the rectangle}.
\tag{45}
\]

For the chosen endpoint X and index i, with A including (43),
define
\[
 {\cal N}_{Xi}
 =2A\prod_{j=H,G,B,D}r_j
   -\overline R\sum_{j=H,G,B,D}(P_j+r_j^2)
                                      \prod_{q\ne j}r_q.
\tag{46}
\]
Because every mass is positive, the exact stress alternative in
(16) is at least \({\cal N}_{Xi}/(2\prod r_j)\).
It remains to prove the twelve explicit polynomials (46) positive.

## 6. The complete polynomial positivity certificates

Section 7 defines the coefficient bounds used here, so all numbers
below are exact finite sums determined by (22), (29), and (32)--(46).
The decimals in the comparisons are rational outward bounds.

### 6.1 The whole triangle

For each of the six triangle polynomials write the exact identity
\[
           {\cal N}(t,e)={\cal N}(t,0)+eH(t,e).
\tag{47}
\]
Polynomial division in (47) has no remainder. The whole-triangle
coefficient upper bounds for H_e are

| Index | A endpoint | T endpoint |
| --- | ---: | ---: |
| H | below −.23 | below −.24 |
| G | below −.43 | below −.42 |
| B | below −.25 | below −.13 |

Thus H decreases as e increases at fixed t, and
\[
                              H(t,e)\ge H(t,d-t).
\tag{48}
\]
For the far-edge polynomials the one-variable lower coefficient
bounds give
\[
 H_{AH}(t,d-t)>.065,\quad H_{AG}(t,d-t)>.143,
\]
\[
 H_{TH}(t,d-t)>.062,\quad H_{TG}(t,d-t)>.150.
\tag{49}
\]
The derivative upper coefficient bounds for H_AB(t,d−t) and
H_TB(t,d−t) are respectively below −.8 and −1.6. Their right
endpoint values are greater than .213 and .086. Hence all six
far-edge polynomials are strictly positive.

For the base edge \(n(t)={\cal N}(t,0)\), the following complete
one-variable certificates suffice:

| Polynomial | Exact form used | Whole-interval coefficient bound |
| --- | --- | --- |
| n_AH | n(0)+t q(t) | n(0)>.001727; q>.054 |
| n_AG | direct lower bound | n>.00168 |
| n_AB | endpoint chord + t(d−t)q(t) | both endpoints>.0968; q>.21 |
| n_TH | n(0)+t q(t) | n(0)>.001786; q>.057 |
| n_TG | endpoint chord + t(d−t)q(t) | both endpoints>.001786; q>−.00657 |
| n_TB | endpoint chord + t(d−t)q(t) | both endpoints>.0266; q>1.25 |

The only negative chord bound still gives
\[
                     n_{TG}>.001786-.00657\frac{d^2}{4}>.001.
\tag{50}
\]
Thus every base polynomial exceeds .001. Equations (47)--(50)
prove positivity on the entire closed triangle (21).

### 6.2 The whole rectangle

For each rectangle polynomial use
\[
                   {\cal N}(x,y)={\cal N}(0,y)+xH(x,y).
\tag{51}
\]
The whole-rectangle lower coefficient bounds are

| Index | A endpoint H | T endpoint H |
| --- | ---: | ---: |
| H | greater than .052 | greater than .046 |
| G | greater than .144 | greater than .137 |
| B | greater than .446 | greater than .259 |

The base n(y)=N(0,y) for A/H has direct one-variable coefficient
lower bound .00125. Every other base has
\(n(y)=n(0)+yq(y)\), with n(0)>.0017 and the following
coefficient lower bounds for q:
\[
 q_{AG}>.100,\quad q_{AB}>1.98,\quad
 q_{TH}>.00029,\quad q_{TG}>.106,\quad q_{TB}>2.10.
\tag{52}
\]
They prove all six bases positive, and hence every polynomial
(51) positive on the full rectangle (28).

## 7. Explicit finite coefficient formulas

This section makes the polynomial certificates reproducible
without a hidden enclosure program. Let T_j be the Chebyshev
polynomial, characterized by \(T_j(\cos u)=\cos(ju)\), so
\(|T_j|\le1\) on [−1,1]. Put
\[
 A_{n0}=4^{-n}\binom{2n}{n},\qquad
 A_{nj}=2\,4^{-n}\binom{2n}{n-j}\quad(1\le j\le n),
\tag{53}
\]
and set A_nj=0 otherwise. Then
\[
              u^n=\sum_j A_{nj}T_j(2u-1),\qquad0\le u\le1.
\]
For a one-variable polynomial \(P(t)=\sum p_nt^n\) on [0,D],
its coefficients are \(b_j=\sum_n p_nD^nA_{nj}\).
Consequently
\[
                     b_0-\sum_{j\ge1}|b_j|\le P
                              \le b_0+\sum_{j\ge1}|b_j|.
\tag{54}
\]

For \(P(x,y)=\sum p_{ij}x^iy^j\) on [0,L]×[0,d], use
\[
                  b_{kl}=\sum_{ij}p_{ij}L^id^jA_{ik}A_{jl}.
\tag{55}
\]
For the triangle, substitute
\(t=du(1-v),\ e=duv\), with 0≤u,v≤1. This covers the
whole triangle. The coefficients become
\[
 b_{kl}=\sum_{ij}p_{ij}d^{i+j}A_{i+j,k}
                 \sum_{q=0}^{i}(-1)^q\binom iq A_{j+q,l}.
\tag{56}
\]
In either (55) or (56), the whole-domain lower and upper bounds are
\[
                    b_{00}\mp\sum_{(k,l)\ne(0,0)}|b_{kl}|.
\tag{57}
\]
Equations (53)--(57) are ordinary monomial-to-Chebyshev identities
and the inequality |T_j|≤1. They are applied once to each whole
domain, with no subdivision.

For the two completed squares in Section 4.1, write
\(P(.2+u)=\sum a_ju^j\), let \(r=1/3\), and put
\[
                  q=a_2-\sum_{j\ge3}|a_j|r^{j-2}.
\tag{58}
\]
The interval 0≤t≤d lies within |u|≤r. In both uses q>0,
and \(P\ge a_0+a_1u+qu^2\ge a_0-a_1^2/(4q)\), giving
the bounds printed after (27).

For a chord certificate, the polynomial is defined exactly by
\[
 q(t)=\frac{P(t)-P(0)-\{P(d)-P(0)\}t/d}{t(d-t)}.
\tag{59}
\]
The numerator vanishes at both endpoints, so (59) is a polynomial;
its coefficient bound is again (54). Quotients by t, e, or x
in the preceding certificates likewise mean exact polynomial
division after subtracting the indicated endpoint or edge.

For reference, the triangle total degrees in the order AH,AG,AB,
TH,TG,TB are 25,26,26,39,39,39; the rectangle degrees are
23,23,23,35,35,35. Equations (22), (29), and (32)--(59), together
with the rational ρ constants, determine every coefficient and
every comparison in this proof.

## 8. Joining the TD2 result and arbitrary TD0

For TD2 with z≥0, the small total is closed by (20). At larger
total, (15)--(19) leave the six intrinsic endpoints. Sections
5--7 prove all of them strictly positive on both complete
weight domains. This contradicts (16).

For TD0, its weight equals the BT2 weight c, so the actual signed
T coordinate cancels exactly. Put θ=a and δ=a+e. The force sum
has four ordinary full-circle blocks
\[
              (k,1),\quad(k,l),\quad(l,c),\quad(1,c).
\tag{60}
\]
Its baseline is exactly the A endpoint of (12), and its extra
charge is lj(a)+j(e). The E deletions leave the same variation
domain (11), with all actual TD0 error retained in the fourth
ordinary block.

For δ≤L, use the already proved small-A TD0 charged stress with
\((k,l,c)=(.78,1.26,1.8)\). Equation (20) holds because l>1.
The original proof of its scalar bound uses only the retained
ordinary signed sum −δ and the same two variation bounds.
It gives the positive lower bound for the virtual A charge
lj(δ), including the endpoint reserve 49/15000. Thus it applies
after the E charge comparison as well.

For δ≥L, use (22) or (29) at θ=a. In both families c≥k and
\(2/3<c<6/5\). Adding the pair (1,c) preserves every balanced
range (15): its large coefficient lies between 1 and the largest
of the already present coefficients. The four-block concentration
in Section 4 of
[the TD0 theorem](HAND_G3_POSITIVE_INTERMEDIATE_TD0_FOUR_CIRCLE_EXCLUSION.md)
therefore leaves only \(\min_{H,G,B,D}V_i(\delta)\).

The same note proves, uniformly on [0,h],
\[
                         V_{\min(1,c),\max(1,c)}\ge V_{k,1}
                          \quad(k\le c<6/5,\ k\le1).
\tag{61}
\]
For c≤1 this is its monotonicity in the smaller coefficient.
For c≥1 it is its additional larger-coefficient monotonicity on
\(1\le c\le6/5\), followed by the smaller-coefficient comparison.
Thus the D negative alternative is redundant. The three remaining
alternatives are precisely the already positive A endpoint
polynomials in Sections 5--7. This closes arbitrary TD0.

All original inequalities have only been added with positive
weights. Signed A/E comparisons delete angular arguments inside
that sum and account for their actual circles once. The proof
does not move a center, alter an original witness, assume an
unproved frame order, or use a sampled numerical bound, a state
mesh, a Bernstein inventory, Lean compilation, or CI.
