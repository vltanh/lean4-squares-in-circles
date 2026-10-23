# The aligned GA/DE endpoint is excluded by one continuous stress

## 1. The complete endpoint branch

Put `Q=9789/2500`. Retain seven original own-frame centers with

\[
 (y_H,y_G,y_A,y_B,y_T,y_D,y_E)
 =(b_H,-b_G,b_A,-b_B,b_T,-b_D,-b_E),\qquad b_i\ge0,
\]

\[
 a_i\ge b_i,\qquad (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q.
\tag{1}
\]

Suppose the three zero-quarter edges are aligned, and the frames are

\[
 \theta_H=\theta_G=\theta_A=\theta_B=0,\qquad
 \theta_T=\theta_D=\theta_E=-\alpha,
 \qquad 0\le\alpha\le7/10.
\tag{2}
\]

Retain an original transverse witness on each of HG, AB and TD,
GA axis 0, BT axis 2, DE axis 3, and EH axis 1. These are the
original zero-based axis numbers, including possible ties.

**Theorem.** No such edge system exists at (1).

Equivalently, the proof excludes the following five-anchor system
without requiring G and T to be present as separate centers:

\[
\begin{gathered}
 b_H+a_A\ge2,\qquad b_A+b_B\ge1,\\
 c a_B-s b_B+b_D\ge1+W,\qquad a_D+b_E\ge1,\\
 a_H+s a_E-c b_E\ge W.
\end{gathered}
\]

Here the five anchors retain their nonnegative sorted coordinates and
the circle bounds (1), and `c=cos(alpha)`, `s=sin(alpha)`,
`W=(1+c+s)/2`. The total-span cap argument used below also uses only
these five inequalities. This form permits composition with a proved
necessary reduction in which the G/T coordinates have already canceled.

This is the `t=0,delta=0` endpoint of the aligned-zero hard-quarter
class. It allows every nonnegative E transverse coordinate and arbitrary
radial slack. It is used after explicit reductions to this branch;
the frame order, signs, aligned zero edges and original owners in
(1)--(2) are hypotheses, not global conclusions.

The total-span argument in Section 2 of
`HAND_G4_E_INTERIOR_BOUNDARY_REDUCTION.md` applies directly to these
same seven vertices and yields

\[
                         0\le\alpha<11/50.
\tag{3}
\]

That argument uses only the A/B circle caps, the three original zero
edges, GA0 and BT2. It does not require E contact, E zero, an E
deformation, or a bound on the mismatch.

Write `s=sin(alpha)`, `c=cos(alpha)` and `W=(1+c+s)/2`. Thus
`0<=s<11/50`. Every terminating decimal below is an exact rational.

## 2. Collect all shared centers before taking circle supports

Use weights, in HG--GA--AB--BT--TD--DE--EH order,

\[
                  (1,1,a,\beta,\beta,\delta,\epsilon).
\tag{4}
\]

Here the weight a is distinct from the primary coordinates `a_i`.
The seven retained projections in (2) are

\[
\begin{gathered}
 b_H+b_G,\qquad a_A-b_G,\qquad b_A+b_B,\\
 c a_B-s b_B-b_T,\qquad b_T+b_D,\qquad a_D+b_E,\\
 a_H+s a_E-c b_E.
\end{gathered}
\]

The unchanged G and T coordinates therefore cancel exactly. The
five remaining own-frame forces are

\[
\begin{array}{c|cc}
 A&1&a\\
 B&\beta c&a-\beta s\\
 D&\delta&\beta\\
 H&\epsilon&1\\
 E&\epsilon s&\delta-\epsilon c.
\end{array}
\tag{5}
\]

The weighted width demand is

\[
               2+a+\beta+\delta+(\beta+\epsilon)W.
\tag{6}
\]

In particular both HG and GA contribute one to the constant term
in (6). No incident edge has used a different copy of its shared
center.

For arbitrary real X,Y and positive m, (1) gives

\[
 Xa_i+Yb_i\le
 T(X,Y;m):=mQ+\frac{X^2+Y^2}{4m}-\frac{X+Y}{2}.
\tag{7}
\]

Choose positive masses `m_A,m_B,m_D,m_H,m_E`. The necessary
demand-minus-support scalar is

\[
 N=2+a+\beta+\delta+(\beta+\epsilon)W
        -\sum_{i=A,B,D,H,E}T(X_i,Y_i;m_i)\le0.
\tag{8}
\]

This is a necessary consequence of the original signed witnesses and
the five circle inequalities. The support bound permits every force
sign; it neither moves a center nor asserts contact in (1).

## 3. One explicit family on the full angle interval

For `0<s<=11/50`, use the polynomial edge weights

\[
\begin{aligned}
 a&=24/41+.6s+.1s^2+.2s^3,\\
 \beta&=1+.33s-.135s^2+.36s^3,\\
 \delta&=36/31-.49s-.05s^2+.09s^3,\\
 \epsilon&=36/31-.795s+.415s^2-.2175s^3,
\end{aligned}
\tag{9}
\]

and polynomial circle masses

\[
\begin{aligned}
 m_A&=12/41+.076s+.041s^2,\\
 m_B&=12/41+.02s-.134s^2+.038s^3,\\
 m_D&=12/31-.04s-.007s^2+.082s^3,\\
 m_H&=12/31-.152s+.101s^2-.053s^3,\\
 m_E&=s(.304-.188s+.11s^2-.044s^3).
\end{aligned}
\tag{10}
\]

All these quantities are positive on this whole interval. For
example, discarding positive terms and putting `s<=.22` in the
negative terms gives

\[
 m_A>.29,\quad m_B>.286,\quad m_D>.377,
 \quad m_H>.353,\quad m_E>.262s.
\]

The same comparisons give `a>0`, `beta>.99`, `delta>1.05`, and
`epsilon>.98`. Hence every use of (7)--(8) and every denominator
below has its required sign.

## 4. Reduce the scalar to one polynomial

Reducing `c^2+s^2=1` in (5), the complete expression (8) is

\[
\begin{split}
 N={}&3+2a+2\beta+2\delta+\epsilon+\beta c+\epsilon s
                          -Q\sum_i m_i\\
 &-\frac{1+a^2}{4m_A}
  -\frac{\beta^2+a^2-2a\beta s}{4m_B}
  -\frac{\delta^2+\beta^2}{4m_D}
  -\frac{\epsilon^2+1}{4m_H}
  -\frac{\delta^2+\epsilon^2-2\delta\epsilon c}{4m_E}.
\end{split}
\tag{11}
\]

Let

\[
 D_*(s)=4m_A m_B m_D m_H m_E>0,
 \qquad D_*N=A(s)+B(s)c.
\tag{12}
\]

Equations (9)--(11) define the two rational polynomials A,B
explicitly, without any numerical interpolation. In particular

\[
 B=D_*\beta+2\delta\epsilon m_A m_B m_D m_H>0.
\tag{13}
\]

For `0<=s<=.22`, the elementary lower bound

\[
                 c\ge C_4(s):=1-s^2/2-.13s^4
\tag{14}
\]

holds. The right side is positive. To check (14), put `v=s^2`;
its square minus `1-v` is

\[
          v^2(-.01+.13v+.0169v^2)\le0,
\]

because `v<=.0484` makes the bracket negative. Both sides of
the square-root comparison have the required positive sign.

Define the single rational polynomial

\[
               P(s)=A(s)+B(s)C_4(s).
\tag{15}
\]

The constant coefficient of P is zero, as follows either by
expanding (11) or by `m_E(0)=0` and `delta(0)=epsilon(0)`.
Write `P(s)=s L(s)`. The following coefficient comparisons from
(9)--(15) give a short whole-interval positivity proof.

If `L(s)=sum_j l_j s^j`, its first coefficients satisfy

\[
\begin{gathered}
 l_0>.00005947,\qquad l_1>-.0010203,
 \qquad l_2>.005211,\qquad l_3>-.004386,\\
 l_4>0,\qquad l_5>0,\qquad l_6>-.002163,
 \qquad \sum_{j>6}(-l_j)_+<.00337.
\end{gathered}
\tag{16}
\]

Moreover `l_7>0`: all negative terms in the last sum have
degree at least eight. These are coefficient comparisons for
the one polynomial (15). They can be reproduced by substituting
the printed weights into (11), multiplying by the printed product
(12), and collecting powers; they are not values at sample angles.

For additional reproducibility, the coefficients through degree six,
rounded outwards in the directions used in (16), are

\[
\begin{split}
 L(s)>{}&.0000594777-.0010201985s+.0052111004s^2
       -.0043859674s^3\phantom{{}+{}}\\
       &+.0037187139s^4+.0013213946s^5-.0021628560s^6
       +\sum_{j>6}l_js^j.
\end{split}
\]

The higher negative coefficients in (16) have total magnitude
less than `.003366206`, hence less than `.00337`. Keeping their
degree at least eight is what permits the following shared bound.
Put `R=11/50`. For `0<=s<=R`, the whole negative remainder
after the cubic is at least

\[
 -(.002163 R^3+.00337 R^5)s^3>-.000025s^3,
\tag{17}
\]

where the exact comparison is

\[
 .002163 R^3+.00337 R^5
       =\frac{774012437}{31250000000000}<\frac1{40000}.
\]

Discarding the nonnegative terms of degree four and higher now
gives the simple cubic bound

\[
 L(s)\ge p(s):=.00005947-.0010203s+.005211s^2-.004411s^3.
\tag{18}
\]

## 5. One curvature bound and one completed square

On `0<=s<=11/50`, direct differentiation gives

\[
 p''(s)=.010422-.026466s
       \ge\frac{114987}{25000000}>\frac9{2000}.
\tag{19}
\]

At the one rational comparison point `s0=11/100`,

\[
 p(s_0)=\frac{4419059}{10^{12}}>\frac{44}{10^7},
 \qquad
 p'(s_0)=-\frac{339993}{10^{10}},
 \qquad |p'(s_0)|<\frac{35}{10^6}.
\tag{20}
\]

Integrate (19), and complete the resulting quadratic about `s0`.
Throughout the entire interval,

\[
\begin{split}
 p(s)&\ge p(s_0)+p'(s_0)(s-s_0)+\frac9{4000}(s-s_0)^2\\
 &>\frac{44}{10^7}
       -\frac{(35/10^6)^2}{2(9/2000)}
   =\frac{307}{72000000}>0.
\end{split}
\tag{21}
\]

For every positive s, (12)--(15), (18) and (21) prove

\[
 D_*N\ge P(s)=sL(s)>0,
\]

contradicting (8).

At `s=0`, omit E from the stress: its force and mass both vanish.
The other four positive masses in (10) and the weights in (9)
give directly

\[
                      N(0)=\frac{3027}{794375}>0.
\tag{22}
\]

Thus the endpoint `alpha=0` is excluded as well. This proves
the theorem on the complete branch (1)--(2).

The proof uses a single continuous stress, one rational polynomial,
and one whole-interval curvature comparison. It invokes no angle
mesh, interval-state cover, numerical optimizer result, generated
row certificate, Lean compilation, or CI result. It does not
establish that an unrestricted candidate reaches this branch.
