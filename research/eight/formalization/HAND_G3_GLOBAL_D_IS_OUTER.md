# Global outer rigidity of D

## 1. Statement and the original two-edge charge

Work on the actual G0--G2 boundary seven-cycle at
\[
 Q=\frac{9789}{2500},\qquad y_E=-b_E\le0.
\]
Retain its original witnesses. The global DE theorem gives
\(y_D=-b_D<0\) and every DE owner in \(\{2,3\}\). Then
\[
                         \boxed{D\text{ is outer}.}             \tag{1}
\]
No GA or EH restriction, sign of T, radial kind of E, frame order,
or additional mismatch bound is assumed.

Put
\[
 v=d_{TD},\qquad d=d_{DE},\qquad
 W(t)=\frac{1+\cos t+|\sin t|}{2},
\]
and use the unchanged common signed G1 marker. Thus
\(\ell_E=-F_E\), while \(\ell_T=\operatorname{sign}(y_T)F_T\).
The charge of the two actual edges is
\[
                 C=\frac\pi2+v+d+\ell_T+F_E.                    \tag{2}
\]
We prove that a core D would give \(C>2\). The five complementary
G1 edges have total charge greater than \(5\Gamma\), where
\(\Gamma=8833/10000\): their nonnegative error gains can be
discarded. Since the two charges sum to \(2\pi\), this contradicts
\[
 2+5\Gamma-\frac{710}{113}=\frac{30129}{226000}>0,
 \qquad 2\pi<\frac{710}{113}.                                   \tag{3}
\]

The original TD owners are 0 and 2. Write \(y_T=\sigma b_T\).
The four projections used below are exactly
\[
\begin{aligned}
 P_{TD,0}&=\sigma b_T+a_D\sin v+b_D\cos v,\\
 P_{TD,2}&=a_T\sin v+\sigma b_T\cos v+b_D,\\
 P_{DE,2}&=a_D\cos d+b_D\sin d+b_E,\\
 P_{DE,3}&=a_D+a_E\sin d+b_E\cos d.
\end{aligned}                                                    \tag{4}
\]
Each retained projection is at least its own W. In particular the
proof includes weak contacts and ties between original witnesses.

## 2. Whole-domain estimates

Set
\[
 L=\frac{447}{800},\quad a_0=\sqrt{Q-\frac14}-\frac12,
 \quad k=\frac{43}{50},\quad m=\frac{111}{100}.
\]
Every actual state has \(L<a\le a_0\), with weak inequalities
sufficient below. The elementary upper bound
\(a_0<283/200\) gives \(a_0-1/2<183/200\).
The [whole-chart marker bounds](HAND_G3_BT_PATH_MARKER_AND_NEGATIVE_AB_COMPARISON.md)
give \(F\ge kb\) on both radial kinds. For an outer state the
[original upper marker plane](HAND_G3_GLOBAL_D_OWNER_BY_CYCLIC_MARKER.md),
Section 2, gives
\[
                  F\le\frac25(a-a_0)+mb.                         \tag{5}
\]

The global variation bound in
[the BT0 path proof](HAND_G3_GLOBAL_BT0_DE2_PATH_EXCLUSION.md),
Section 2, supplies
\[
 |v|,|d|<\frac7{10},\qquad
 \max(0,-v)+\max(0,-d)<\frac7{10}.                               \tag{6}
\]
This bound is a consequence of the full G1 cycle and does not assume
a forbidden BT witness.

For \(0\le t\le7/10\), alternating sine and cosine bounds give
\[
 \sin t<\frac{13}{20},\qquad \cos t>\frac{19}{25},
 \qquad \sec t<\frac{25}{19},\qquad
 \tan t\le\frac{17}{14}t.                                       \tag{7}
\]
For the last bound, tan is convex and vanishes at zero, so it is
enough that \(\tan(7/10)<17/20\). If
\[
 S_5=x-x^3/6+x^5/120,\qquad
 C_6=1-x^2/2+x^4/24-x^6/720,\qquad x=7/10,
\]
the three exact reserves proving (7) are
\[
 \frac{13}{20}-S_5=\frac{69193}{12000000},\quad
 C_6-\frac{19}{25}=\frac{3485351}{720000000},\quad
 \frac{17}{20}C_6-S_5=\frac{84682567}{14400000000}.                 \tag{8}
\]

Consequently every positive-angle cost with coefficient k obeys
\[
 t-k(a_0-\tfrac12)\tan t\ge0,
 \qquad
 1-k\frac{183}{200}\frac{17}{14}
                      =\frac{6227}{140000}>0.                   \tag{9}
\]
With coefficient m the slightly weaker bound suffices:
\[
 t-m(a_0-\tfrac12)\tan t>-\frac{17}{100}.
                                                                    \tag{10}
\]
Indeed replacing \(a_0-1/2\) by \(183/200\) and using (7) leaves a
negative linear coefficient. Its minimum is at \(t=7/10\), and
the reserve above \(-17/100\) is
\[
 \frac{17}{100}+\frac7{10}
       \left(1-m\frac{183}{200}\frac{17}{14}\right)
                              =\frac{2679}{400000}>0.            \tag{11}
\]

For any nonnegative \(z_1,z_2\) with \(z_1+z_2\le7/10\),
\[
            \sum_{j=1}^2(-z_j+k\sin z_j)>-\frac3{20}.            \tag{12}
\]
To see this, \(\sin z_1+\sin z_2\ge\sin(z_1+z_2)\), and
\(-z+k\sin z\) is decreasing. At \(z=7/10\), the lower sine
polynomial \(z-z^3/6\) gives the reserve
\[
 \frac3{20}-\frac7{10}
       +k\left(\frac7{10}-\frac{(7/10)^3}{6}\right)
                            =\frac{851}{300000}>0.               \tag{13}
\]
The one-angle version is included by setting the other argument
to zero. Also, because \(L+1/2>1\),
\[
 -z+k(L+\tfrac12)\tan z\ge-z+k\sin z.                            \tag{14}
\]

## 3. A support inequality on the actual core

Suppose D is core. Its actual boundary has
\(a_D\le7/12\), \(b_D<14/25\). If \(b_D\le1/2\), then
\(a_D=7/12\). If \(b_D\ge1/2\), then
\[
           (a_D-\tfrac12)^2+(b_D-\tfrac12)^2=\frac1{144}.
\]
For any positive U,V this gives
\[
       Ua_D+Vb_D\le\frac{U+V}{2}
                         +\frac1{12}\sqrt{U^2+V^2}.              \tag{15}
\]
On the flat side one may increase b_D to 1/2 and use
\(U\le\sqrt{U^2+V^2}\); on the corner (15) is Cauchy--Schwarz.
Thus (15) does not replace the actual core by its enclosing square.

## 4. Nonnegative T: all four original-owner combinations

First let \(y_T=b_T\ge0\), so \(\ell_T\ge kb_T\). Also
\(F_E\ge kb_E\), regardless of E's radial kind.
For the retained TD inequality choose the multiplier
\[
       \lambda_{TD}=k\quad(TD0),\qquad
       \lambda_{TD}=k\sec v\quad(TD2);
\]
for the retained DE inequality choose
\[
       \lambda_{DE}=k\quad(DE2),\qquad
       \lambda_{DE}=k\sec d\quad(DE3).                           \tag{16}
\]
Subtracting the weighted projections from (2), and adding their
weighted widths, gives a lower bound for C. The endpoint
coefficients of b_T and b_E cancel exactly. The collected force
\((U,V)\) on D is the sum of one vector from each row below:

| Retained edge | Contribution to \((U,V)\) |
|---|---|
| TD0 | \(k(\sin v,\cos v)\) |
| TD2 | \(k\sec v(0,1)\) |
| DE2 | \(k(\cos d,\sin d)\) |
| DE3 | \(k\sec d(1,0)\) |

Both U,V are positive. In the case where both sine contributions
occur, (7) gives \(\cos t-|\sin s|>19/25-13/20>0\);
the cases with a secant contribution are stronger.
Each vector has norm less than \(k(25/19)\), hence
\[
              N:=\sqrt{U^2+V^2}<2k\frac{25}{19}<\frac{12}{5}.
                                                                    \tag{17}
\]

Use (15). The constant left after subtracting \((U+V)/2\)
from the two weighted widths is k. All other contributions
separate into the following one-angle costs, in addition to
the norm loss \(-N/12\):

| Original owner | Error \(t\ge0\) | Error \(-z\le0\) |
|---|---|---|
| TD0 or DE2 | \(t\) | \(-z+k\sin z\) |
| TD2 or DE3 | \(t-k(a_0-1/2)\tan t\) | \(-z+k(L+1/2)\tan z\) |

For example, TD2 leaves
\(k\sec v\,W(v)-(k/2)\sec v- k a_T\tan v\).
When v is positive use \(a_T\le a_0\); when negative use
\(a_T\ge L\). The other entries follow by the same direct
subtraction in (4); they do not impose an E or T circle equality.

By (9), all positive-angle entries are nonnegative. By (6),
(12), and (14), the combined negative-angle entries exceed
\(-3/20\). Finally \(\pi/2>157/100\), so
\[
 C>\frac{157}{100}+k-\frac3{20}-\frac15
                              =\frac{52}{25}>2.                  \tag{18}
\]

## 5. Negative T

Now let \(y_T=-b_T<0\). The global zero-sign theorem excludes
TD0, so the retained owner is TD2. Its projection in (4) is
\(a_T\sin v-b_T\cos v+b_D\). If \(v\le0\), this is at most
\(b_D<14/25<1\), so necessarily \(v>0\).

T must be outer. If T were core, (7) would give
\[
 P_{TD,2}\le\frac7{12}\frac{13}{20}+\frac{14}{25}<1,
 \qquad
 1-\frac7{12}\frac{13}{20}-\frac{14}{25}=\frac{73}{1200}>0,
                                                                    \tag{19}
\]
contrary to \(W(v)\ge1\).

Use (5) at this actual outer T and choose
\[
          \lambda_{TD}=m\sec v,\qquad
          \lambda_{DE}=k\quad(DE2),\quad
          \lambda_{DE}=k\sec d\quad(DE3).                         \tag{20}
\]
Since
\(\ell_T\ge-(2/5)(a_T-a_0)-mb_T\), subtracting the
weighted TD projection cancels b_T and leaves
\[
 -\{\tfrac25+m\tan v\}a_T+\tfrac25 a_0
                              \ge-ma_0\tan v.                    \tag{21}
\]
Here \(v>0\) makes the coefficient have the required sign.

The D force is now \(m\sec v(0,1)\) plus the retained DE
vector from the previous table. Both its coordinates are positive,
and
\[
 N<\frac{25}{19}(m+k)=\frac{197}{76}<\frac{13}{5},
 \qquad \frac{13}{5}-\frac{197}{76}=\frac3{380}>0.                \tag{22}
\]
The width subtraction using (15) leaves the constant
\((m+k)/2\). The TD angle cost is
\(v-m(a_0-1/2)\tan v\), which exceeds \(-17/100\) by (10).
The DE angle cost is the corresponding k-entry of the last table:
it is nonnegative at positive d, and exceeds \(-3/20\) at
negative d. Consequently
\[
 \begin{aligned}
 C&>\frac{157}{100}+\frac{m+k}{2}
               -\frac{17}{100}-\frac3{20}-\frac{13}{60}\\
  &=\frac{1211}{600}>2.
 \end{aligned}                                                    \tag{23}
\]

Equations (18) and (23) cover every T sign and every original
TD/DE witness. They contradict (3), proving (1). All comparisons
were on the original two-edge path, with the original common
marker and true core curve; no frame deformation, chart mesh,
sampled minimum, or compiled theorem is part of this argument.
