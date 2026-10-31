# Every strict radial return owner has actual channel height below seven tenths

Date: October 26, 2026.

**Status: complete analytic local theorem, accepted after root and separate full-source reviews in REVIEW_C6_RADIAL_ADJACENT_RETURN_OWNER_ROOT_2026_10_26.md and REVIEW_C6_RADIAL_ADJACENT_RETURN_OWNER_BLOCK_2026_10_26.md.** This strengthens the earlier \(H<4/5\) bound over the same whole actual return-owner domain. It makes no claim about a different feature or a lower-turn placement.

Retain the original one-radial all-side C6, its full radius window
\[
 K:=79/40\le R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-1/4}-1,\qquad r_0^2=d^2+1/4,
\tag{1}
\]
all actual squares, original forces and circle weights, actual shared means and endpoints, and all transmitter sliders.

Consider one physically unique endpoint which genuinely owns the normal of the actual return channel, whose S-incident application is its opposite circle-corner vertex, and whose original turn is strictly greater than \(\pi/2\). Use the actual T chart in SIX_CYCLE_ONE_RADIAL_SINGLE_SHARED_OPPOSITE_RETURN_EXCLUSION.md, Section 1. Its local derivation does not require a particular feature at the partner endpoint.

In the reflected inward own axes, write
\[
 a>b>1/2,\qquad a^2+b^2=R^2,\qquad
 t=1-H/b\in[0,1),
\]
\[
 X=1-ta>0,\quad Y=1-tb=1-b+H\in(0,1],\quad
 L=\sqrt{X^2+Y^2},\quad x=X/L,\quad y=Y/L.
\tag{2}
\]
The genuine original return mean has exactly the coordinate \(Y\); it is not varied independently. Properness and the actual moment give the signs in (2). Put \(r=1/\sqrt2\). Since \(a>b\),
\[
                 0<x\le r\le y<1,\qquad x^2+y^2=1.
\tag{3}
\]
The original reserve-one S-incident channel gives the actual radial port in these own axes as
\[
               P=(a-1-x,b-1-y),\qquad |P|^2=r_0^2.
\tag{4}
\]

**Theorem.** Every such actual endpoint satisfies
\[
                              \boxed{H<7/10.}
\tag{5}
\]

## 1. A whole-domain normal bound under the contrary height premise

Suppose \(H\ge h:=7/10\). Since \(H\le b\), we have \(b\ge h\). Also
\[
 b<R/\sqrt2<3/2,\qquad a^2\le1105/256-h^2<4,
\]
so \(a<2\).

For a scalar comparison only, define
\[
 X_0=1-a+ah/b,\qquad Y_0=1-b+h.
\tag{6}
\]
The original mean and configuration are unchanged. At fixed a,b,
\[
 \frac{\partial}{\partial H}\left(\frac{1-a+aH/b}{1-b+H}\right)
       =\frac{a/b-1}{(1-b+H)^2}>0.
\tag{7}
\]
Once \(X_0,Y_0>0\) are proved, this gives \(x\ge x_0\), \(y\le y_0\), where \(x_0=X_0/\sqrt{X_0^2+Y_0^2}\) and similarly for \(y_0\).

The exact Cauchy bound
\[
                  a+\frac7{10}b<\frac{203}{80}
\tag{8}
\]
follows from
\[
 (203/80)^2-\frac{1105}{256}\left(1+(7/10)^2\right)
                         =\frac{191}{25600}>0.
\]
Since \(b-h\ge0\), substitution of (8) gives
\[
 \begin{split}
 b(X_0-\tfrac7{12}Y_0)
 &\ge\frac{77}{60}b^2-\frac{3623}{1200}b+\frac{1421}{800}>0.
 \end{split}
\tag{9}
\]
The quadratic has positive leading coefficient and
\[
 4\frac{77}{60}\frac{1421}{800}
      -\left(\frac{3623}{1200}\right)^2
                         =\frac{3911}{1440000}>0.
\]
Also \(Y_0=17/10-b>0\). Thus \(X_0>0\), all comparisons in (7) are legitimate, and
\[
                    x\ge x_0>\frac7{\sqrt{193}}>\frac12,
                    \qquad y<\frac{\sqrt3}{2}.
\tag{10}
\]
This proof includes \(H=b\) and the genuine mean endpoint \(Y=1\).

## 2. The case b>=1

Here \(a<11/6\), because
\[
 (11/6)^2-(1105/256-1)=103/2304>0.
\]
On the other hand \(a>R/\sqrt2>139/100\). Together with \(x\le r<5/7\) and (10), these give
\[
                         |a-1-x|<1/3.
\]
Indeed the lower bound is \(-227/700>-1/3\), while the upper is \(11/6-1-1/2=1/3\).

Since \(b<3/2\) and \(y\ge r>7/10\), the second port coordinate is negative. For \(b\ge1\),
\[
                        |b-1-y|\le y<\sqrt3/2.
\]
Consequently
\[
                 |P|^2<1/9+3/4=31/36<53/50<r_0^2,
\tag{11}
\]
where \(d>9/10\). This contradicts (4).

## 3. One analytic normal inequality for the whole case 7/10<=b<=1

Put \(z=1-b\in[0,3/10]\). Equation (8) gives
\[
 bX_0\ge p(z):=\frac{359}{800}+\frac{251}{400}z+\frac7{10}z^2,
\qquad
 bY_0=q(z):=\frac7{10}+\frac3{10}z-z^2.
\tag{12}
\]
Both polynomials are positive on this full interval. Set
\[
                     \lambda(z)=\frac12+\frac35z
                                 =\frac{11}{10}-\frac35b.
\]
It lies in \((0,1)\). The exact expansion
\[
 \begin{split}
 &(1-\lambda^2)p^2-\lambda^2q^2\\
 &=\frac{73043}{2560000}-\frac{609}{6250}z
   +\frac{2041603}{8000000}z^2
   +\frac{313863}{500000}z^3
   +\frac{216311}{4000000}z^4\\
 &\hspace{14mm}-\frac{49713}{50000}z^5-\frac{1341}{2500}z^6
 \end{split}
\tag{13}
\]
has a positive whole-interval lower bound. Bound the two negative higher powers by \(z^2(3/10)^3\) and \(z^2(3/10)^4\), respectively, and discard the positive cubic and quartic. The remaining quadratic coefficient exceeds \(11/50\) by \(802103/200000000\), the constant exceeds \(7/250\) by \(1363/2560000\), and \(1/10-609/6250=8/3125>0\). Thus (13) is strictly greater than
\[
 \frac7{250}-\frac z{10}+\frac{11}{50}z^2
   =\frac{11}{50}\left(z-\frac5{22}\right)^2
                         +\frac{183}{11000}>0.
\tag{14}
\]
The positive-square comparison in (13), then (12), proves
\[
                     x\ge x_0>\frac{11}{10}-\frac35b
\tag{15}
\]
throughout this whole interval. This is one exact polynomial identity and one completed-square bound, with no sampled sign or parameter subdivision.

## 4. Complete radial-port norm comparison when b<=1

Here \(a>17/10\), since
\[
 K^2-1-(17/10)^2=17/1600>0.
\]
Equation (15) gives
\[
 a-1-x<a-\frac{21}{10}+\frac35b.
\]
For fixed R, the function \(\sqrt{R^2-b^2}+(3/5)b\) increases on the entire interval in question: its derivative is \(3/5-b/a>3/5-10/17>0\). Therefore
\[
 a-1-x<\sqrt{R^2-1}-\frac32<R-\frac74.
\tag{16}
\]
The last inequality follows by positive squaring from \(R<17/8\). The lower bound \(a-1-x>-1/70\), and \(R-7/4\ge9/40\), now give
\[
                            |a-1-x|<R-\frac74.
\tag{17}
\]

It remains to bound the other actual coordinate. Let \(\epsilon=b-h\ge0\) and \(\delta=a-b>0\), only in this paragraph. The comparison normals satisfy
\[
 Y_0-X_0=\epsilon\delta/b,\qquad
 y_0-r=\frac{\epsilon\delta}{b}
                   \frac{x_0+y_0}{2L_0(y_0+r)}
             \le\frac{\epsilon\delta}{2bL_0},
\tag{18}
\]
where \(L_0=\sqrt{X_0^2+Y_0^2}\). Here \(x_0+y_0\le\sqrt2\) and \(y_0+r\ge\sqrt2\).

As \(a<2\) and \(b\le1\),
\[
 2bL_0\ge2\sqrt2\,bX_0
        \ge2\sqrt2(7/5-b)>2-b>\delta.
\tag{19}
\]
The middle strict inequality is linear in b and is weakest at \(b=1\), where it follows from \(4\sqrt2/5>1\). Thus \(y_0-r\le\epsilon\), including \(\epsilon=0\). Since \(y\le y_0\), \(b\le1\), and the actual second port coordinate is negative,
\[
                  |b-1-y|=1-b+y\le\frac3{10}+\frac1{\sqrt2}.
\tag{20}
\]

Combining (17),(20),
\[
 |P|^2<
 \left(R-\frac74\right)^2+
                 \left(\frac3{10}+\frac1{\sqrt2}\right)^2
                          <r_0^2.
\tag{21}
\]
For the last strict comparison, its exact difference is
\[
 g(R):=\frac72R-2\sqrt{R^2-\frac14}
                         -\frac{1061}{400}-\frac{3\sqrt2}{10}.
\]
It increases for \(R\ge K>1\), since \(2R/\sqrt{R^2-1/4}<4/\sqrt3<7/2\). At K,
\[
 g(K)=\frac{213}{50}-\frac{\sqrt{5841}}{20}
                               -\frac{3\sqrt2}{10}
       >\frac{213}{50}-\frac{153}{40}-\frac{297}{700}
       =\frac3{280}>0.
\tag{22}
\]
The two radical bounds are \(\sqrt{5841}<153/2\), with squared reserve \(45/4\), and \(\sqrt2<99/70\). This proves (21), again contradicting (4).

Both complete b ranges are impossible under \(H\ge7/10\). The actual height bound (5) follows with every original mean endpoint and slider retained. No equality relabeling, altered radial mask, new computational certificate, Lean compilation or CI occurs.

