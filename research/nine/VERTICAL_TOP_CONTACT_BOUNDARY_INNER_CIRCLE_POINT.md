# A positive top contact forces one fixed inner-circle point into the boundary unit

Date: October 26, 2026.

**Status: complete hand local geometric theorem, awaiting independent
full-source review.** The theorem retains every orientation and allows
one or two physical circle corners. No force or graph hypothesis is
needed in its statement.

Put
\[
 \frac{\sqrt{17}}2\le R\le\frac{\sqrt{1105}}{16},\qquad
 k=\frac{\sqrt{21}}4,\qquad p=(1/2,-k),\qquad |p|=5/4.
\tag{1}
\]
Let B be a physical unit square contained in \(D_R\), with
\[
 \max_{z\in B}z_y=-b,\quad
 (q,-b)\in B,\quad
 0<q<61/60,\quad 49/60<b<1.
\tag{2}
\]
Assume B has a physical circle corner with positive x coordinate,
and assume the additional full-range implication
\[
                          q<1/2\quad\Longrightarrow\quad b>13/15.
\tag{3}
\]

**Theorem.** The fixed point p belongs to the closed square B.
The original top application may be a side mean or a vertex.

The elementary constants used below are
\[
 1<8/7<k<23/20<3/2,\qquad
 R<133/64<15/7<1+k.
\tag{4}
\]
The relevant positive squared reserves are
\((133/64)^2-1105/256=9/4096\),
\(21/16-(8/7)^2=5/784\), and
\((23/20)^2-21/16=1/100\).

## 1. The aligned top-face alternative

If B has a horizontal top side, write
\[
                       B=[X-1,X]\times[-b-1,-b].
\]
Its bottom corners have strictly larger norms than its top corners.
A physical circle corner with positive x coordinate must be
\((X,-b-1)\), and it is a farthest corner, so \(X\ge1/2\) and
\[
                             X^2+(b+1)^2=R^2.
\]
In fact \(X>1/2\), because \(b<1\) and \(R^2\ge17/4\).
Also
\[
 X^2<1105/256-(109/60)^2<9/4,
\]
so \(X<3/2\). Thus \(X-1<1/2<X\).
Finally \(b<1<k<b+1\), by (2), (4). Both coordinates of p
lie strictly between the appropriate faces of B.
This handles every top-side mean and both physical circle masks
in the aligned alternative.

## 2. The actual top-vertex chart

Otherwise the actual top contact is the unique highest vertex.
Write the two inward unit sides from it as
\[
 P_0=(q,-b),\qquad
 u=(c,-s),\quad v=(-s,-c),\qquad
 c,s>0,\quad c^2+s^2=1.
\tag{5}
\]
Then \(B=P_0+[0,1]u+[0,1]v\).

The top corner P_0 is not a circle point: its squared norm is
less than \((61/60)^2+1<17/4\).
The left adjacent corner \(P_0+v\) cannot be a circle point,
because the other corner \(P_0+u+v\) has squared norm larger by
\[
                         2(qc+bs)+1>0.
\]
Consequently any physical circle corner is either
\[
                     z_{\rm right}=P_0+u
       \quad\hbox{or}\quad z_{\rm bottom}=P_0+u+v.
\tag{6}
\]
If the right corner is a circle point, use that case, including
a tie with the bottom corner. Otherwise the bottom corner is
the only possible circle corner and has positive x coordinate
by hypothesis:
\[
                              q+c-s>0.
\tag{7}
\]

The coordinates of \(p-P_0\) in the actual u,v frame are
\[
 \xi=c(1/2-q)+s(k-b),\qquad
 \eta=s(q-1/2)+c(k-b).
\tag{8}
\]
Once \(\xi,\eta\ge0\) have been proved, their upper bounds
are automatic. Indeed
\[
 |p-P_0|^2
 <(31/60)^2+(1/3)^2
 =1361/3600<1,
\tag{9}
\]
using \(q<61/60,\ k<23/20,\ b>49/60\).
Thus each nonnegative own coordinate is strictly below one.

We shall use one full angular inequality:
\[
             s\ge4/5\quad\Longrightarrow\quad c/2+ks\ge k.
\tag{10}
\]
For \(c>0\),
\[
 c/2+ks-k
 =c\left(\frac12-\frac{kc}{1+s}\right)\ge
 c\left(\frac12-\frac{k}{3}\right)>0,
\]
because \(c\le3/5,\ 1+s\ge9/5\), and \(k<3/2\).
The limiting \(c=0\) equality also satisfies (10).

## 3. The right adjacent circle corner

If \(|z_{\rm right}|=R\), the bottom corner remains in \(D_R\).
Their squared-norm comparison gives
\[
                              qs-bc\ge1/2.
\tag{11}
\]
This forces \(c<1/2\). Otherwise \(s\le\sqrt3/2<7/8\),
and (2) would give
\[
 qs-bc<
 \frac{61}{60}\frac78-\frac{49}{60}\frac12
                        =\frac{77}{160}<\frac12.
\]
In particular \(s>4/5\).

Equation (11) immediately yields
\[
 \eta=qs-bc+ck-s/2\ge(1-s)/2+ck\ge0.
\]
If \(\xi<0\), then the actual circle corner would satisfy
\[
 z_{\rm right}\cdot u=1+qc+bs
                       >1+c/2+ks\ge1+k>R,
\]
by (4), (10), contradicting \(|z_{\rm right}|=R\).
Thus \(\xi\ge0\), and (9) proves \(p\in B\).
The weak comparison in (11) retains two-circle-corner ties.

## 4. The bottom circle corner: first own coordinate

Now let \(z=z_{\rm bottom}\) be the circle corner with (7).
Its actual own coordinates are
\[
 z\cdot u=1+qc+bs,\qquad z\cdot v=1-qs+bc.
\tag{12}
\]
Suppose \(\xi<0\). If \(s\ge4/5\), the same projection
contradiction as in Section 3 applies.

For \(s\le4/5\), one has \(c\ge3/5\).
Use (2), (8), (12), and \(k>8/7\):
\[
 \begin{split}
 z\cdot u+\frac45 z\cdot v
 &>\frac95+\frac{173}{150}c+
                         \left(k-\frac{61}{75}\right)s\\
 &>\frac95+\frac{173}{150}c+\frac{173}{525}s.
 \end{split}
\tag{13}
\]
The last positive cosine/sine expression is concave throughout
\(0\le\arcsin s\le\arcsin(4/5)\). Its endpoint values are
\[
                         \frac{443}{150},\qquad
                         \frac{14467}{5250}.
\]
Both exceed \(11/4\); the smaller excess is \(59/10500>0\).
Cauchy's inequality now gives
\[
 R^2=|z|^2>
       \frac{(11/4)^2}{1+(4/5)^2}
       =\frac{3025}{656}>\frac{1105}{256}.
\tag{14}
\]
The final exact reserve is \(3095/10496>0\).
This contradiction proves \(\xi\ge0\) on the entire bottom
circle-corner domain.

## 5. The bottom circle corner: second own coordinate

Suppose \(\eta<0\). Since \(k>b\), (8) first gives
\[
                              q<1/2,\qquad b>13/15.
\tag{15}
\]
If \(c\ge4/5\), then
\[
 b>k-\frac{s}{2c},\qquad
 c+s-\frac{s}{2c}\ge1.
\tag{16}
\]
For the second inequality, after factoring s its required
numerator is
\[
 (2c-1)(1+c)-2cs\ge27/25-1>0.
\]
Thus the bottom circle corner has vertical magnitude
\[
                         b+c+s>1+k>R,
\]
a contradiction.

If \(c<4/5\) and \(s\ge c\), positivity (7) and (15) give
\(s-c<q<1/2\). Hence
\[
                       c+s>\sqrt7/2>13/10.
\]
If instead \(s<c<4/5\), then \(s>3/5\) and
\(c>1/\sqrt2>7/10\), giving the same last bound.
In either case
\[
 b+c+s>\frac{13}{15}+\frac{13}{10}
              =\frac{13}{6}>\frac{133}{64}>R.
\tag{17}
\]
Again the physical circle corner cannot have that vertical
coordinate. Therefore \(\eta\ge0\).

Equations (8)--(9) complete the proof that p belongs to B.
Every orientation, the full top-side mean alternative, the
physical two-circle-corner tie, and the closed point endpoints
have been covered. The proof uses two analytic concavity
endpoints, with all arithmetic displayed; it introduces no
parameter grid or computational sign certificate.
