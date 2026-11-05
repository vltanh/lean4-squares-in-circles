# A two-square cap in the central strip, and its lower-floor obstruction

November 2, 2026. Complete hand proof. The support minima, scalar
polynomial, and rational anchors below are derived explicitly. No
mathematical program, numerical sampling, Lean, Lake, or CI is used.

Put

\[
 Q=\frac{1105}{256},\qquad r=\sqrt Q,\qquad
 l=\frac{29}{60},\qquad D=2l=\frac{29}{30}.
\]

## 1. Statement

**Theorem.** There cannot be two physical, interior-disjoint unit squares
in the closed Q-disk such that both center x-coordinates belong to
\([-29/60,29/60]\) and both squares lie wholly in

\[
                         y\ge\frac9{20}.
\tag{1}
\]

Their orientations are arbitrary. No coordinate projection separation
between the two squares is assumed. Reflection gives the same conclusion
below \(y=-9/20\).

**Stronger ordered form.** It is enough that the unit with the lower
center lie wholly above 9/20. The higher-center unit needs only disk
containment, physical interior-disjointness, and its center in the same
x-strip. Equivalently, a unit in this strip lying wholly above 9/20 cannot
have another strip unit whose center is at least as high. The proof below
establishes this form as well.

The floor 7/16 cannot replace 9/20 in this statement. Section 7 gives an
exact strictly subcritical counterexample, including a version with
strictly interior strip centers and strictly separated closed squares.
No claim is made that 9/20 is the best possible floor.

Write \(H_S(w)\) for the support halfwidth of a centered physical unit
square S in vector direction w. In an orthonormal frame,
\(h_S=H_S(e_x)=H_S(e_y)\in[1/2,1/\sqrt2]\).

## 2. An exact two-vector support minimum

For nonzero vectors v,w with \(|v|\ge|w|\),

\[
 \min_S\{H_S(v)+H_S(w)\}
 =\frac12\left(|v|+
       \frac{|v\cdot w|+|\det(v,w)|}{|v|}\right).
\tag{2}
\]

Here the minimum runs over all orientations of a unit square. It is
attained by taking a physical side normal parallel to v.

To prove this, write a side frame as orthonormal vectors u,z. The quantity
to minimize is

\[
 \frac12\bigl(|u\cdot v|+|z\cdot v|
                  +|u\cdot w|+|z\cdot w|\bigr).
\]

Between consecutive angles at which one of these four projections
vanishes, all signs are fixed. The expression has second derivative equal
to its negative and is positive; it is therefore concave on that
interval. A minimum occurs at a breakpoint, where a side normal aligns
with v or with w. If \(L=|v|\), \(M=|w|\), and
\(f=|\cos\alpha|+|\sin\alpha|\ge1\) for their relative angle,
these two candidate values are

\[
 \frac{L+Mf}{2},\qquad \frac{M+Lf}{2}.
\]

The second minus the first is \((L-M)(f-1)/2\ge0\), proving (2).
The formula also extends to w=0 by continuity.

## 3. Reduction to a positive separating normal

Suppose two squares satisfy the hypotheses of the stronger ordered form.
Denote the lower center by L and the higher by U. Reflect the horizontal
coordinate if needed so U is to the right of L. Put

\[
 d_x=x_U-x_L\ge0,\qquad d_y=y_U-y_L\ge0,
 \qquad c=\frac9{20}.
\]

Containment of U and the whole-square floor of L give

\[
 0\le d_x\le D<1,
 \qquad
 0\le d_y\le r-c-h_L-h_U\le r-c-1<1.
\tag{3}
\]

For the last strict inequality it suffices to use
\(r<25/12\), which gives \(r-c-1<19/30\).

The two physical squares admit a separating unit normal n oriented from
L to U, so

\[
 n\cdot(c_U-c_L)\ge H_L(n)+H_U(n)\ge1.
\tag{4}
\]

If either component of n were nonpositive, its scalar product with
\((d_x,d_y)\) would be less than one by (3). Therefore

\[
 n=(a,b),\qquad a>0,\quad b>0,\quad a^2+b^2=1.
\tag{5}
\]

This argument treats every possible separating normal; it does not depend
on which square owns a separating side axis. It also shows that the two
center gaps cannot vanish in any putative example.

For \(0\le t\le a\), set \(m=(t,b)\). Then \(|m|\le1\), and (2)
gives

\[
 H_L(n)+b h_L\ge\frac12+\frac{b(a+b)}2,
\tag{6}
\]

\[
 H_U(n)+H_U(m)
 \ge\frac12+\frac{(a-b)t+b(a+b)}2.
\tag{7}
\]

Indeed, in (6) the second vector is \(b e_y\). For (7),
\(n\cdot m=at+b^2\ge0\) and
\(\det(n,m)=b(a-t)\ge0\), whose sum is
\((a-b)t+b(a+b)\).

From (4), \(x_L\ge-l\), and \(y_L\ge c+h_L\), we obtain

\[
 a x_U+b y_U\ge-al+bc+b h_L+H_L(n)+H_U(n).
\]

On the other hand, containment of U gives
\(m\cdot c_U+H_U(m)\le r|m|\), while
\((a-t)x_U\le(a-t)l\). Combining these facts with (6)--(7) proves,
for every \(0\le t\le a\),

\[
 r\sqrt{t^2+b^2}\ge A+Bt,
\quad
 A=1-Da+b(c+a+b),\quad
 B=l+\frac{a-b}{2}.
\tag{8}
\]

The physical pair and both variable orientations have now been retained in
one scalar inequality.

## 4. Steep normals are impossible

Suppose \(a\le b\). Taking t=0 in (8) gives

\[
 r\ge Z:=c+a+b+\frac{1-Da}{b}.
\tag{9}
\]

Set \(w=a/b\in[0,1]\). The part after c is

\[
 J(w)=\frac{w^2+w+2}{\sqrt{1+w^2}}-Dw.
\]

Direct differentiation gives

\[
 J'(w)=\frac{w^3+1}{(1+w^2)^{3/2}}-D,
 \qquad
 J''(w)=\frac{3w(w-1)}{(1+w^2)^{5/2}}\le0.
\]

Thus J is concave and

\[
 J(w)\ge\min\{J(0),J(1)\}
       =\min\{2,2\sqrt2-D\}>\frac{11}{6}.
\]

The strict comparison uses \(\sqrt2>7/5\). Consequently (9) would give

\[
 r>\frac9{20}+\frac{11}{6}=\frac{137}{60}
   >\frac{25}{12}>r,
\]

a contradiction. This exclusion covers both ownership choices and both
physical-frame chiralities because (8) had already minimized over all
orientations.

## 5. Shallow normals give an explicit radius lower bound

It remains to consider \(a\ge b>0\). In this case B>0 and

\[
 Z:=A/b=c+a+b+\frac{1-Da}{b}>0.
\]

The choice

\[
                         t_* =\frac{Bb}{Z}
\]

belongs to (0,a). In fact \(Z>a+b\), so
\(aZ>a(a+b)\ge1\), whereas
\(Bb\le(l+1/2)b<1\). Evaluating (8) at this allowed value yields

\[
 Q=r^2\ge B^2+Z^2
 =\left(\frac{29}{60}+\frac{a-b}{2}\right)^2
  +\left(\frac9{20}+a+b+\frac{1-(29/30)a}{b}\right)^2.
\tag{10}
\]

For clarity, the ratio
\((A+Bt)/\sqrt{t^2+b^2}\) at \(t=t_*\) equals
\(\sqrt{B^2+Z^2}\); no unproved optimization is used.

We next prove that the right side of (10) is strictly larger than Q on
the entire remaining orientation interval.

## 6. One polynomial and a positive cubic lower bound

Use the half-angle parameter

\[
 s=\frac{b}{1+a}\in(0,\sqrt2-1]\subset(0,1/2],
 \quad
 a=\frac{1-s^2}{1+s^2},\quad b=\frac{2s}{1+s^2}.
\]

Then

\[
 B=\frac{59-60s-s^2}{60(1+s^2)},
 \qquad
 Z=\frac{N(s)}{60s(1+s^2)},
\]

where

\[
                    N(s)=1+87s+180s^2-33s^3+59s^4.
\]

The exact square-expansion identity is

\[
 B^2+Z^2-Q=\frac{P(s)}{57600s^2(1+s^2)^2},
\tag{11}
\]

\[
 P(s)=16\left[N(s)^2+s^2(59-60s-s^2)^2\right]
                    -248625s^2(1+s^2)^2.
\tag{12}
\]

Expanding this single identity gives the complete coefficient list

\[
\begin{aligned}
P(s)={}&16+2784s-66065s^2+386784s^3-13122s^4\\
       &-23904s^5+108655s^6-62304s^7+55696s^8.
\end{aligned}
\tag{13}
\]

For \(0\le s\le1/2\),

\[
 -13122s^4-23904s^5\ge-25074s^4\ge-12537s^3,
\]

and

\[
 108655s^6-62304s^7=s^6(108655-62304s)\ge0.
\]

Therefore

\[
 P(s)\ge C(s):=16+2784s-66065s^2+374247s^3.
\tag{14}
\]

The following two hand ranges prove C>0.

For \(0\le s\le3/50\), put
\(J_0(s)=2784-66065s+374247s^2\). Its derivative is negative on
this interval, and

\[
 J_0(3/50)=\frac{418473}{2500}>0.
\]

Thus \(C(s)=16+sJ_0(s)\ge16\).

For \(s\ge3/50\),

\[
 C''(s)=-132130+2245482s
       \ge\frac{64973}{25}>2500.
\]

At the rational anchor \(s_0=9/100\), direct fraction arithmetic gives

\[
 C(s_0)=\frac{4259563}{1000000}>4,
 \qquad
 C'(s_0)=-\frac{134979}{10000},\quad |C'(s_0)|<14.
\tag{15}
\]

The quadratic lower bound obtained by integrating C''>2500 gives, on
the whole half-line \([3/50,\infty)\),

\[
\begin{aligned}
 C(s)&\ge C(s_0)+C'(s_0)(s-s_0)+1250(s-s_0)^2\\
     &\ge C(s_0)-\frac{C'(s_0)^2}{5000}
      >4-\frac{196}{5000}=\frac{4951}{1250}>0.
\end{aligned}
\tag{16}
\]

Consequently P(s)>0 throughout the interval in (11). Its denominator is
positive, so (10) contradicts (11). This completes the theorem.

## 7. Why the floor 7/16 is false

Take both physical frames to be

\[
 u=\frac{(99,20)}{101},\qquad
 v=\frac{(-20,99)}{101},\qquad
 h=\frac{119}{202},\quad k=\frac{79}{202}.
\]

First take centers

\[
 c_L=\left(-\frac{29}{60},\frac7{16}+h\right),
 \qquad
 c_U=\left(\frac{29}{60},\frac7{16}+h+\frac{53}{200}\right).
\tag{17}
\]

Both whole lower edges are at least 7/16, and both x-centers belong to the
claimed central strip. Their center gap along the common side normal u is

\[
 u\cdot(c_U-c_L)
 =\frac{99}{101}\frac{29}{30}
  +\frac{20}{101}\frac{53}{200}=1.
\]

Thus their open interiors are disjoint.

For U, both physical side-coordinate projections of its center are
positive. The farthest corner is therefore

\[
 c_U+\frac{u+v}{2}
 =\left(\frac{5299}{6060},\frac{75981}{40400}\right).
\]

Its two coordinates are strictly smaller than \(7/8\) and
\(301/160\), respectively. Hence every corner of U has squared norm

\[
 <\left(\frac78\right)^2+\left(\frac{301}{160}\right)^2
  =\frac{110201}{25600}
  <Q=\frac{110500}{25600}.
\tag{18}
\]

For L, the crude bounding box already suffices. Since
\(h<19/32\), every corner satisfies

\[
 |x|<\frac{13}{12},\qquad |y|<\frac{13}{8},
\]

so its squared norm is less than

\[
 \left(\frac{13}{12}\right)^2+\left(\frac{13}{8}\right)^2
 =\frac{2197}{576}<Q.
\]

There is also an exact strict version. Replace the two x-centers in (17)
by \(\pm(29/60-1/100000)\), and increase only the upper y-center by
\(1/5000\). The separating gap then becomes

\[
 1-\frac{99}{101\cdot50000}
   +\frac{20}{101\cdot5000}
 =1+\frac1{50000}>1.
\]

Thus the two closed squares are strictly separated and their centers lie
strictly inside the strip. Estimate (18) remains valid: its x-coordinate
has decreased, and the original y-coordinate reserve is

\[
 \frac{301}{160}-\frac{75981}{40400}
   =\frac{43}{80800}>\frac1{5000}.
\]

The floor remains 7/16 or higher. This refutes even the strict-subcritical,
open-center-strip version of the lower-floor conjecture.

## 8. A precise actual-four-chain caller

Let \(M_0<_xM_1<_xM_2<_xM_3\) be an actual four-chain in Q. The
adjacent-proxy barrier from
[ADJACENT_PROXY_BARRIER_HAND_PROOF.md](ADJACENT_PROXY_BARRIER_HAND_PROOF.md) proves that any physical outsider
with center between the two inner centers and above both inner centers has

\[
 y_F-h_F>\min(y_1,y_2)+\frac{869}{1860}.
\]

If

\[
             \min(y_1,y_2)\ge-\frac8{465},
\]

this whole lower edge is strictly above 9/20, because
\(9/20-869/1860=-8/465\). At most one such outsider can have its
x-center in \([-29/60,29/60]\), by the theorem proved here.
More strongly, once such a strip outsider exists, there is no other strip
outsider with a higher center, whether or not the latter itself satisfies
the adjacent-proxy barrier's hypotheses.

The reflected conclusion applies to outsiders below both inner centers
when \(\max(y_1,y_2)\le8/465\). These are conditional physical callers;
they do not assert that an arbitrary actual-four configuration has these
main-height bounds or that all its outsiders fall into these two classes.
