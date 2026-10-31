# A strict radial-incident adjacent endpoint has return diagonal projection greater than nine tenths

Date: October 26, 2026.

**Status: complete analytic local theorem, accepted after independent full-source root review in REVIEW_C6_RADIAL_ADJACENT_RETURN_DIAGONAL_ROOT_2026_10_26.md.** This source proves a whole physical endpoint bound. It does not by itself close either remaining mixed radial feature family or the unrestricted one-radial parent.

Retain the original one-radial, all-side alternating C6, its full radius window
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
 \qquad d=\sqrt{R^2-\frac14}-1,\qquad r_0^2=d^2+\frac14,
\tag{1}
\]
all original positive forces, both actual radial circle weights, every actual shared mean and endpoint, every transmitter slider, and all nine physical squares.

Consider a physically unique endpoint whose original turn is strictly greater than \(\pi/2\), whose actual S-incident application is the vertex adjacent to its unique circle corner, and whose actual other port is the opposite-to-circle vertex. These are the actual A-feature premises of the accepted strict-turn cover. A genuine S-incident mean already at the adjacent vertex is included with its unchanged physical contact label.

Normalize the actual other channel horizontally with outward side above the origin. Write its endpoint as
\[
                       T=(-m,H),\qquad H>0.
\tag{2}
\]

**Theorem.** The original return span and original channel height satisfy
\[
                              \boxed{m+H>\frac9{10}.}
\tag{3}
\]
No constraint on the feature at the other end of this horizontal channel is needed beyond the original proper channel chart.

## 1. Original endpoint chart and two whole-domain consequences

Use the actual chart from the adjacent classification:
\[
 c=\cos\eta,\quad s=\sin\eta,\quad
 \frac\pi4\le\eta<\frac\pi2,\quad
 v=(-c,s),\quad u=(-s,-c),
\]
\[
 C=s+c,\quad D=s-c,\quad Z=H+D,\quad
 A=\sqrt{R^2-Z^2},\quad
 z=(-A,Z)=av+bu,
\]
\[
 a=cA+sZ,\quad b=sA-cZ,\quad
 a>b>\frac12,\quad a^2+b^2=R^2,\quad m=A-C.
\tag{4}
\]
These statements follow from the actual positive radial concurrence, the opposite-vertex return, and properness; see SIX_CYCLE_ONE_RADIAL_BOTH_ADJACENT_PORTS_CLASSIFICATION.md, Sections 1--3, and the local-scope discussion in SIX_CYCLE_ONE_RADIAL_ADJACENT_AND_MEAN_CLASSIFICATION.md, Section 1.

The original adjacent port and its unchanged inward normal are
\[
 Q=z-v,\qquad t=\frac DZ\in[0,1),\qquad
 V=q-Q=v-tz=(tA-c,c),\quad L=|V|>0,\quad G=V/L.
\tag{5}
\]
The original reserve-one transmitter gives the actual radial port
\[
                              P=Q-G,\qquad |P|^2=r_0^2.
\tag{6}
\]

The strict turn at this unique unit means \(G_x<0\), so \(tA<c\). Substituting \(t=D/Z\) and the inverse own-coordinate relations gives
\[
 (s-c)A-cZ=-c^2a+(1-sc)b<0,
 \qquad c^2a>(1-sc)b.
\tag{7}
\]
This forces the uniform angle bound
\[
                              c>\frac38.
\tag{8}
\]
Indeed, if \(c\le3/8\), then \(sc\le c\le3/8\), while \(b>1/2\) and
\(a<R<133/64\). Consequently (7) would imply
\[
 \frac5{16}<(1-sc)b<c^2a
          <\frac9{64}\frac{133}{64}
          =\frac{1197}{4096}<\frac5{16}.
\]
The final positive contradictory margin is \(83/4096\). The strict radius comparison \(R<133/64\) follows from
\((133/64)^2-1105/256=9/4096>0\).

In the actual own frame, (5)--(6) read
\[
 P=\left(a-1-\frac{1-ta}{L}\right)v+
                  \left(b+\frac{tb}{L}\right)u.
\tag{9}
\]
Since \(t\ge0\), the radial-port norm in (6) yields
\[
                           \frac12<b\le r_0.
\tag{10}
\]
In particular
\[
 a^2=R^2-b^2\ge R^2-r_0^2=2d+1.
\tag{11}
\]
The full radius window gives \(d>91/100\), because
\[
 (79/40)^2-\frac14-(191/100)^2=\frac{101}{40000}>0.
\tag{12}
\]
Thus \(a>5/3\), using \(141/50>25/9\), and \(a+b-2>0\).

## 2. Concavity gives the complete diagonal bound

The inverse relations in (4) give the exact identity
\[
 \begin{split}
 m+H&=A-C+Z-D=A+Z-2s\\
    &=c(a-b)+s(a+b-2).
 \end{split}
\tag{13}
\]
For fixed original \(a,b\), both coefficients on the last line are positive. As a function of \(\eta\), that expression has second derivative equal to its negative. It is therefore concave on the entire interval
\[
                         \frac\pi4\le\eta\le\arccos(3/8).
\]
Its minimum occurs at an endpoint. Equation (8) puts the original angle in this interval, including the originally permitted \(\eta=\pi/4\).

At \(\eta=\pi/4\), (11)--(12) give
\[
 c(a-b)+s(a+b-2)=\sqrt2(a-1)>
                 \frac75\frac23=\frac{14}{15}>\frac9{10}.
\tag{14}
\]

At \(c=3/8\), \(s=\sqrt{55}/8\), the expression is
\[
 \frac{(3+\sqrt{55})a+(\sqrt{55}-3)b-2\sqrt{55}}8.
\tag{15}
\]
Fix the original R, substitute \(a=\sqrt{R^2-b^2}\), and enlarge the original \(b\) to the complete interval \([1/2,r_0]\). This is a connected real interval because \(r_0<R\). The expression in (15) is concave in b: the square-root coefficient is positive and the other b term is linear. It again suffices to bound its two endpoints.

At \(b=1/2\), \(a=d+1\), (15) equals
\[
 \frac38(d+1/2)+\frac{\sqrt{55}}8(d-1/2)
 >\frac{423+41\sqrt{55}}{800}
 >\frac{227}{250}>\frac9{10}.
\tag{16}
\]
Here \(\sqrt{55}>37/5\), with squared reserve \(6/25\). The final margin in (16) is \(1/125\).

At \(b=r_0\), \(a=\sqrt{2d+1}\). Equations (11)--(12) give the fixed lower bounds
\[
 a>\frac{47}{28},\qquad r_0>\frac{29}{28},
\tag{17}
\]
since
\[
 \frac{141}{50}-\left(\frac{47}{28}\right)^2
       =\frac{47}{19600}>0,\qquad
 \frac{10781}{10000}-\left(\frac{29}{28}\right)^2
       =\frac{661}{122500}>0.
\]
Both coefficients of a and b in (15) are positive. Substitution therefore gives (15) the strict lower bound
\[
 \frac{27+10\sqrt{55}}{112}
       >\frac{101}{112}
       =\frac9{10}+\frac1{560}.
\tag{18}
\]
Thus both b endpoints exceed \(9/10\), so (15) does throughout the whole interval. Equations (14)--(18) bound both angle endpoints, and concavity then proves (3) for every original physical endpoint.

## 3. Exact scope and a remaining partner criterion

The proof uses only the stated actual adjacent endpoint, its strict unique turn, its original radial-port norm, and the full radius window. It preserves a genuine endpoint mean, allows \(t=0\), and assumes neither equal radial weights nor a concurrence point inside the radial square.

For the remaining A/T combination, the actual return reserve is
\[
                           m+(a_T-1)=1.
\]
A separately proved whole-domain inequality \(a_T-H>11/10\) would combine with (3) to contradict that reserve:
\[
 m+a_T-1=(m+H)+(a_T-H)-1>1.
\]
This source does not assume or prove that additional T inequality, and therefore does not mark A/T closed. The A/O family, all lower-turn placements, every physical extra and every original parent gate remain unchanged by this local theorem alone.

All comparisons above are uniform concavity or fixed rational inequalities. No sampled configuration, angle grid, coefficient packet, Lean compilation or CI is used.

