# Three fixed markers control each side of an unrestricted actual four-chain

November 2, 2026. Complete hand proof of the stated marker theorem and
strict-subcritical side capacity. No coordinate cover or bound on exceptional
pairs is assumed. No mathematical program, numerical search, Lean, Lake,
or CI is a proof input.

The earlier exploratory four-square side-strip optimization suggested a
capacity direction. It is not used below. The proof instead retains the
physical outer endpoint of the actual four-chain and establishes an exact
three-point capture theorem.

Put
\[
 Q=\frac{1105}{256},\qquad \rho=\frac{91}{60},\qquad
 l=\frac{29}{60},\qquad u=\frac{13}{12}.
\]
For a unit square in the fixed coordinate frame, write
\[
 h\in[1/2,1/\sqrt2],\qquad
 g=\frac1{4h},\qquad k=\sqrt{\frac12-h^2}.
\]

## 1. Statement and the retained physical endpoint

Suppose an actual horizontal four-chain
\[
                      M_0<_xM_1<_xM_2<_xM_3
\]
is contained in the closed Q-disk. Put E=M3. Every physical unit S
contained in that disk, with center satisfying
\[
                             l\le x_S\le u,             \tag{1}
\]
and with open interior disjoint from E, contains at least one of the
three **closed** points
\[
               P_-=(3/5,-1),\qquad P_0=(3/5,0),\qquad P_+=(3/5,1).
                                                                  \tag{2}
\]
The orientation of S is unrestricted.

Consequently, in a packing strictly below Q that has this actual
four-chain, there are at most two outsiders with \(x\ge29/60\).
By reflection there are at most two outsiders with \(x\le-29/60\).
In a nine-square strict counterexample with an actual four-chain, at
least one of the five outsiders therefore has \(|x|<29/60\).

Closed containment in (2) is intentional. The proof of the strict-radius
capacity uses common center expansion and does not silently convert marker
boundary contacts into interior contacts.

The reviewed theorem
[UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md](UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md) gives
\[
 \frac{89}{60}<x_E<\rho,\qquad h_E<\frac8{15},\qquad
                  g_E-|y_E|>\frac{221}{600}.             \tag{3}
\]
The inscribed axis-aligned square of E has \(g_E>15/32\).
Set
\[
 c=\frac{221}{600},\qquad
 L=\frac{503}{480}=\rho-\frac{15}{32},\qquad
 \xi=\frac35,\qquad \lambda=L-\xi=\frac{43}{96}.
\]
Every point of the vertical segment
\[
                              \{L\}\times[-c,c]          \tag{4}
\]
lies strictly inside E's inscribed square, and hence strictly inside E.
Indeed \(x_E-g_E<L<x_E+g_E\) by (3), and (3) also gives the strict
vertical containment. The right-hand inequality follows, for example,
from \(x_E+g_E>89/60+15/32>L\).

## 2. Every side square has a genuine section on the marker line

Let I be S's closed vertical section at x=ξ, regarded as a y-interval.
It is nondegenerate and the line passes strictly between the square's
extreme horizontal coordinates, because
\[
 x_S-h_S\le u-\frac12=\frac7{12}<\xi,
 \qquad x_S+h_S\ge l+\frac12=\frac{59}{60}>\xi.           \tag{5}
\]

We first exclude I lying wholly above 1 or wholly below −1.
Write \(X=x_S\), \(Y=y_S\). Every unit contains its centered closed
radius-1/2 disk. Since
\[
                |X-\xi|\le\frac{29}{60}<\frac12,
\]
this disk has a section at x=ξ with half-length
\[
                   w(X)=\sqrt{\frac14-(X-\xi)^2}.
\]
If \(\inf I>1\), then \(Y-w(X)>1\), and therefore
\[
 |c_S|^2>X^2+(1+w(X))^2
      =\frac{89}{100}+\frac65X+2w(X)=:F(X).             \tag{6}
\]
The function F is concave on [l,u], so its minimum is at an endpoint.
At those endpoints,
\[
 F(l)=\frac{147}{100}+\frac{\sqrt{851}}{30}
       >\frac{731}{300}>\rho^2,
\]
\[
 F(u)=\frac{219}{100}+\frac{\sqrt{59}}{30}
       >\frac{61}{25}>\rho^2.
\]
Here \(\sqrt{851}>29\), \(\sqrt{59}>15/2\), and
\(731/300-\rho^2=491/3600>0\). This contradicts the universal strict
center bound \(|c_S|<\rho\). Reflection handles \(\sup I<-1\).

Suppose S misses all three closed markers (2). Since I is a closed
interval, the only possibilities left are
\[
                             I\subset(0,1)
          \quad\hbox{or}\quad I\subset(-1,0).           \tag{7}
\]
In particular I has length strictly below one. We will show that either
case forces S to overlap the segment (4) in interior points, contradicting
disjointness from E. Because (4) is symmetric about y=0, it suffices to
treat \(I\subset(0,1)\).

## 3. Exact geometry of a short left-hand section

Write the absolute physical side-axis components of S as
\[
 a\ge b\ge0,\qquad a^2+b^2=1,\qquad
                  h=\frac{a+b}{2},\quad k=\frac{a-b}{2}.
\]
The vertical section at horizontal offset t from the center has length
\(1/a\) when \(|t|\le k\), and length
\((h-|t|)/(ab)\) when \(k\le|t|\le h\), for b>0.
When b=0 every nonextreme section has length one.

Thus length(I)<1 implies b>0 and
\[
                         |\xi-X|>h-ab\ge k.             \tag{8}
\]
It also implies X>ξ. Indeed, if X≤ξ, then
\(|\xi-X|\le7/60\), whereas
\[
                  h-ab\ge\frac{\sqrt2-1}{2}>\frac7{60}.
\]
The lower bound follows by writing a+b=p and minimizing
\((1+p-p^2)/2\) on \([1,\sqrt2]\).

Measure horizontal depth from S's leftmost vertex, and let
\[
                         z=h+\xi-X.
\]
Equations (1), (5), and (8) give
\[
                        h-l\le z<ab\le b\le a.         \tag{9}
\]
The line x=L has depth z+λ. It too lies strictly inside the horizontal
projection of S: the rightmost coordinate satisfies
\[
 X+h=\xi+2h-z>\xi+2h-ab
          \ge\xi+\sqrt2-\frac12>\xi+\lambda=L.          \tag{10}
\]

Let \(U_S(x)\), \(L_S(x)\) denote its upper and lower section endpoints.
We claim that both cross-section gaps obey
\[
 \begin{split}
 U_S(\xi)-L_S(L)&>\frac{379}{600},\\
 U_S(L)-L_S(\xi)&>\frac{379}{600}.                       \tag{11}
 \end{split}
\]
These inequalities retain the actual edges of the arbitrarily oriented S.

For clarity, first take the orientation whose leftmost vertex has
vertical coordinate T=Y+k. At horizontal depth w, its upper and lower
boundary functions are
\[
 \begin{split}
 U(w)&=T+\min\left\{\frac ba w,\frac{1-aw}{b}\right\},\\
 L(w)&=T+\max\left\{-\frac ab w,\frac{bw-1}{a}\right\}.
 \end{split}                                             \tag{12}
\]
These are the four actual side-line equations. Since z<ab≤b≤a,
\(U(z)=T+(b/a)z\) and \(L(z)=T-(a/b)z\). Substituting w=z+λ
in (12) gives the exact cross-gaps
\[
 \begin{split}
 U(z)-L(z+\lambda)
 &=\min\left\{\frac{z}{ab}+\frac ab\lambda,
                         \frac{1-b\lambda}{a}\right\},\\
 U(z+\lambda)-L(z)
 &=\min\left\{\frac{z}{ab}+\frac ba\lambda,
                         \frac{1-a\lambda}{b}\right\}.
 \end{split}                                             \tag{13}
\]
Reflecting vertically exchanges these two formulas, covering the other
chirality as well.

Both fractional terms involving 1 have the lower bound
\[
 \frac{1-b\lambda}{a},\ \frac{1-a\lambda}{b}
       \ge\sqrt{1-\lambda^2}>\frac45>\frac{379}{600}.     \tag{14}
\]
For example,
\((1-b\lambda)^2-(1-\lambda^2)a^2=(b-\lambda)^2\ge0\);
all factors are positive. Also λ<1/2, which gives the strict bound
\(\sqrt{1-\lambda^2}>\sqrt3/2>4/5\).

The smaller of the other two terms in (13) is at least
\[
                   \frac{h-l}{ab}+\frac ba\lambda.
\]
The following scalar proof shows that this is strictly greater than
379/600. It completes (11).

## 4. A whole-interval quartic proof of the cross-gap estimate

We must prove, for a≥b>0 and a²+b²=1,
\[
 G:=\frac{a+b}{2}-\frac{29}{60}
       +\frac{43}{96}b^2-\frac{379}{600}ab>0.           \tag{15}
\]
Set t=b/a∈(0,1]. Multiplication by 1+t² transforms (15) into
\[
 \frac12(1+t)\sqrt{1+t^2}
             >\frac{29}{60}+\frac{379}{600}t+\frac{17}{480}t^2.
                                                                  \tag{16}
\]
Both sides are positive. After multiplying both sides by two, one squaring
shows that (16) is equivalent to positivity of the explicit quartic
\[
 \begin{split}
 P(t)={}&\frac{59}{900}-\frac{1991}{4500}t
        +\frac{12017}{45000}t^2\\
        &+\frac{65557}{36000}t^3+\frac{57311}{57600}t^4. \tag{17}
 \end{split}
\]
The complete coefficient identity is
\[
 P(t)=(1+t)^2(1+t^2)
       -\left(\frac{29}{30}+\frac{379}{300}t
                         +\frac{17}{240}t^2\right)^2.  \tag{18}
\]

Every coefficient of P'' is positive, and
\[
                       P''(t)\ge\frac{12017}{22500}>\frac12
                         \quad(t\ge0).                \tag{19}
\]
At the rational anchor \(t_0=9/40\), direct substitution in (17) gives
\[
 P(t_0)=\frac{415436159}{147456000000}>\frac1{400},
 \qquad
 P'(t_0)=-\frac{342793}{921600000},\quad |P'(t_0)|<\frac1{1000}.
                                                                  \tag{20}
\]
For a direct integer check of the first comparison, the excess numerator
over 1/400 is 46796159. All entries can also be checked by expanding (18).

The quadratic lower bound from (19) now gives, for all t∈[0,1],
\[
 \begin{split}
 P(t)&\ge P(t_0)+P'(t_0)(t-t_0)+\frac14(t-t_0)^2\\
     &\ge P(t_0)-\bigl(P'(t_0)\bigr)^2
      >\frac1{400}-\frac1{1000000}>0.
 \end{split}                                             \tag{21}
\]
This proves (15)--(16) on the full orientation interval, and hence both
cross-gap estimates (11). No sampled angles are used.

## 5. Marker capture by physical overlap with the endpoint

Assume \(I\subset(0,1)\). The first inequality in (11) gives
\[
                L_S(L)<U_S(\xi)-\frac{379}{600}
                       <1-\frac{379}{600}=c.
\]
The second gives
\[
                U_S(L)>L_S(\xi)+\frac{379}{600}>-c.
\]
Thus the relative interior of S's section at x=L intersects (−c,c).
The line is strictly between S's horizontal extremes by (10), so these
relative-interior points are interior points of S. They are also interior
points of E by (4). This contradicts physical interior-disjointness.

Reflection treats \(I\subset(-1,0)\). All possibilities for missing
the three closed markers have now been excluded, proving (2).

## 6. Strict-subcritical side capacity and what remains

Suppose a packing has q<Q and an actual horizontal four-chain, together
with three outsiders having x≥29/60. Apply one common factor t>1 to all
centers, retaining every frame, until the largest squared corner norm is Q.
As proved in the global boundary-normalization note, every physical pair
then has a strict separator, so the expanded **closed** units are pairwise
disjoint. Actual four-chain inequalities are preserved under this expansion.

The three selected outsider centers remain in x≥29/60. The unrestricted
outsider-strip theorem applies afresh to the expanded chain and places
them in x<13/12. Its internal square M2 also has
\(29/60<x_{M_2}<31/60\). Thus these four units satisfy (1), and all
are disjoint from E=M3. By (2), they each contain one of three fixed
closed markers. Two must contain the same point, contradicting their
closed-disjointness.

Therefore a strict subcritical packing with an actual four-chain has at
most two outsiders on its right side. Reflecting gives the same result
on its left side. With five outsiders at least one has |x|<29/60.

This is an unrestricted side-capacity theorem. It does not provide actual
coordinate separators between the remaining outsiders and the two internal
main squares. The possible middle-occupancy counts, and any extraction of
a physical sharp terminal from them, remain separate geometric obligations.
No unrestricted nine-square lower bound or equality classification is
claimed by this note alone.

## 7. Marker order agrees with the actual order of center heights

In the closed-disjoint normalization used in Section 6, take any two units
whose centers satisfy (1) and which avoid E. Their center x-gap is at most
3/5. On the vertical line halfway between those two x-centers, the point
at each unit's own center height lies strictly inside its radius-1/2 disk.
Thus both units have nondegenerate sections there, and their vertical
section order agrees with the order of their center y-coordinates.

The halfway line and the marker line x=3/5 both lie strictly between
the horizontal extremes of each unit. On every line between them both
sections remain nondegenerate. The two vertical section intervals cannot
exchange their order without intersecting: their upper and lower boundary
functions are continuous on this closed interval of x-coordinates, and
the units are closed-disjoint. Hence their section order on the marker
line also agrees with their center-height order.

In particular, when a side contains three units and each must occupy a
different marker, their increasing marker indices −1,0,1 identify their
increasing actual center y-coordinates. This does not assert separation
of their full vertical projections. It is an order statement about the
centers and the actual sections on the one common line.

## 8. A quantitative height gap next to an internal main square

Every pair of side units has horizontal center gap below 3/5. Their
inscribed radius-1/2 disks are disjoint, so their center distance is at
least one. Consequently every such pair has
\[
                            |\Delta y|>\frac45.          \tag{22}
\]

If one member is the corresponding internal main square M1 or M2, the
bound strengthens to
\[
                            |\Delta y|>\frac{29}{30}.    \tag{23}
\]
Indeed its main-chain halfwidth is h<31/60, so its inscribed aligned
square has halfwidth g>15/31. The radius-1/2 disk of the other square
is disjoint from that aligned square. Since the horizontal gap is less
than 3/5, the distance from its center to the aligned square forces
\[
 |\Delta y|\ge
 g+\sqrt{\frac14-\max\{3/5-g,0\}^2}
 \ge\frac{15}{31}+\sqrt{\frac14-\left(\frac{18}{155}\right)^2}
 >\frac{29}{30}.
\]
The middle inequality follows by monotonicity in g on g∈[15/31,1/2].
For the final positive-root comparison, note
\[
 \frac14-\left(\frac{18}{155}\right)^2
       -\left(\frac{29}{30}-\frac{15}{31}\right)^2
       =\frac{2960}{864900}>0.
\]

Every side center also satisfies |y|<36/25, from |x|≥29/60 and
|c|<91/60; the squared comparison is
\[
 \left(\frac{29}{60}\right)^2+\left(\frac{36}{25}\right)^2
       -\left(\frac{91}{60}\right)^2=\frac{13}{1875}>0.
\]
Thus if a full side column has its main square assigned the middle marker,
the center order in Section 7 and (23) imply
\[
                         |y_{M_i}|<\frac{71}{150}.       \tag{24}
\]
If its main square has the bottom marker, the two successors instead give
\(y_{M_i}< -49/150\), by (22)--(23); the top-marker case is the reflected
bound \(y_{M_i}>49/150\). These are necessary height restrictions, not
actual projection comparisons or a completed nine-square capacity theorem.

## 9. Equal main-marker indices exclude a middle center between the mains

The stronger physical clearance proved independently in
[UNRESTRICTED_ACTUAL_FOUR_CHAIN_INNER_CLEARANCE_HAND_PROOF.md](UNRESTRICTED_ACTUAL_FOUR_CHAIN_INNER_CLEARANCE_HAND_PROOF.md) states that
every middle outsider F, meaning |x_F|<29/60, satisfies
\[
 \begin{cases}
 |y_F-y_{M_2}|>59/60,&x_F\ge0,\\
 |y_F-y_{M_1}|>59/60,&x_F\le0.
 \end{cases}                                             \tag{25}
\]
Both inequalities apply on x_F=0. Consequently, whenever
\[
                         |y_{M_1}-y_{M_2}|<59/60,        \tag{26}
\]
every middle outsider is either above both main centers or below both.
It cannot be between their heights, since its distance in y from the
main in its own half-plane would then be less than 59/60.

Here are exact marker conditions that imply (26).

First, both internal main centers satisfy
\[
                             |y_{M_i}|<\frac{27}{20}.    \tag{27}
\]
Their h<31/60 gives
\[
 k^2>839/3600>(193/400)^2,
\]
the last comparison having positive cross-product difference 143600.
If |y|≥27/20, then |y|>|x|. An outward-quadrant corner, taking the
smaller of the two offset orders, would force
\[
 q>\left(\frac{59}{60}\right)^2+
                \left(\frac{733}{400}\right)^2
   =Q+\frac{1547}{180000}>Q.
\]
This proves (27).

If both mains contain their respective bottom marker, marker containment
and h<31/60 put both heights in
\((-27/20,-29/60)\). Their difference is therefore below 13/15,
which is below 59/60. The same conclusion holds when both contain their
respective top marker, by reflection. These two conclusions do not require
both side columns to be full.

For the zero-marker case, an internal main square containing its marker
\((\pm3/5,0)\) has
\[
                              |y_{M_i}|<\frac{51}{100}.  \tag{28}
\]
To see this, its side-axis components a≥b satisfy
\[
 b=h-k<\frac{41}{1200}<\frac7{200},\qquad a>\frac{99}{100}.
\]
The horizontal gap from its center to the marker is below 7/60.
Its nearly vertical physical side inequality therefore gives
\[
 a|y_{M_i}|\le\frac12+b\frac7{60},\qquad
 |y_{M_i}|<\frac{6049}{11880}<\frac{51}{100}.
\]
If at least one of the two side columns is full, its zero-marker main
also satisfies (24). The two height bounds then imply
\[
 |y_{M_1}-y_{M_2}|<\frac{71}{150}+\frac{51}{100}
                         =\frac{59}{60}.                \tag{29}
\]
Thus (26) also follows when both mains contain their zero markers and
at least one side has two outsiders.

In particular, with exactly one middle outsider both side columns are
full. All three equal-index main-marker patterns j=−1,0,1 force that
middle outsider to lie above both main centers or below both. The six
unequal-index patterns are not excluded by this argument, nor is the
above/below alternative itself a completed physical terminal.
