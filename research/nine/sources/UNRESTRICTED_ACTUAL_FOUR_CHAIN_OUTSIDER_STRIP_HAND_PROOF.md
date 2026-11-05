# Every physical outsider of an actual four-chain lies in a narrow center strip

November 2, 2026. A complete hand proof of an unrestricted conditional
geometric theorem. No coordinate-cover, exceptional-pair, or common-frame
assumption is imposed on the outsiders. No mathematical scripts, numerical
search, Lean, Lake, or CI are used.

Put
\[
 Q=\frac{1105}{256},\qquad \rho=\frac{91}{60}.
\]
For a physical unit square in the fixed coordinate frame write
\[
 \frac12\le h\le\frac1{\sqrt2},\qquad
 g=\frac1{4h},\qquad k=\sqrt{\frac12-h^2}.
\]
Its horizontal and vertical projection halfwidths both equal h. It contains
the centered axis-aligned square of halfwidth g. Its actual vertex offsets,
up to coordinate reflections, are \((h,k),(-k,h),(-h,-k),(k,-h)\).

## 1. The statement

Suppose four interior-disjoint physical unit squares contained in the
closed Q-disk form an actual horizontal projection chain
\[
                         M_0<_xM_1<_xM_2<_xM_3.
\]
Let F be any additional physical unit square in that disk whose open
interior is disjoint from the four main squares. Then
\[
                         \boxed{|x_F|<\frac{13}{12}.}       \tag{1}
\]
The frame and pose of F are arbitrary. In fact the proof only needs F to
be disjoint from the relevant outer endpoint, after deriving that endpoint's
bounds from the full actual four-chain.

The argument uses the following elementary four-chain facts
\[
 \begin{gathered}
 -\rho<x_0<-\frac{89}{60},\qquad
 \frac{89}{60}<x_3<\rho,\qquad
 \frac12\le h_0,h_3<\frac8{15},\\
 |y_0|,|y_3|<\frac15,
 \end{gathered}                                             \tag{2}
\]
which follow only from the actual four-chain and disk containment, as
verified next. The transverse endpoint inequality is proved in Section2.

### Elementary four-chain bounds

For a square centered at c, choose the corner whose two frame-coordinate
signs agree with c. Its squared norm is

    |c|^2+1/2+|c dot u|+|c dot v| >= |c|^2+|c|+1/2.

Thus |c|<=sqrt(Q-1/4)-1/2<91/60; the last squared comparison has
positive reserve 31/57600. The three actual chain edges give

    x3-x0 >= h0+2h1+2h2+h3 >=3.

It follows that x0<-89/60 and x3>89/60. The sum on the right is
strictly less than 91/30. Since every h_i>=1/2, we obtain
h0,h3<8/15 and h1,h2<31/60. The same chain and center bound give

    -31/60<x1<-29/60,     29/60<x2<31/60,
    |x0|-h0>59/60,       x3-h3>59/60.

For either endpoint put X=|x|, Y=|y|. The center bound and X>89/60
give Y^2<1/10, hence Y<X. One of the actual outward corners has
offsets (h,k) or (k,h). Since X>Y, its squared norm is at least

    (X+k)^2+(Y+h)^2.

The concave function h+sqrt(1/2-h^2) on [1/2,8/15] is greater than
149/150: at h=1/2 it equals one, while at h=8/15 its second summand
is greater than 23/50 because 97/450>(23/50)^2. Therefore

    X+k=(X-h)+(h+k)>59/60+149/150=593/300.

If Y>=1/5, containment would imply

    Q>(593/300)^2+(7/10)^2>Q,

where the positive reserve in the last comparison is 116359/1440000.
This contradiction gives |y0|,|y3|<1/5 and proves every bound in(2).

## 2. A transverse budget retaining endpoint tilt

Set
\[
 S=|y_0|+|y_3|,\qquad U=h_0+h_3-1.
\]
We strengthen the previous bound S≤1/8 to
\[
             \boxed{S+\frac{37}{50}U\le\frac18.}             \tag{3}
\]

For each endpoint put \(X_i=|x_i|\), \(Y_i=|y_i|\).
The bounds (2) give \(X_i>Y_i\). An actual outward-quadrant corner has
offsets either \((h_i,k_i)\) or \((k_i,h_i)\); the latter gives the
smaller squared norm when \(X_i>Y_i\). Thus, without asserting which
of these two vertices is physically present, we obtain
\[
                    (X_i+k_i)^2+(Y_i+h_i)^2\le Q.
\]
The actual chain gives \(X_0+X_3\ge2+h_0+h_3\). Adding the two
corner vectors and applying the planar triangle inequality yields
\[
 4Q\ge(2+h_0+k_0+h_3+k_3)^2+(S+h_0+h_3)^2.                 \tag{4}
\]

On \(1/2\le h\le8/15\), the concave function
\(h+\sqrt{1/2-h^2}\) lies above the affine function
\[
             h+k\ge1-\frac{73}{1000}\left(h-\frac12\right).
                                                                  \tag{5}
\]
They agree at h=1/2. At h=8/15, (5) is the positive-root comparison
\[
 k\ge\frac{13927}{30000},\qquad
 \frac{97}{450}-\left(\frac{13927}{30000}\right)^2
       =\frac{38671}{900000000}>0.
\]
Concavity proves (5) throughout the interval.

Suppose \(S+(37/50)U\ge1/8\). By (4)--(5),
\[
 \begin{split}
 4Q&\ge\left(4-\frac{73}{1000}U\right)^2
          +\left(\frac98+\frac{13}{50}U\right)^2\\
    &=4Q+\frac{U}{1000}
       +\left(\frac{5329}{1000000}+\frac{169}{2500}\right)U^2.
 \end{split}                                                \tag{6}
\]
All quantities that were squared are nonnegative. Thus U=0, and then
(4) forces S≤1/8. This proves (3), including its boundary case.

For either endpoint E, (3) implies
\[
 |y_E|\le\frac18-\frac{37}{50}\left(h_E-\frac12\right).
\]
The function \(1/(4h)+(37/50)(h-1/2)\) decreases on
\([1/2,8/15]\). Consequently
\[
 \begin{split}
 g_E-|y_E|
 &\ge\frac{15}{32}+\frac{37}{1500}-\frac18\\
 &=\frac{4421}{12000}>\frac{221}{600}.                       \tag{7}
 \end{split}
\]

## 3. Physical separation from the endpoint's inscribed square

Suppose \(x_F\ge13/12\), and let E=M3. The center bound and (2) give
\[
                   |x_F-x_E|<\rho-\frac{13}{12}=\frac{13}{30}.
                                                                  \tag{8}
\]
Replace E only by its contained axis-aligned square of halfwidth g_E.
This smaller square and F still have disjoint open interiors.

Write the absolute components of a physical side axis of F as a,b, where
\[
 a\ge b\ge0,\qquad a^2+b^2=1,\qquad
 h=\frac{a+b}{2},\quad k=\frac{a-b}{2}.
\]
The separating-axis theorem for the inscribed square and F has only
the coordinate axes and F's physical side axes to consider. Horizontal
separation is impossible by (8), since \(g_E+h>13/30\).

Vertical separation requires \(|y_F-y_E|\ge g_E+h\).
For a physical side normal n of F, the separating inequality and (8)
imply
\[
 |y_F-y_E|\ge g_E+
       \frac{1/2+(g_E-13/30)|n_x|}{|n_y|}.                 \tag{9}
\]
A zero vertical component would be impossible by (8). Of the component
ratios a/b and b/a, the latter gives the smaller right side: for any
δ≥0,
\[
 \frac{1/2+\delta a}{b}\ge\frac{1/2+\delta b}{a}
\]
when b>0, and the b=0 case uses the vertical axis directly.

Since \(g_E\ge15/32\), put
\[
 \delta=\frac{15}{32}-\frac{13}{30}=\frac{17}{480},\qquad
 c=\frac{221}{600},\qquad
 m=\min\left\{h,\frac{1/2+\delta b}{a}\right\}.
\]
Every possible separating axis therefore implies, by (7),
\[
                  |y_F|\ge c+m.                         \tag{10}
\]
Only physical disjointness was used here; no coordinate separation of
F and E was assumed.

## 4. Reduction to one scalar corner bound

For any square with center magnitudes X,Y,
\[
 q\ge\min\{(X+h)^2+(Y+k)^2,(X+k)^2+(Y+h)^2\}.             \tag{11}
\]
Both expressions increase in nonnegative X,Y. We may therefore substitute
the lower bounds \(X=13/12\), \(Y=c+m\) before taking the minimum.
Moreover
\[
 c+m\le c+h\le\frac{221}{600}+\frac1{\sqrt2}
       <\frac{221}{600}+\frac{71}{100}<\frac{13}{12}.
\]
The second expression is the smaller one, so (8)--(11) give
\[
 q\ge\left(\frac{13}{12}+k\right)^2+(c+m+h)^2.             \tag{12}
\]

If k≤δ, then m=h. Also
\[
 h^2\ge\frac12-\left(\frac{17}{480}\right)^2
        >\left(\frac{12}{17}\right)^2;
\]
the positive numerator in the last comparison is 31679 after multiplying
by \(230400\cdot289\). Hence
\[
 c+2h>\frac{221}{600}+\frac{24}{17}
       =\frac{89}{50}+\frac1{10200},
\]
and (12) gives
\[
 q>\left(\frac{13}{12}\right)^2+\left(\frac{89}{50}\right)^2
   =Q+\frac{36871}{1440000}>Q.                            \tag{13}
\]

It remains to treat k≥δ, when
\(m=(1/2+\delta b)/a\). Set
\[
 t=\frac ba\in[0,1],\qquad J=\sqrt{1+t^2}.
\]
Then
\[
 h=\frac{1+t}{2J},\quad k=\frac{1-t}{2J},\quad
 m=\frac J2+\delta t.
\]
The right side of (12) is
\[
 F(t)=A_0+A_1t+A_2t^2+\frac{N(t)}{\sqrt{1+t^2}},           \tag{14}
\]
where all coefficients are rational:
\[
 \begin{gathered}
 A_0=\frac{921341}{360000},\qquad
 A_1=\frac{75757}{144000},\qquad
 A_2=\frac{57889}{230400},\\
 N(t)=\frac{17}{480}t^3+\frac{323}{800}t^2
                     -\frac{773}{1200}t+\frac{91}{50}.
 \end{gathered}                                          \tag{15}
\]
The expansion uses the identity
\[
 (1-t)^2+(2+t+t^2)^2=(1+t^2)(t^2+2t+5).
\]

## 5. Exact scalar estimate on the whole orientation interval

We prove
\[
                      F(t)>Q+\frac3{2000}
                         \quad(0\le t\le1).             \tag{16}
\]

### 5.1. F decreases up to t=1/4

Direct differentiation gives
\[
 F'(t)=A_1+2A_2t+\frac{P_1(t)}{(1+t^2)^{3/2}},
\]
\[
 P_1(t)=\frac{17}{240}t^4+\frac{323}{800}t^3
         +\frac{17}{160}t^2-\frac{81}{80}t-\frac{773}{1200}.
\]
For \(0\le t\le1/4\), the sum of the three positive terms, divided
by t when t>0, is at most
\[
 \frac{17}{15360}+\frac{323}{12800}+\frac{17}{640}
       =\frac{4063}{76800}<\frac1{16}.
\]
The same resulting bound is valid at t=0. Thus
\[
 P_1(t)\le-\frac{773}{1200}-\frac{19}{20}t<0.
\]
On this interval \((1+t^2)^{3/2}<11/10\); indeed
\((17/16)^3<(11/10)^2\). Using
\(A_1<53/100\) and \(2A_2<51/100\),
\[
 \begin{split}
 F'(t)&<\frac{53}{100}+\frac{51}{100}t
       +\frac{10}{11}\left(-\frac{773}{1200}-\frac{19}{20}t\right)\\
       &=-\frac{367}{6600}-\frac{389}{1100}t<0.
 \end{split}                                            \tag{17}
\]

### 5.2. A uniform convexity bound from t=1/4 onward

Another direct derivative gives
\[
 F''(t)=2A_2+\frac{P_2(t)}{(1+t^2)^{5/2}},
\]
\[
 P_2(t)=\frac{17}{240}t^5+\frac{17}{96}t^3
       +\frac{2589}{800}t^2+\frac{429}{200}t-\frac{81}{80}.
\]
This polynomial is increasing for t≥0. At t=1/4, discarding its
two positive odd-power terms gives
\[
 P_2(1/4)>\frac{2589}{12800}+\frac{429}{800}-\frac{81}{80}
        =-\frac{3507}{12800}>-\frac3{10}.
\]
When P2 is negative, division by \((1+t^2)^{5/2}\ge1\) increases
it; when P2 is nonnegative, its quotient is nonnegative. Since
\(2A_2>1/2\), throughout \([1/4,1]\) we obtain
\[
                             F''(t)>\frac15.             \tag{18}
\]

### 5.3. Exact value and derivative at t=1/2

Substitution in (14)--(15) gives
\[
 F(1/2)=\frac{66473609}{23040000}
                       +\frac{10261}{3200\sqrt5}.
\]
Since \(\sqrt5<161/72\),
\[
 \begin{split}
 F(1/2)-Q-\frac1{400}
 &>\frac{66473609}{23040000}+\frac{92349}{64400}
                         -Q-\frac1{400}\\
 &=\frac{829849}{3709440000}>0.                           \tag{19}
 \end{split}
\]
The derivative is
\[
 F'(1/2)=\frac{895501}{1152000}-\frac{5131}{3000\sqrt5}.
\]
Its first term lies strictly between 77/100 and 39/50. Its second
term lies strictly between 19/25 and 77/100: use
\(20/9<\sqrt5<9/4\), and note
\(5131/6750>19/25\) and \(46179/60000<77/100\).
Therefore
\[
                              0<F'(1/2)<\frac1{50}.       \tag{20}
\]

For \(t\in[1/4,1]\), integrating (18), or completing the square in
the resulting quadratic lower bound about 1/2, yields
\[
 \begin{split}
 F(t)&\ge F(1/2)+F'(1/2)(t-1/2)+\frac1{10}(t-1/2)^2\\
     &\ge F(1/2)-\frac52\bigl(F'(1/2)\bigr)^2\\
     &>Q+\frac1{400}-\frac1{1000}
       =Q+\frac3{2000}.
 \end{split}                                            \tag{21}
\]
For \(0\le t\le1/4\), (17) gives \(F(t)\ge F(1/4)\), so the same
bound follows. This proves (16) without orientation sampling.

## 6. Conclusion and precise scope

Equations (12)--(16) contradict q≤Q whenever x_F≥13/12. Reflection
in the y-axis treats x_F≤−13/12, proving (1).

Thus an unrestricted nine-square packing that has an actual horizontal
four-chain has all five remaining centers in the open strip
\(-13/12<x<13/12\). The four main frames are already nearly aligned by
their actual-chain bounds, while the five remaining frames are completely
free. The proof establishes a genuine geometric barrier that previously
required a coordinate-cover assumption.

This strip theorem does not itself provide coordinate separators among
the five outsiders, nor between them and the two internal main squares.
It therefore does not yet prove the unrestricted nine-square lower bound
or a terminal-or-one-exception extraction. Those further implications
must still retain all five physical outsiders.

