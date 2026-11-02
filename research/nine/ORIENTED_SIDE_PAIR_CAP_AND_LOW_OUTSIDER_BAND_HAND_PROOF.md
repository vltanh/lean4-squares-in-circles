# An oriented side-pair cap and a wider low-center outsider band

November 2, 2026. Hand derivation. No Lean, CI, or computational proof
certificate. Exploratory scalar evaluations tested candidate directions;
all accepted inequalities below are proved on their full intervals.

Put
\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 l=\frac{29}{60},\quad u=\frac{13}{12},\quad
 v=\frac45,\quad \eta=\frac{37}{100}.
\]
We use \(r<133/64\), since \(133^2-16\cdot1105=9\).
The established center bound is \(|c|<\rho=91/60\).

## 1. Every low outsider has horizontal center magnitude below 47/80

Suppose physical units in the closed Q-disk contain an actual horizontal
four-chain \(M_0<_xM_1<_xM_2<_xM_3\). Every physical outsider F
with
\[
                            |y_F|\le\frac9{16}
\]
satisfies
\[
                         \boxed{|x_F|<\frac{47}{80}.}       \tag{1}
\]
No orientation or projection-separation condition is imposed on F.

For the right endpoint E=M3, the established endpoint budget gives
\[
 x_E<\frac{91}{60},\qquad
 g_E\ge\frac{15}{32},\qquad
 g_E-|y_E|>\frac{221}{600},
\]
where E contains the aligned square of halfwidth g_E. The centered
radius-1/2 disk of F is disjoint from the interior of that aligned square.
If \(V=|y_F-y_E|\), then
\[
 V-g_E<\frac9{16}-\frac{221}{600}=\frac{233}{1200}<\frac12.
\]
The exact distance from the center of F to the aligned square therefore
gives
\[
 |x_F-x_E|\ge g_E+
 \sqrt{\frac14-\max(V-g_E,0)^2}
 >\frac{15}{32}+\sqrt{\frac14-\left(\frac{233}{1200}\right)^2}.
\]
The outsider-strip theorem places x_F<x_E. Consequently
\[
 x_F<\frac{91}{60}-\frac{15}{32}
      -\sqrt{\frac14-\left(\frac{233}{1200}\right)^2}
      <\frac{47}{80}.
\]
For the last strict comparison, the radical must exceed 221/480;
the exact squared reserve is
\[
 \frac14-\left(\frac{233}{1200}\right)^2
                 -\left(\frac{221}{480}\right)^2
 =\frac{1819}{5760000}>0.
\]
Reflection using M0 gives the lower horizontal bound. This proves (1).

## 2. An oriented asymmetric two-square cap

There do not exist two physical units U,V with disjoint open interiors
in the closed Q-disk such that
\[
 l\le x_U\le v,\qquad l\le x_V\le u,\qquad
 \eta\le y_U\le y_V,                                    \tag{2}
\]
and which admit a separating unit normal directed from U to V of the
form
\[
                  n=(-a,b),\quad a\ge0,\quad b>0,
                  \quad a^2+b^2=1.                       \tag{3}
\]
The sign in (3) is an essential hypothesis. The theorem does not exclude
the positive-horizontal-normal case. It does not require that x_V<=x_U;
the proof retains arbitrary horizontal center order.

For a centered physical unit S let H_S(w) denote its support halfwidth.
The exact two-vector orientation minimum, proved in
`TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md`, is
\[
 H_S(w)+H_S(z)\ge\frac12\left(L+
        \frac{|w\cdot z|+|\det(w,z)|}{L}\right),
 \qquad L=\max(|w|,|z|).                                 \tag{4}
\]
Also \(H_S(n)\ge1/2\) for every unit normal.

### 2.1. Reduce to 0<=a<3/5

Put \(D=v-l=19/60\). The actual separator and (2) give
\[
 b y_V\ge-Da+b\eta+H_U(n)+H_V(n).
\]
Adding H_V((0,b)), using (4), and using containment yields
\[
 r\ge Z(a):=\eta+\frac{a+b}{2}+\frac{1-Da}{b}.            \tag{5}
\]
Direct differentiation gives
\[
 Z'(0)=\frac{11}{60}>0,\qquad
 Z''(a)=\frac{\tfrac12+\tfrac52a^2-\tfrac{19}{20}a}{b^5}>0.
\]
Completing the square in the numerator leaves the positive constant
1639/4000. Hence Z increases. At a=3/5, b=4/5,
\[
 Z(3/5)=\frac{833}{400}>\frac{133}{64}>r.
\]
Thus 0<=a<3/5.

Set
\[
 t=\frac25,\qquad m=(t,b),\qquad L=|m|=\sqrt{29/25-a^2}.
\]
The dot product n.m=b^2-at is positive on this range, and
the determinant is -b(a+t)<0. Hence
\[
 |n\cdot m|+|\det(n,m)|=b(a+b)+t(b-a).                   \tag{6}
\]
Using x_U<=v and x_V>=l in the actual separator gives
\[
 m\cdot c_V\ge-Da+tl+b\eta+H_U(n)+H_V(n).                \tag{7}
\]
These endpoint choices are valid for all t>0 because the coefficient
of x_V in this rearrangement is t+a>0.

### 2.2. The normal range 2/5<=a<=3/5

Here L<=1. Equations (4), (6), and (7) imply
\[
 rL\ge N:=\frac{179}{150}-\frac{31}{60}a
                 +\frac{57}{100}b+\frac12ab+\frac12b^2.
\]
Concavity gives the chord estimate b>=1-(5/9)a^2 on a<=3/5.
The tangent bound at a^2=4/25 gives L<=27/25-a^2/2. Substitution gives
\[
 \begin{aligned}
 N-\frac{133}{64}L
 &\ge\frac{91}{4800}-\frac a{60}
                    +\frac{427}{1920}a^2-\frac5{18}a^3\\
 &\ge\frac{91}{4800}-\frac a{60}+\frac{107}{1920}a^2
 \ge\frac{43}{4800}>0.                                  \tag{8}
 \end{aligned}
\]
The last two inequalities use a<=3/5. This contradicts r<133/64.

### 2.3. The normal range 0<=a<=2/5

Here L>=1, so (4), (6), and (7) give
\[
 r\ge F(a):=\frac12+\frac A L
  +\frac{b(a+b)+(2/5)(b-a)}{2L^2},
 \quad A=\frac{52}{75}-\frac{19}{60}a+\frac{37}{100}b.     \tag{9}
\]
We prove F>52/25 on this full interval.

Put s=29/25, kappa=52/75, and D=19/60. Differentiation gives
\[
 (A/L)''=\frac{\kappa(s+2a^2)-3Dsa}{L^5}
 -\eta t^2\left(\frac1{b^3L^3}+\frac{3a^2}{bL^5}\right). \tag{10}
\]
The numerator in the first term is greater than 7/12. Its quadratic,
linear, and constant coefficients are 104/75, -551/500, and 1508/1875.
The exact discriminant comparison after subtracting 7/12 is
\[
 4\frac{104}{75}\left(\frac{1508}{1875}-\frac7{12}\right)
                      -\left(\frac{551}{500}\right)^2
 =\frac{24839}{2250000}>0.
\]
Also L>=1, L<27/25, L^5<3/2, and b>9/10. The absolute size of
the subtracted term in (10) is less than
\[
 \frac{37}{625}\left(\frac{1000}{729}+\frac8{15}\right)<\frac3{25}.
\]
Consequently
\[
                              (A/L)''>\frac{121}{450}.    \tag{11}
\]

Write the last term in (9) as
\[
 F=1+A/L+\tfrac12(a+t)f(b),\qquad
 f(b)=\frac{b-t}{b^2+t^2}.
\]
On the actual interval sqrt(21)/5<=b<=1 (in particular b>9/10),
\[
 |f'|\le\frac7{100},\qquad |f''|<\frac54,
 \qquad |b'|\le\frac49,
 \qquad |b''|<\frac{11}{8}.                              \tag{12}
\]
Indeed,
\[
 f'=\frac{-b^2+(4/5)b+4/25}{(b^2+4/25)^2},
\quad
 f''=\frac{2[b^3-(6/5)b^2-(12/25)b+8/125]}{(b^2+4/25)^3}.
\]
The first numerator lies between -1/25 and 7/100, and both denominators
are at least one. For the second, write b=1-z with 0<=z<=1/10.
The bracket is
\[
 -77/125-(3/25)z+(9/5)z^2-z^3.
\]
It is negative and exceeds -5/8. For the lower bound replace the last
two terms by (17/10)z^2, complete the square, and use
77/125+45/21250<5/8. This proves (12).

Differentiating the last product twice and using a+t<=4/5 gives
\[
 \bigl(\tfrac12(a+t)f(b)\bigr)''
 >-\frac7{225}-\frac8{81}-\frac{77}{2000}.
\]
Combined with (11), this yields
\[
 F''>\frac{121}{450}-\frac7{225}-\frac8{81}-\frac{77}{2000}
       =\frac1{10}+\frac{83}{162000}>\frac1{10}.           \tag{13}
\]

At a=0,
\[
 F(0)=\frac12+\frac{319}{60\sqrt{29}}+\frac{35}{58}
 >\frac12+\frac{319}{324}+\frac{35}{58}
 =\frac{19619}{9396}>\frac{261}{125},
\]
\[
 F'(0)=\frac{15}{58}-\frac{19}{12\sqrt{29}},
 \qquad -\frac1{25}<F'(0)<0.                              \tag{14}
\]
Use 16/3<sqrt(29)<27/5, and 19/64<433/1450=15/58+1/25.
The final value comparison has cross-product numerator reserve 19.
Integration of (13) and completion of the square give
\[
 F(a)\ge F(0)+F'(0)a+\frac1{20}a^2
       \ge F(0)-5F'(0)^2
       >\frac{261}{125}-\frac1{125}=\frac{52}{25}>r.       \tag{15}
\]
This proves the oriented cap, including the vertical-normal endpoint a=0.

## 3. A precise full-side caller: one signed branch is excluded

Suppose an actual four-chain has two right-side outsiders, both below
the corresponding internal main M2, and suppose y_M2<=3/5.
The physical clearance from the nearer main gives each outsider
y<3/5-97/100=-37/100. Reflect y, and label their positive heights
so y_U<=y_V. The side-strip 9/16 cap gives y_U<9/16. By (1),
\[
 l\le x_U<47/80<4/5,\qquad l\le x_V<u,
 \qquad 37/100<y_U\le y_V.
\]
Thus the reflected U,V cannot admit a separating normal with nonpositive
horizontal component and positive vertical component, by Section 2.

Any genuine separating normal from U to V has positive vertical
component, since their horizontal center gap is less than 3/5 and the
two support halfwidths sum to at least one. Therefore every such normal
must have **positive** horizontal component. Coordinate reflections
give the other three variants of this necessary signed condition.

This is a reduction of a physical signed-normal branch. It does not
prove y_M2>3/5: the remaining positive-horizontal-normal branch must
retain the inner main and the outer endpoint. The simple asymmetric
two-square assertion obtained by dropping (3) is false, so that missing
branch cannot be silently filled by symmetry. No A.2 or whole-root
exclusion is asserted by the present note.
