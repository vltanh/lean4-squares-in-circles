# A downward transfer retaining the central center cost

November 2, 2026 UTC / November 1 America/Chicago. Complete hand derivation
of the stated conditional geometric inequality. No mathematical program,
numerical search, Lean, Lake, or CI is used. The scalar estimates below
are displayed rational comparisons and derivatives on whole intervals.

Put
\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 a=46,\quad b=\frac{27}{2},\quad k=\frac{207}{16},
 \quad T=\frac{211}{4},\quad \mu=\frac{k}{b}=\frac{23}{24},
 \quad c=\frac7{60}.
\]
For a physical unit square S let H_S(v) be its centered support
halfwidth in vector direction v, and let h_S=H_S(e_x)=H_S(e_y).

## 1. Statement

Let M,A,B be physical unit squares with disjoint open interiors. Assume
M and A are contained in the centered disk of radius R<=r, and
\[
 y_A-y_M\ge h_A+h_M.                                      \tag{1}
\]
Assume a genuine separating normal from A toward B is proportional to
(1,-z), with z>=0:
\[
 (1,-z)\cdot(c_B-c_A)\ge H_A((1,-z))+H_B((1,-z)).           \tag{2}
\]
Finally assume the whole central square B lies above y=c:
\[
                         y_B-h_B\ge\frac7{60}.           \tag{3}
\]
Then
\[
 \boxed{a(-x_M-h_M)+b\left(\frac12-x_B\right)\le T.}       \tag{4}
\]
The inequality is strict if R<r or z>0. If z=0 and equality holds,
B is coordinate-aligned. The whole floor in (3) is essential to this
proof; (1) remains an actual vertical projection comparison.

Unlike the earlier transfer, (4) retains no negative h_B term. Two
reflected copies can therefore be added using the central square's
actual center without separately minimizing its two orientations.

## 2. The physical support reduction and its exact orientation cost

The support reduction in
`DOWNWARD_THREE_SQUARE_CAP_FLOOR_ONE_TENTH_HAND_PROOF.md` applies with
the stronger whole floor c. Set t=bz. Before estimating B's orientation
it gives
\[
\begin{aligned}
 a(-x_M-h_M)+b(-x_B-h_B)
 \le{}&R\left(\sqrt{a^2+k^2}+bL_2\right)-bcz\\
      &-P_M-P_A-P_B,                                    \tag{5}
\end{aligned}
\]
where
\[
 L_1=\sqrt{1+z^2},\qquad L_2=\sqrt{1+(\mu+z)^2},
\]
\[
 P_M\ge a+k,\qquad
 P_B=b\{(1+z)h_B+H_B((1,-z))\},
\]
and the triangle bounding-rectangle minimum gives
\[
 \frac{P_A}{b}\ge\min\{E,N,D\},\qquad
 E=1+\mu+z,\quad
 N=L_1+\frac{\mu(1+z)}{L_1},\quad
 D=L_2+\frac\mu{L_2}.                                   \tag{6}
\]
These are the three physical edge-alignment cases of that triangle;
the ownership and orientation of A are not restricted.

Here a sharper two-vector bound is useful:
\[
 z h_B+H_B((1,-z))
 \ge\frac12\left(L_1+\frac{z(1+z)}{L_1}\right)
 =\frac12+z-d(z),                                       \tag{7}
\]
where
\[
 d(z)=\frac12\left(1+2z-\frac{1+z+2z^2}{\sqrt{1+z^2}}\right).
                                                                  \tag{8}
\]
For completeness, for two vectors v,w of lengths L>=M the minimum
of H_S(v)+H_S(w) over unit-square orientations is
\[
 \frac12\left(L+
       \frac{|v\cdot w|+|\det(v,w)|}{L}\right).
\]
The minimum occurs at a side alignment with one of the two vectors:
between alignment breakpoints the nonnegative expression has second
derivative equal to its negative. The difference between the two
alignment candidates is (L-M)(|cos alpha|+|sin alpha|-1)/2>=0.
Apply this with v=(1,-z), w=z e_y; their dot/determinant absolute
sum is z(1+z). This proves (7), including z=0.

Consequently
\[
 P_B\ge b(1+z)+b(h_B-1/2)-b d(z).                       \tag{9}
\]
Using the identities
\[
 r\sqrt{1+\mu^2}-(1+\mu)=\frac{353}{384},\qquad
 r\left(\sqrt{a^2+k^2}+b\sqrt{1+\mu^2}\right)
                  -(a+b+2k)=T,
\]
the reduction proves (4) if each of the three normalized reserves
\[
 \Delta_m(z)=m(z)-(1+\mu)+(1+c)z
             -r\left(L_2-\sqrt{1+\mu^2}\right),
 \qquad m=E,N,D,                                       \tag{10}
\]
satisfies Delta_m(z)>=d(z). We prove strictness for z>0.

## 3. Two elementary bounds for d

For every z>=0,
\[
                  d(z)\le z/2,\qquad d(z)<1/4.           \tag{11}
\]
For the first bound, the left side of (7), before minimization, is
at least z/2+1/2: h_B>=1/2 and H_B((1,-z))>=L_1/2>=1/2.
The same lower bound holds for its orientation minimum.

For the second, square the positive sides of
\[
 \frac{1+z+2z^2}{\sqrt{1+z^2}}>\frac12+2z.
\]
The exact squared difference is
\[
 (2z^2+z+1)^2-(1+z^2)(2z+1/2)^2
                    =2z^3+\frac34z^2+\frac34>0.
\]

## 4. The E branch

Delta_E=(2+c)z-r(L_2-L_2(0)) is concave, vanishes at zero,
and is strictly increasing, since 2+c-r>0. At z=1/2 use
\[
 r<\frac{133}{64},\qquad
 \sqrt{1801}<\frac{85}{2},\qquad
 \sqrt{1105}>\frac{166}{5}
\]
to get
\[
 \Delta_E(1/2)-1/4
 >\frac{97}{120}-\frac{133}{64}\frac{93}{240}
 =\frac{47}{15360}>0.                                  \tag{12}
\]
Concavity gives Delta_E(z)>z/2 for 0<z<=1/2. For z>=1/2,
monotonicity gives Delta_E(z)>1/4. Thus (11) proves this branch
strictly for every z>0; at zero both relevant quantities vanish.

## 5. Reduce the N branch to D except on a short interval

The two positive quantities N and D satisfy
\[
 (N^2-D^2)L_1^2 L_2^2
 =\mu^2\left(2z^3+\frac{17}{6}z^2+
                       \frac{1105}{288}z-1\right).       \tag{13}
\]
For a direct expansion, set w=z+mu and C=1+mu. Then the left side is
\[
 (C+zw)^2(1+w^2)-(C+w^2)^2(1+z^2)
 =\mu^2\{(1+\mu)(2z+\mu-1)+w^2(2z-1)\},
\]
which expands to (13). The cubic is increasing for z>=0 and its
value at 1/4 is 193/1152>0. Hence N>D for z>=1/4.

On [0,1/4], Delta_N is strictly concave. Indeed
\[
 N''=\frac{(1-\mu)+(1+2\mu)z^2-3\mu z}{(1+z^2)^{5/2}}
       \le\frac{43}{192},
\]
where a negative numerator only strengthens the bound. On this
interval L_2<8/5 and r>2, so
\[
 \Delta_N''=N''-\frac r{L_2^3}
               <\frac{43}{192}-\frac{125}{256}<0.
\]
Also Delta_N(0)=0. At 1/4,
\[
 \Delta_N(1/4)-\frac18
  =\frac{687}{640}+\frac{217}{24\sqrt{17}}
                         -\frac{r\sqrt{1417}}{24}
  >\frac{687}{640}+\frac{217}{99}-\frac{15029}{4608}
  =\frac{977}{253440}>0.                                \tag{14}
\]
Here sqrt17<33/8, sqrt1417<113/3 and r<133/64; all are
positive-root comparisons. Concavity gives Delta_N(z)>z/2>=d(z)
for 0<z<=1/4. Above 1/4, (13) reduces this branch to D.

## 6. The D branch: a uniformly positive scalar function

Subtracting (8) from Delta_D gives
\[
 \Delta_D-d
 =\frac{161}{384}+cz-(r-1)L_2+\frac\mu{L_2}
                   +L_1+\frac{z-1}{2L_1}.
\]
Since r-1<69/64, it is strictly greater than
\[
 F(z)=\frac{161}{384}+\frac7{60}z-\frac{69}{64}L_2
                       +\frac\mu{L_2}+L_1+\frac{z-1}{2L_1}.
                                                                  \tag{15}
\]
We prove F(z)>0 for all z>=0, without sampling.

### 6.1. A curvature bound on [0,1]

Put w=mu+z. Differentiation gives
\[
 F''(z)=A(w)+\frac{3(1-z)}{2(1+z^2)^{5/2}},\qquad
 A(w)=\frac{161w^2-391}{192(1+w^2)^{5/2}}.               \tag{16}
\]
A is increasing for mu<=w<=mu+1: its derivative has the sign
of w(2277-483w^2), which is positive because w<2. The following
rational interval bounds establish F''>1/50 throughout [0,1]:

| z interval | lower bound on A(mu+z) | lower bound on the other term |
|---|---:|---:|
| [0,1/2] | -1/4 | 48/125 |
| [1/2,3/4] | -1/50 | 384/3125 |
| [3/4,9/10] | 0 | 1/40 |
| [9/10,1] | 1/50 | 0 |

The bounds on A follow by monotonicity and these explicit anchors:
\[
 A(23/24)=\frac{-10083384}{1221025\sqrt{1105}}>-\frac14,
\]
\[
 A(35/24)=\frac{-2015352}{3243601\sqrt{1801}}>-\frac1{50},
 \qquad A(41/24)>0,
\]
\[
 A(223/120)=\frac{21383721000}{4112528641\sqrt{64129}}
                         >\frac1{50}.                  \tag{17}
\]
Use sqrt1105>166/5, sqrt1801>42, and sqrt64129<254.
For the last comparison the integer cross-products are
\[
 50\cdot21383721000=1069186050000
 >1044582274814=254\cdot4112528641.
\]
The other-term bounds use, respectively,
(5/4)^(5/2)<(5/4)^3, the exact value
(25/16)^(5/2)=3125/1024, and 2^(5/2)<6.
Every row's sum exceeds 1/50, as required.

### 6.2. One rational anchor controls the whole unit interval

At z0=5/8, (15) and its derivative simplify to
\[
 F(z_0)=\frac{63}{128}+\frac{77}{8\sqrt{89}}
                           -\frac{8671}{256\sqrt{505}},
\]
\[
 F'(z_0)=\frac7{60}+\frac{861}{89\sqrt{89}}
                         -\frac{829863}{32320\sqrt{505}}.\tag{18}
\]
The positive-root bounds
\[
 \frac{9433}{1000}<\sqrt{89}<\frac{4717}{500},\qquad
 \frac{2809}{125}<\sqrt{505}<\frac{22473}{1000}
\]
give
\[
 F(z_0)>
 \frac{63}{128}+\frac{9625}{9434}-\frac{1083875}{719104}
 =\frac1{200}+\frac{14905879}{84800339200}>\frac1{200}.
                                                                  \tag{19}
\]
They also give the easy fraction comparisons
\[
 \frac{41}{40}<\frac{861}{89\sqrt{89}}<\frac{513}{500},
 \qquad
 \frac{571}{500}<\frac{829863}{32320\sqrt{505}}<\frac{229}{200}.
\]
Thus -1/300<F'(z0)<1/1500, and in particular |F'(z0)|<1/300.
Integrating (16), or completing the resulting square, now gives
\[
 F(z)\ge F(z_0)+F'(z_0)(z-z_0)+\frac1{100}(z-z_0)^2
       \ge F(z_0)-25F'(z_0)^2
       >\frac1{200}-\frac1{3600}>0
 \quad(0\le z\le1).                                    \tag{20}
\]

### 6.3. F increases beyond one

Write
\[
 B(z)=\frac z{\sqrt{1+z^2}}+
                   \frac{1+z}{2(1+z^2)^{3/2}},
\]
\[
 G(w)=\frac{69}{64}\frac w{\sqrt{1+w^2}}
                     +\mu\frac w{(1+w^2)^{3/2}}.
\]
Then F'=7/60+B(z)-G(mu+z). On z>=1, B decreases to 1;
on w>=47/24, G decreases, because G'=-A(w)<0.

For 1<=z<=2,
\[
 G(w)\le G(47/24)
 =\frac{47}{\sqrt{2785}}\left(\frac{69}{64}+\frac{552}{2785}\right)
 <\frac{96115}{84160}<\frac87,
\]
using sqrt2785>263/5 and 552/2785<1/5. Also
\[
 B(z)\ge B(2)=\frac{23}{10\sqrt5}>\frac{36}{35},
\]
using sqrt5<161/72. Hence F'>7/60-4/35=1/420>0.

For all w>=0 the elementary concavity bound
w/sqrt(1+w^2)<=1-1/[2(1+w^2)] gives
\[
 G(w)\le\frac{69}{64}+\frac{161}{384(1+w^2)}.             \tag{21}
\]
If 2<=z<=3, this is at most 69/64+483/11234<9/8.
Meanwhile B(z)>=B(3)=16/(5sqrt10)>96/95>101/100, using
sqrt10<19/6. Thus F'>7/60+101/100-9/8=1/600>0.

For z>=3, (21) gives
\[
 G(w)\le\frac{69}{64}+\frac{483}{19202}<\frac{67}{60},
\]
while B(z)>=1. Therefore F'>0 here too. Together with (20),
this proves F>0 everywhere and completes the D branch.

## 7. Finish the transfer and state its caller exactly

Sections 4--6 prove all three reserves in (10) dominate d(z),
strictly for z>0. Insert (9) into (5), and use these reserves.
The resulting bound is
\[
 a(-x_M-h_M)+b(1-x_B-h_B)
                       \le T-b(h_B-1/2),
\]
which is exactly (4). A containing radius R<r makes the positive
disk-support step strict. At z=0, (7) becomes h_B>=1/2, so equality
requires h_B=1/2.

Suppose an actual horizontal four-chain has three additional physical
units L,C,R, each shoulder is actually above its matched outer main,
the central unit has whole floor at least 7/60, and the separating
normals from C toward L,R point upward (with either slope zero allowed).
Apply (4) on the left and its horizontal reflection on the right.
Adding gives
\[
 46(x_{M_3}-x_{M_0}-h_{M_0}-h_{M_3})+\frac{27}{2}
                              \le\frac{211}{2}.
\]
The actual four-chain makes the left side at least211/2. Strict
subcritical radius is impossible. At Q, a positive separating slope
is impossible; two zero slopes give an actual parallel three-chain.

Thus this closes the remaining same-sign downward-transfer case for
**all** slopes under the stated whole floor and actual vertical endpoint
premises. In the bounded-inner actual-four configuration, the central
adjacent-proxy barrier gives the stronger floor109/930>7/60; its caller
is recorded separately. This theorem does not convert an oblique
shoulder-to-main separator into the actual comparison (1), nor does it
close unrestricted A.2 by itself.
