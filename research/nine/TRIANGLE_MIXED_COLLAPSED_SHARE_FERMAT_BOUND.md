# A strict radius-two Fermat bound for the mixed collapsed-share endpoint

Date: October 26, 2026.

**Status: complete elementary geometric inequality, accepted after root
and separate independent full-source reviews.** See
REVIEW_TRIANGLE_MIXED_COMMON_POINT_ROOT_2026_10_26.md and
REVIEW_C6_COMMON_POINT_FERMAT_BOUND_C6_2026_10_26.md.
This is a reusable endpoint bound for the remaining mixed one-share
support functional. Its required common-point join is now proved in
TRIANGLE_MIXED_ONE_SHARE_COMMON_POINT_BOUND.md, giving R<2 throughout
the original physical orbit. The endpoint alone does not supply that
join. All triangle shapes are covered without an angle or force-ratio
subdivision.

## 1. Statement

Let \(f_0,f_1,f_2\) be a nondegenerate counterclockwise triangle, let
\(J\) be counterclockwise rotation through \(\pi/2\), and put
\[
 F_i=f_{i-1}-f_i,\qquad P=\sum_i|F_i|,
\]
\[
 g_1=f_0+JF_1,\qquad g_2=f_2+JF_2.
\tag{1}
\]
Then at an original-triangle Fermat point \(o\),
\[
 \boxed{\quad
 \Psi(o):=\sum_{i=0}^2|f_i-o|+|g_1-o|+|g_2-o|
                     +\sqrt2|F_0|<2P.\quad}
\tag{2}
\]
Consequently the minimum of \(\Psi\) also satisfies (2).

This is precisely the collapsed outgoing-share endpoint of the mixed
corner word \(110\). The fixed term is the norm of
\((I+J)F_0\), so no contact mean or physical force is moved by the
statement. Section 6 specifies the missing join for a genuine mean.

## 2. A jointly convex two-force difference

For \(a,b\ge0\), define
\[
 D(a,b)=\sqrt{a^2+ab+b^2},\qquad
 E(a,b)=\sqrt{2a^2+(1+\sqrt3)ab+b^2},
\]
\[
                         G(a,b)=2D(a,b)-E(a,b).
\tag{3}
\]
On the positive quadrant,
\[
 G_{bb}=a^2\left\{\frac{3/2}{D^3}
                    -\frac{1-\sqrt3/2}{E^3}\right\}>0,
\tag{4}
\]
because \(E^2-D^2=a^2+\sqrt3ab>0\) and
\(0<1-\sqrt3/2<3/2\). Homogeneity gives
\[
 \nabla^2G=G_{bb}
   \begin{pmatrix}(b/a)^2&-b/a\\-b/a&1\end{pmatrix},
\tag{5}
\]
which is positive semidefinite. Thus \(G\) is jointly convex; continuity
extends the convexity to the closed nonnegative quadrant. In particular,
\[
 G(a,b)+G(c,b)\ge2G\left(\frac{a+c}{2},b\right).
\tag{6}
\]
Also
\[
 D(a,c)\ge\frac{\sqrt3}{2}(a+c)
\tag{7}
\]
by the square difference \((a-c)^2/4\).

## 3. One convex scalar, with an explicit positive reserve

For \(t\ge0\), put
\[
 f(t)=4\sqrt{1+t+t^2}
       -2\sqrt{2+(1+\sqrt3)t+t^2}-t
       +(2-\sqrt2)\sqrt3-2.
\tag{8}
\]
The full half-line bound is
\[
                              f(t)>\frac{19}{20000}.
\tag{9}
\]
Indeed, \(f(t)=2G(1,t)-t+(2-\sqrt2)\sqrt3-2\), so (4)
gives \(f''>0\). It is enough to verify the three fixed comparisons
\[
 f(9/20)>1/1000,\qquad
 -1/200<f'(9/20)<0,\qquad f'(23/50)>0.
\tag{10}
\]
Strict convexity puts the unique critical point in \((9/20,23/50)\).
For every \(t\) in that interval, the supporting-line inequality gives
\[
 f(t)\ge f(9/20)+f'(9/20)(t-9/20)
           >\frac1{1000}-\frac1{200}\frac1{100}
           =\frac{19}{20000}.
\]
Outside the interval, the derivative signs and convexity make \(f\)
no smaller than the relevant endpoint. This proves (9) on all \(t\ge0\).

Here are elementary fixed-radical comparisons proving (10); none is a
parameter-cell sign test. Let
\[
 S=\sqrt{1061+180\sqrt3},\qquad
 T=\sqrt{6679+1150\sqrt3}.
\]
Use
\[
 \frac{433}{250}<\sqrt3<\frac{17321}{10000},\qquad
 \sqrt6<\frac{4899}{2000},
\]
\[
 \frac{257099}{10000}<\sqrt{661}<\frac{2571}{100},
 \qquad \frac{370507}{10000}<S<\frac{370511}{10000},
\]
\[
 \sqrt{4179}<\frac{161613}{2500},\qquad
 T>\frac{931171}{10000}.
\tag{11}
\]
Every bound follows by squaring positive numbers; for nested radicals
use the displayed lower or upper bound for \(\sqrt3\). In the order
listed, the exact positive square reserves are
\[
 \frac{11}{62500},\ \frac{17041}{10^8},\ \frac{201}{4000000},\
 \frac{104199}{10^8},\ \frac{41}{10000},\
 \frac{562951}{10^8},\ \frac{601121}{10^8},\
 \frac{11769}{6250000},\ \frac{568759}{10^8}.
\tag{12}
\]
The exact scalar formulas are
\[
 f(9/20)=\frac{\sqrt{661}}5-\frac S{10}
                         +2\sqrt3-\sqrt6-\frac{49}{20},
\]
\[
 f'(9/20)=\frac{76}{\sqrt{661}}
                         -\frac{38+20\sqrt3}{S}-1,
\]
\[
 f'(23/50)=\frac{192}{\sqrt{4179}}
                         -\frac{96+50\sqrt3}{T}-1.
\tag{13}
\]
Substitution of (11), with each direction preserved, gives
\[
 f(9/20)>\frac{137}{100000}>\frac1{1000},
\]
\[
 f'(9/20)>-\frac{4346117}{952573497}>-\frac1{200},
 \qquad
 f'(9/20)<-\frac{426361189}{95258007589}<0,
\]
\[
 f'(23/50)>\frac{453107509}{50163112941}>0.
\tag{14}
\]
For the only close comparison in (14), adding \(1/200\) gives
\(83350097/190514699400>0\). Thus (10) is proved by fixed
rational arithmetic and (9) follows from global convexity.

## 4. Interior Fermat point: simultaneous force symmetrization

Let \(o\) minimize \(\sum_i|f_i-o|\). Existence follows from
continuity and coercivity. If \(o\) is not a triangle vertex,
its three unit radial vectors sum to zero, hence their successive
counterclockwise angles are \(2\pi/3\).

Translate \(o\) to zero and write
\[
                 a=|f_0|>0,\quad b=|f_1|>0,\quad c=|f_2|>0.
\]
The orientation in (1) gives
\[
 |F_0|=D(a,c),\quad |F_1|=D(a,b),\quad |F_2|=D(c,b),
\]
\[
                         |g_1|=E(a,b),\quad |g_2|=E(c,b).
\tag{15}
\]
These formulas retain the mixed second argument order; replacing
\(E(c,b)\) by \(E(b,c)\) would be incorrect.

Consequently, using (6)--(7), and writing \(m=(a+c)/2>0\),
\[
\begin{split}
 2P-\Psi(o)
 &=(2-\sqrt2)D(a,c)+G(a,b)+G(c,b)-(a+b+c)\\
 &\ge (2-\sqrt2)\sqrt3\,m+2G(m,b)-2m-b\\
 &=m f(b/m)>\frac{19m}{20000}>0.
\end{split}
\tag{16}
\]
Thus a single convex symmetrization and the scalar bound handle
all positive force magnitudes simultaneously.

## 5. Fermat point at a triangle vertex

If \(o=f_i\), the angle between the two nonzero rays is at least
\(2\pi/3\). This follows from the subgradient condition that the
sum of those two unit vectors has norm at most one; it includes
an angle exactly \(2\pi/3\).

First let \(o=f_1=0\), \(a=|f_0|>0\), \(c=|f_2|>0\),
and \(d=|F_0|\). Then
\[
 d\ge\frac{\sqrt3}{2}(a+c),\quad
 P=a+c+d,\quad
 \Psi(o)=(1+\sqrt2)(a+c)+\sqrt2d.
\]
Hence
\[
 2P-\Psi(o)
 =(2-\sqrt2)\left(d-\frac{a+c}{\sqrt2}\right)>0,
\tag{17}
\]
since \(\sqrt3/2>1/\sqrt2\).

Next let \(o=f_0=0\), \(b=|f_1|>0\), \(c=|f_2|>0\),
and \(d=|F_2|\). Then
\[
 d^2\ge b^2+bc+c^2\ge(b/2+c)^2,
\]
\[
 |g_1|=b,\qquad |g_2|=|(I-J)f_2+Jf_1|\le\sqrt2c+b.
\]
Therefore
\[
 \Psi(o)\le3b+(1+2\sqrt2)c,
\]
\[
 2P-\Psi(o)\ge2d-b+(1-2\sqrt2)c
                      \ge(3-2\sqrt2)c>0.
\tag{18}
\]
The case \(o=f_2\) is its reflected version, interchanging the
roles of \(f_0\) and \(f_2\); the same calculation gives the
strict gap \((3-2\sqrt2)|f_0|>0\). Thus all Fermat cases are
exhausted, proving (2).

## 6. Exact scope and the separate genuine-mean join

For the original mixed outgoing share, set
\(\delta=1-\ell_0\in[0,1]\) while retaining the original
forces and the original mean. With
\[
 g_0^{\rm full}=f_2+JF_0,\qquad
 g_0^\delta=g_0^{\rm full}-\delta f_0,
\]
the translated support functional is
\[
 \Phi_\delta(x)=\sum_i|f_i-x|+|g_1-x|+|g_2-x|
                         +|g_0^\delta-(1-\delta)x|.
\tag{19}
\]
At \(\delta=1\), the last term is
\(|(I+J)F_0|=\sqrt2|F_0|\), exactly giving \(\Psi\).
For any single common point \(x\), norm convexity gives
\[
 \Phi_\delta(x)\le(1-\delta)\Phi_0(x)+\delta\Psi(x).
\tag{20}
\]
The original closure makes the physical origin a minimizer of
\(\Phi_\delta\) for its fixed actual \(\delta\). However,
(2) alone does not supply a common point with
\(\Phi_0(x)<2P\), and separate endpoint minimizers cannot be
inserted into (20). The required join is proved separately in
TRIANGLE_MIXED_ONE_SHARE_COMMON_POINT_BOUND.md; it explicitly supplies
one common comparison point before applying (20).

Accordingly this source supplies the whole geometric endpoint inequality
used in that now-accepted R<2 join. Neither source proves the remaining
coordinate bounds or a three-extra-square completion exclusion. The actual nine
squares, physical masks, force positivity, means and sliders remain
unchanged wherever the result is later used. No numerical optimum,
angle grid, Lean compilation or CI is a premise.
