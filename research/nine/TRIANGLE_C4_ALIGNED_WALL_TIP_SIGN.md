# An aligned endpoint of the three-load C4 wall cannot send a westward force

**Status: complete whole-frame hand sign theorem and two-aligned-tip
exclusion; root and separate independent full hand audits passed.**
Use the complete same-normal domain of
TRIANGLE_C4_THREE_LOAD_PARALLEL_DOMAIN.md:
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 H-A-B-C-H,\qquad H-X-Y-H,
\tag{1}
\]
\[
 H=[-s,1-s]\times[l,l+1],\qquad
 P_A=(-s,y),\quad P_C=(-s,-w),\qquad
 \frac14<s<\frac12,\quad y,w>0,\quad y+w\le1.
\tag{2}
\]
H retains true positive degree four and the full intact X/Y petal.
A,B,C,X,Y are loaded of true degree two. The three arbitrary
completion squares, all B masks and every original shared-side mean
remain. Both wall endpoints A,C are physically unique by the cited
whole domain theorem.

**Theorem.** If the upper wall endpoint A is aligned with H, its
actual outward A-to-B unit normal g satisfies \(g_x\ge0\).
The reflected conclusion holds for an aligned C. Consequently the
entire parallel-root family in which both A,C are aligned is impossible.
This does not yet exclude the tilted-endpoint alternatives.

## 1. Exact whole-frame geometry and the actual outgoing normal

Write
\[
 S=1+s,\qquad Y=\sqrt{R^2-S^2},\qquad
 A=[-S,-s]\times[Y-1,Y],\qquad z_A=(-S,Y).
\tag{3}
\]
This is the complete aligned physical mask, including all actual
means \(Y-1\le y\le Y\). Put \(r=R-\sqrt2\). The domain theorem
gives \(r^2>5/16\), so
\[
 w\ge\sqrt{r^2-s^2}>\frac14,\qquad y<\frac34.
\tag{4}
\]
The exact radius and wall ranges imply
\[
 \frac54<S<\frac32,\qquad
 \frac54<Y<\frac53.
\tag{5}
\]
For the lower Y comparison,
\((79/40)^2-9/4-25/16=141/1600>0\). For the upper one,
\(Y^2<1105/256-25/16=705/256<25/9\).

The loaded endpoint's genuine proper concurrence is
\[
                         q_A=(-Sy/Y,y).
\tag{6}
\]
This uses its actual degree-two equations and its physical boundary
neighbor B. The root force is horizontal, whereas its unique
circle force has positive vertical component. Its other outward
normal therefore obeys \(g_y<0\).

Suppose \(g_x<0\). On the aligned square (3), the actual contact
must then be its lower-left vertex
\[
                              T=(-S,Y-1).
\tag{7}
\]
The proper relation \(T-q_A=\lambda g\), \(\lambda\ge0\),
cannot have \(\lambda=0\): equality in both coordinates would
require \(y=Y\) and \(y=Y-1\) at once. Thus \(g\) is proportional
to \((-1,-t)\), where
\[
 t=\frac{Y(y-Y+1)}{S(Y-y)}>0.
\tag{8}
\]
Here \(Y-y>Y-3/4>0\), and \(g_y<0\) implies \(y>Y-1\).
The right side of (8) strictly increases with y. Hence
\[
 0<t<t_*:=\frac{Y(7/4-Y)}{S(Y-3/4)}.
\tag{9}
\]
The upper bound is positive by (5).

Its actual support is
\[
                     h=\frac{S-(Y-1)t}{\sqrt{1+t^2}}.
\tag{10}
\]
For \(t\ge0\), this expression strictly decreases with t, since
its derivative has numerator \(-(Y-1)-St<0\).
We prove a uniform lower bound at the complete endpoint \(t_*\).

## 2. A full analytic support inequality

Put \(q=R^2=S^2+Y^2\), and define
\[
 \begin{split}
 u&=Y-\frac34,\qquad
 A_0=Y\left(\frac74-2Y\right),\qquad
 B_0=Y^2\left(\frac52-2Y\right),\\
 N(q,Y)&=qu+A_0,\\
 D_0(q,Y)&=qu^2+B_0,\\
 F(q,Y)&=16N(q,Y)^2-q^2D_0(q,Y).
 \end{split}
\tag{11}
\]
Direct substitution of \(S^2=q-Y^2\) in (9)--(10) gives
\[
 \frac{S-(Y-1)t_*}{\sqrt{1+t_*^2}}
       =\frac{N(q,Y)}{\sqrt{D_0(q,Y)}},
\tag{12}
\]
where, in the actual domain,
\[
 D_0=S^2(Y-3/4)^2+Y^2(7/4-Y)^2>0.
\tag{13}
\]
Also \(q\ge Y^2+25/16\), so
\[
 N(q,Y)\ge
 Y^3-\frac{11}{4}Y^2+\frac{53}{16}Y-\frac{75}{64}
 \ge\frac58>0.
\tag{14}
\]
The cubic on the right is strictly increasing: its derivative is
\(3(Y-11/12)^2+19/24>0\), and its value at \(Y=5/4\)
is \(5/8\).

We now prove \(F>0\) on the entire domain, without evaluating
individual poses. Its q derivatives are
\[
 \begin{split}
 F_q&=q(32-3q)u^2+32uA_0-2qB_0,\\
 F_{qq}&=(32-6q)u^2-2B_0>0
 \end{split}
\tag{15}
\]
on the enlarged rectangle
\[
              \frac{61}{16}\le q\le\frac{13}{3},
              \qquad\frac54\le Y\le\frac53.
\tag{16}
\]
Indeed \(B_0\le0\) there and \(32-6q\ge6>0\).
At \(q_*=61/16\), write \(G(Y)=F_q(q_*,Y)\).
This is a cubic with negative leading coefficient. Its second
derivative is decreasing in Y, and
\[
 G''(5/4)=-\frac{4987}{128}<0,\qquad
 G(5/4)=\frac{4709}{1024}>0,\qquad
 G(5/3)=\frac{225469}{36864}>0.
\tag{17}
\]
Thus G is concave and positive on the whole Y interval. Equations
(15)--(17) prove that F strictly increases with q throughout (16).

### 2.1. The full interval \(5/4\le Y\le3/2\)

Here the actual radius gives \(q\ge q_0=6241/1600\).
The polynomial \(F(q_0,Y)\) is concave on this whole interval.
For an explicit check, its second derivative is a convex quadratic,
and the following are its exact endpoint values:
\[
 \begin{array}{c|cc}
 Y&5/4&3/2\\ \hline
 F(q_0,Y)&
 \dfrac{25817018079}{16384000000}&
 \dfrac{91062695511}{65536000000}\\[1ex]
 F_{YY}(q_0,Y)&
 -\dfrac{169247293921}{2048000000}&
 -\dfrac{105381179521}{2048000000}.
 \end{array}
\tag{18}
\]
The negative endpoint values of that convex quadratic make it
negative throughout. The positive endpoint values of F then give
\[
                         F(q,Y)\ge F(q_0,Y)>0.
\tag{19}
\]

### 2.2. The full interval \(3/2\le Y\le5/3\)

Now \(q\ge Y^2+25/16\ge61/16\), so the same monotonicity gives
\(F(q,Y)\ge F(Y^2+25/16,Y)\).
With \(z=Y-3/2\in[0,1/6]\), the latter polynomial is exactly
\[
 \begin{split}
 &\frac{44883}{65536}
 +\frac{109215}{8192}z
 +\frac{12313}{512}z^2
 +\frac{6573}{512}z^3\\
 &\hspace{4mm}
 -\frac{1749}{128}z^4-\frac{771}{32}z^5
 -18z^6-\frac{17}{2}z^7-z^8.
 \end{split}
\tag{20}
\]
The sum of the absolute negative terms is at most \(20z^4\):
after factoring \(z^4\), use \(z\le1/6\) and
\[
 \frac{1749}{128}+\frac{771}{192}
          +\frac12+\frac{17}{432}+\frac1{1296}<20.
\]
Consequently (20) is greater than
\[
                 \frac{44883}{65536}-\frac5{324}>0.
\tag{21}
\]
This covers the whole second interval, including its endpoints.

Equations (14),(19),(21) prove from (11)--(13) that
\[
 \frac{S-(Y-1)t_*}{\sqrt{1+t_*^2}}>\frac q4
           \ge R-1,
 \qquad \frac{R^2}{4}-(R-1)=\frac{(R-2)^2}{4}\ge0.
\tag{22}
\]
All estimates apply to the entire actual curved parameter domain;
the enlarged rectangle was used only for the monotonic comparison.

## 3. Whole aligned-tip sign and its complete two-aligned consequence

By (9)--(10),(22), the actual support at T satisfies \(h>R-1\).
The unit B lies beyond this support line. Every unit square has
width at least one in every unit direction, so it would contain
a point with g projection at least \(h+1>R\), impossible in
the containing disk. Therefore \(g_x<0\) is excluded and
\[
                                  g_x\ge0.
\tag{23}
\]
No owner was assigned to the A/B edge in this argument. In particular
it retains every fixed side owner, shared-side mean and strict free
vertex normal that can occur at the lower-left vertex. Reflection
gives (23) for the aligned lower endpoint C as well.

If both A,C are aligned, let \(g_A,g_C\) point from these tips
toward B. Each has nonnegative first coordinate by (23).
The genuine B force equation would give
\[
                         F_B=\gamma_A g_A+\gamma_C g_C,
                         \qquad\gamma_A,\gamma_C>0,
\tag{24}
\]
and hence \((F_B)_x\ge0\). But every physical B circle corner is
acute to both the northwest A corner and the southwest C corner,
by ACUTE_LOADED_CONTACT_GRAPH.md, Section 2.
A vector with nonnegative first coordinate cannot be acute to both.
Thus every such corner, and the actual B resultant with any
nonnegative original weight split, has strictly negative first
coordinate. This contradicts (24).

The two-aligned-endpoint parallel-root family is therefore wholly
excluded. In every surviving same-normal family at least one endpoint
is tilted and has a strictly westward outgoing normal toward B.
For an upper tilted endpoint the strict negative vertical component
then restricts its application to the lower vertex or outer lower
face; the unique circle corner is unshareable. This is an exact
remaining feature statement, not an exclusion of those tilted
families.

Only the actual degree-two endpoint equations and the original B
equation were used. H's intact petal, its degree four, all three
extra units and all physical masks remain. No old D-leaf wall range,
radial-leaf substitution, numerical sample, Lean compilation or CI
is a premise.
