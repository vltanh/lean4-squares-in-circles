# The free negative C4 endpoint cannot have a radial far endpoint

**Status: complete full-window hand exclusion; root and separate
independent full hand and exact rational audits passed.**

Use the unchanged selected physical certificate throughout
\[
                        79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
Let H--A--B--C--H be an actual physical four-cycle. A and B each have
exactly two positive pair neighbors and positive total circle loads.
A has one physical circle corner z_A with positive weight. B and C
physically touch the circle, and H may retain arbitrary additional
positive forces. Assume
\[
                              c_H\cdot z_A<0
\tag{2}
\]
and that HA is a genuinely free point contact. Every original force,
physical square, shared mean and individual zero circle weight remains.

**Theorem.** C cannot have two physical circle corners. For the
triangle-attached C4 this closes the entire free-HA portion of the
SUS mask, in the order (B,A,C), throughout the full radius interval.
No force equation at C or H is used.

## 1. The complete free-contact module

The negative-pressure point bound gives |c_H|²<3/5, so every H
point has norm<3/2<R. Thus H is physically clear, as required by
the module source. A/B retain their positive total circle loads;
individual radial weights have not been assumed positive.
NEGATIVE_ENDPOINT_FREE_SHARED_RADIAL_MODULE.md applies with exactly
these premises. Its independent full scope audit gives, after the
actual physical rotation and possible reflection,
\[
 \begin{gathered}
 q=R^2,\quad N=\sqrt{q-9/4},\quad T=\sqrt{q-1/4},\quad d=T-1,\\
 A=[N-1,N]\times[1/2,3/2],\qquad z_A=(N,3/2),\\
 B=[d,d+1]\times[-1/2,1/2],\\
 Q=H\cap A=(N-1,1/2),\qquad P=B\cap C=(d,-1/2).
 \end{gathered}
\tag{3}
\]
The AB interval is genuinely shared. Both original B circle weights
are strictly positive, and BC is a physical singleton. The unchanged
H-to-A normal is \((u,v)\), with
\[
                                  u\ge v>0.
\tag{4}
\]
It strictly exposes Q on H. This is a feature theorem in the common
preselected certificate, not a resetting of an actual mean.

The exact endpoint comparisons give
\[
 \frac{321}{250}<N\le\frac{23}{16},\qquad
 \frac{91}{100}<d<\frac{61}{60},\qquad
                 \Delta:=T-N>\frac{23}{40}>\frac12.
\tag{5}
\]
For the first lower bound,
\[
 (79/40)^2-9/4-(321/250)^2=1969/1000000>0.
\]
For d, the lower squared margin is
\((79/40)^2-1/4-(191/100)^2=101/40000>0\).
The function T-N decreases with q. At the upper endpoint it is
\((\sqrt{1041}-23)/16>23/40\), since
\(1041-(161/5)^2=104/25>0\).

## 2. The entire physical radial-pair contact fixes C

Suppose C has two physical circle corners. It is an actual radial
side-normal square, independently of whether either of its individual
circle weights is zero. The complete two-radial-boundary-unit contact
classification in BOWTIE_TIP_OWNED_PRESSURE.md, Section6, says that
the contact is at the two inner vertices. Its geometric proof uses
only containment, physical circle contact, the acute boundary-pair
corner directions and actual disjointness. It uses no tip degree or
force equation.

Apply that classification to the actual point P in (3). Define
\[
 E=\frac{4d^2-1}{4d^2+1},\qquad
 F=\frac{4d}{4d^2+1},\qquad
 e=(E,-F),\qquad t=(-F,-E).
\tag{6}
\]
Then
\[
               E^2+F^2=1,\quad 0<E<F,\qquad
                        C=P+[0,1]e+[0,1]t.
\tag{7}
\]
The alternative reflected radial pose would use B's upper inner
vertex, whereas the actual BC point is its lower inner vertex P.
Thus (7) covers the full physical C mask in this module.

In particular every C point has y<=-1/2, with equality only at P.
Its exact inward radial minimum support is
\[
                              \min_{x\in C} e\cdot x=e\cdot P.
\tag{8}
\]
The uniform comparisons in (5)--(6) also give
\[
 \frac12<E<F,\qquad F>\frac34,\qquad
 \frac EF=d-\frac1{4d}>\frac{5781}{9100}.
\tag{9}
\]
Indeed E>1/2 follows from d>91/100>sqrt(3)/2. The function F(d)
decreases for d>1/2, and
\[
       F(61/60)-3/4=3660/4621-3/4=777/18484>0.
\]
The increasing ratio d-1/(4d) has value5781/9100 at91/100.
Finally its value at61/60 is2821/3660<1, proving E<F.

## 3. Actual return contact forces the downward H vertex frame

Q is a strict support vertex of H for (u,v) in (4). Because H
physically touches C, H must reach y<=-1/2. If Q is not its strict
top vertex, at most one inward edge from Q points downward, and
the entire downward span is at most one. Since Q_y=1/2, H could
then reach C only at y=-1/2, hence only at P.

Equality of that span forces the downward edge to be vertical.
Its perpendicular inward edge must point left: an edge pointing
right would have positive dot product with (u,v), contradicting
strict exposure of Q. The whole bottom side of H would then have
x<=Q_x=N-1<d=P_x. It cannot contain P. The same argument covers
an inward horizontal edge and every side-axis endpoint.

Consequently Q is the strict top vertex of H, with inward frame
\[
                  h_1=(c,-s),\qquad h_2=(-s,-c),
             \qquad c,s>0,\qquad c^2+s^2=1.
\tag{10}
\]
Strict exposure by the original normal (u,v) gives
\(uc-vs<0\). Using u>=v yields
\[
                             0<c<s,\qquad c<1/\sqrt2.
\tag{11}
\]
No angle or contact normal is changed.

Its actual center is
\[
        c_H=(N-1,1/2)+\tfrac12(c-s,-s-c).
\tag{12}
\]
The negative premise (2) is exactly
\[
 \Phi(N,c):=N^2-N+\frac34
       +\frac12\left[(N-\tfrac32)c
                    -(N+\tfrac32)\sqrt{1-c^2}\right]<0.
\tag{13}
\]

## 4. The negative projection forces c<2/3 on the whole radius interval

For every N>=321/250 and 0<=c<=1/sqrt(2),
\[
          \Phi_N=2N-1+\tfrac12(c-\sqrt{1-c^2})>0.
\tag{14}
\]
For c>=2/3 the derivative
\[
       \Phi_c=\tfrac12(N-\tfrac32)
              +\tfrac12(N+\tfrac32)\frac{c}{\sqrt{1-c^2}}
\tag{15}
\]
is positive: N>1 and c/sqrt(1-c^2)>=2/sqrt(5)>4/5
already suffice.

If c>=2/3, monotonicity (14)--(15), the exact lower N in (5),
and \(\sqrt5<56/25\) would give
\[
 \begin{split}
 \Phi(N,c)&>\Phi(321/250,2/3)\\
 &>(321/250)^2-321/250+3/4
       +(321/250-3/2)/3
       -(321/250+3/2)\,(56/25)/6\\
 &=103/31250>0.
 \end{split}
\tag{16}
\]
The radical comparison has squared margin11/625>0.
This contradicts (13). Therefore
\[
                                  0<c<2/3.
\tag{17}
\]

## 5. Every such H lies strictly short of C's radial support

Use the actual direction e in (6). Relative to Q, the exact maximum
e-projection on H is
\[
 \begin{split}
 L(c)&=\max_{x\in H}e\cdot(x-Q)\\
     &=Ec+Fs+\max\{0,Fc-Es\}\\
     &\le\max\{1,W(c)\},\\
 W(c)&=(E+F)c+(F-E)\sqrt{1-c^2}.
 \end{split}
\tag{18}
\]
The first branch is at most one by Cauchy. For 0<=c<=2/3,
\[
 W'(c)=E+F-(F-E)\frac{c}{\sqrt{1-c^2}}>2E>0,
\]
using E<F and c/sqrt(1-c^2)<1. Thus
\[
                  L(c)\le\max\{1,W(2/3)\},\qquad
 W(2/3)=\frac{(2-\sqrt5)E+(2+\sqrt5)F}{3}.
\tag{19}
\]

But the unchanged displacement P-Q=(Delta,-1) has
\[
                              D:=e\cdot(P-Q)=E\Delta+F>1
\tag{20}
\]
by Delta>1/2, E>1/2 and F>3/4. It also exceeds the second
quantity in (19). Since E-F<0 and sqrt(5)<9/4,
\[
 \begin{split}
 D-W(2/3)
 &=\frac{E(3\Delta-2+\sqrt5)+F(1-\sqrt5)}3\\
 &>\frac{F}{12}\left[(12\Delta+1)\frac EF-5\right]\\
 &>\frac{F}{12}\left[\frac{79}{10}\frac{5781}{9100}-5\right]
   =\frac{F}{12}\frac{1699}{91000}>0.
 \end{split}
\tag{21}
\]
All comparisons hold simultaneously on the entire radius interval.
Combining (8),(18)--(21) gives the strict physical separator
\[
                    \max_{x\in H}e\cdot x
                        <e\cdot P
                        =\min_{x\in C}e\cdot x.
\tag{22}
\]
Thus H and C cannot physically touch. This contradicts the actual
four-cycle and proves the theorem.

## 6. Full scope and the remaining free-contact family

The module source first forces a radial B with both original circle
weights positive, regardless of C's initial physical mask. The present
whole-window argument excludes its entire radial-C alternative.
No C force or torque equation, H degree reduction, root/petal force
replacement, canonical motion, mean reset or positive-weight
assumption at C enters (6)--(22).

For the triangle-attached ABC orbit, all free-HA masks are now
excluded except SUU in the order(B,A,C). Its remaining exact module
has B physically radial with both weights positive and C physically
unique. That whole residual still requires a proof. The other
H-owned, A-owned and shared-HA families remain subject to their
separately stated full-radius/high-radius theorems.

The seven displayed rational margins were independently reconstructed
in exact integer arithmetic by the root; none is based on sampled
orientations or numerical interval coverage. No Lean compilation
or CI is used.
