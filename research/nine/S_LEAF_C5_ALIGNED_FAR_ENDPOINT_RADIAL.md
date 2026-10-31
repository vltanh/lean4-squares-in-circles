# The far endpoint of an aligned S-leaf C5 channel is radial and both transmitters are side-normal

Date: October 26, 2026.

**Status: complete whole-aligned-domain structural theorem, accepted after
root and separate independent full-source reviews in REVIEW_S_C5_ALIGNED_RADIAL_FAR_ENDPOINT_ROOT_2026_10_26.md
and REVIEW_S_C5_ALIGNED_RADIAL_FAR_ENDPOINT_C6_2026_10_26.md.**
No contact normal or mean is selected anew.
The remaining three-extra completion problem is not claimed closed.

Keep exactly the original C5 load13 component

    A--B--V--C--U--A, with the genuine S leaf L at A,

where the original labels are A=0, B=1, V=2, C=3, U=4. The block
loads are B,C; U,V retain true unloaded degree two and A true degree
three. All nine physical units, original positive forces, physical
circle masks, individual radial weights, means and sliders remain.

Use the complete aligned-root normalization and accepted restrictions
of S_LEAF_C5_ALIGNED_CHANNEL_DIRECTION.md and
S_LEAF_C5_ALIGNED_DIRECT_NORMAL_HALFPLANE.md:

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\quad
 d=\sqrt{R^2-\frac14}-1,\quad\delta=d-1,\quad
                         0\le\delta<1/60,
\]
\[
 L=[d,d+1]\times[-1/2,1/2],\quad
 A=[\delta,d]\times[-b,a],\quad a,b\ge0,\quad a+b=1,
\]
\[
 n=(-c,s),\quad c,s>0,\quad c^2+s^2=1,\quad
 m_x\le0,\ m_y<0,\quad w_U=1,\quad h:=h_A(n)\le\delta.
\tag{1}
\]

Here n is the original A-to-C channel normal and m the original
direct A-to-B normal. Put f=Jn=(-s,-c). The true root and far
applications are

\[
 p_{AU}=(\delta,a),\quad p_{CU}=p_{AU}+n,\quad
 h=-\delta c+as,\quad t=f\cdot p_{AU}=-\delta s-ac.
\tag{2}
\]

The positive root-concurrence argument of the D-leaf source, with
nonnegative root proper lengths, gives
q_A=(q,0), q=delta+a c/s>0. In particular t=-qs<0.
If delta=0, h=as<=0 would give a=0 and q=0.
Consequently the entire actual aligned domain has

\[
                         \delta>0,\qquad R^2>17/4.
\tag{3}
\]

**Theorem.** C is physically radial. Its original U interface is
a genuine shared inner-axis side, and the entire remaining V channel
also has reserve one. More explicitly,

\[
 C=[d,d+1]n+[-1/2,1/2]f,\qquad
             p_{CU}=dn-af,\qquad h=\delta,\qquad w_V=1.
\tag{4}
\]

Both individual circle weights at C remain arbitrary nonnegative
weights with positive total. The theorem does not set them equal.

## 1. Uniform root-slider bounds from the actual B application

Write rho=R-sqrt(2). Every point of any physical boundary unit has
norm at least rho, by its actual circle corner and diameter sqrt(2).
Since d>=1, the fixed elementary comparisons

\[
 R\ge\sqrt{17}/2>2061/1000,\qquad
             \sqrt2<283/200
\]

give
\[
                           \rho>323/500.
\tag{5}
\]

Their squared reserves are respectively 2279/10^6 and 89/40000.

If m_x<0, the original direct root application is
p_BA=(delta,-b), so

\[
        \delta^2+b^2\ge\rho^2>(323/500)^2.
\tag{6}
\]

In particular b>3/5, a<2/5. A useful stronger consequence is
b>16/25, a<9/25.

If m_x=0, its actual application is instead p_BA=(q,-b), with
q<=d because it is a point of A. The exact support calculation
from Section 1 of the direct-normal theorem applies unchanged:

\[
             a^2\le d^2-1<121/3600,\qquad
                       a<11/60<1/4,\quad b>3/4.
\tag{7}
\]

Thus a<2/5 in both original alternatives. The far point in (2)
satisfies

\[
 |p_{CU}|^2=\delta^2+a^2+1+2h
 <1/3600+4/25+1+1/30
 =4297/3600<5/4\le d^2+1/4.
\tag{8}
\]

The final reserve is 203/3600.

## 2. The C interface cannot be a strict vertex

For a unit with a unique circle corner z=Xu+Yv in its own inward
frame, X,Y>1/2 and X^2+Y^2=R^2. Either adjacent-to-circle
vertex has squared norm at least

\[
 R^2+1-2\sqrt{R^2-1/4}=d^2+1/4.
\tag{9}
\]

For a physical radial unit, both inner vertices have exactly that
norm. Circle vertices themselves are unshareable. Therefore, if
the actual C application in (8) is a strict exposed vertex, C must
be physical unique and that application must be the opposite vertex.

Let u,v be its actual orthonormal inward sides from that vertex.
The original strict support gives n dot u,n dot v>0. Put

\[
 L=n\cdot(u+v),\quad T=f\cdot(u+v),\qquad
                       1\le L\le\sqrt2,\quad |T|\le1.
\]

Its circle corner is z=p_AU+n+u+v. Since h>=-delta and
|t|<=delta+a, the exact norm expansion gives

\[
 \begin{split}
 R^2
 &=\delta^2+a^2+3+2L+2(1+L)h+2Tt\\
 &\ge\delta^2+a^2+3+2L-2\delta(1+L)-2(\delta+a)\\
 &\ge\delta^2+a^2+5-6\delta-2a\\
 &=\delta^2+b^2+4-6\delta .
 \end{split}
\tag{10}
\]

In the penultimate line, combine the L terms as
2L(1-delta)>=2(1-delta), which has the required positive
coefficient. Since R^2=delta^2+4delta+17/4, (10) implies

\[
                           b^2\le1/4+10\delta.
\tag{11}
\]

For m_x=0 this contradicts b>3/4. For m_x<0 it gives
delta^2+b^2<1501/3600, contradicting (6), because

\[
             (323/500)^2-1501/3600=209/562500>0.
\tag{12}
\]

Hence C's original normal is a side axis of C. U already owns that
axis. Their supporting faces must have positive overlap: a singleton
intersection of those parallel faces would be vertex/vertex with
the selected normal a side axis, forbidden by the existing strict
point-normal convention. Thus U--C is a genuine shared interface,
including every possible actual mean endpoint.

## 3. A physical-unique C would have a uniformly long inner-side return

The fixed C frame is n,f. Its n-coordinate interval is
[X,X+1], where

\[
                         X=1+h,\qquad 1-\delta\le X\le1+\delta.
\]

Suppose C is physical unique. Its circle corner has a nonzero
f-coordinate: in this fixed axis frame physical uniqueness gives
absolute far f-coordinate greater than 1/2. Its two contact forces
therefore cannot be parallel to the incoming axis n, since their
sum could not balance that nonzero f-component. The accepted true
degree-two proper-concurrence lemma applies. Its positive concurrence q_C
has f-coordinate t<0, so its circle corner has negative
f-coordinate. Write its exact unit and circle corner as

\[
       C=[X,X+1]n+[-M,1-M]f,\qquad
       z_C=(X+1)n-Mf,\qquad M>1/2.
\tag{13}
\]

The unique circle equation is
M^2=R^2-(h+2)^2. Thus

\[
 M^2\le R^2-(2-\delta)^2=1/4+8\delta<23/60
                         <(31/50)^2.
\tag{14}
\]

The last squared reserve is 2/1875. Put T_0=-t>0.
Properness on the original inner-axis contact gives
q_C=tau z_C, tau=T_0/M and
tau(X+1)>=X. Therefore

\[
                    T_0>\frac{59}{238}.
\tag{15}
\]

Indeed X>59/60, M>1/2, and X/(X+1)>59/119.
Since T_0=delta s+ac<=delta+a, (15) first gives a>23/100.
The support inequality as<=delta(1+c) then yields
s<10/69 and delta s<1/414. Refining (15) gives

\[
 a>\frac{59}{238}-\frac1{414}>\frac{49}{200},
 \qquad s<\frac{20}{147}<\frac7{50}.
\tag{16}
\]

The close first reserve is 2383/4926600. The alternative m_x=0
is now impossible by (7), so m_x<0 and (6) gives

\[
                         49/200<a<9/25.
\tag{17}
\]

The other C force has positive f-coordinate: the positive unique
circle force has negative f-coordinate, and the force toward A
is along -n. Let g be the actual C-to-B channel normal. Its
support obeys

\[
                           h_C(g)+w_V\le d,
\tag{18}
\]

by the sharp contained-unit center bound at the actual boundary B.
If g dot n>=0, its positive f-coordinate and (13)--(14) would
give h_C(g)>19/50>delta, contradicting (18), since w_V>=1.
Thus g dot n<0 and g dot f>0. Its C port is the strict
inner-plus vertex, and diagonal avoidance rules out w_V=sqrt(2).
Consequently w_V=1 and

\[
 Q:=p_{CV}=Xn+(1-M)f,\qquad g=-\alpha n+\beta f,
       \quad\alpha,\beta>0,\quad\alpha^2+\beta^2=1.
\tag{19}
\]

Define the true local distances

\[
 v=T_0(X+1)/M-X>0,\qquad
                     \ell=1-M+T_0>0.
\tag{20}
\]

Then Q-q_C=-v n+ell f, so alpha/beta=v/ell.
The support bound also gives T_0>=a: indeed
delta s>=a(1-c). Equations (14),(16) therefore give

\[
 \ell>a+19/50>5/8,\qquad
 v<\frac{121}{30}(a+1/414)-\frac{59}{60}.
\tag{21}
\]

The ratio of the displayed affine upper bound for v to a+19/50
increases with a: its numerator has positive slope and negative
intercept. Evaluating at the whole-domain endpoint a=9/25 yields

\[
 \frac v\ell<
 \frac{74273}{114885}<\frac{13}{20},
 \qquad
 \frac{13}{20}-\frac{74273}{114885}
                         =\frac{1609}{459540}>0.
\tag{22}
\]

Hence

\[
 \alpha<\frac{13}{\sqrt{569}}<\frac6{11},
\tag{23}
\]

where the last positive squared comparison is
36*569-169*121=35.

## 4. One actual supporting half-plane excludes the entire unique-C domain

No local feature of B needs to be selected. Because its whole unit
lies beyond the actual reserve-one C-to-B channel, its original
A application satisfies

\[
                          g\cdot(p_{BA}-Q)\ge1.
\tag{24}
\]

In the n,f coordinates, p_BA=p_AU-e_y has coordinates
(h-s,t+c), while Q has coordinates (h+1,1-M).
Using the exact ell of (20), (24) becomes

\[
                         \alpha(1+s)+\beta(c-\ell)\ge1.
\tag{25}
\]

But (16),(21),(23) give

\[
 \alpha(1+s)+\beta(c-\ell)
 <\frac6{11}\frac{57}{50}+\frac38
 =\frac{2193}{2200}<1.
\tag{26}
\]

For the second term, if c-ell is negative it is already below
zero; otherwise beta<=1 and c<=1 give the stated upper bound
3/8. This records the sign needed for that estimate.
The exact contradictory reserve is 7/2200.

Thus the complete physical-unique C alternative is impossible,
with both possible B masks and all original direct-contact means
retained. C must be physical radial.

## 5. Exact radial chart and exclusion of the remaining diagonal

A radial C in the fixed n,f frame must have transverse interval
[-1/2,1/2] and X=d. Thus h=delta, and (2) gives

\[
 as=\delta(1+c),\quad \delta s=a(1-c),\quad
 p_{CU}=dn-af,\quad q=a/s.
\tag{27}
\]

Equivalently, without changing any original parameter,

\[
 a^2=2\delta q-\delta^2,\qquad
              c=1-\delta/q,\qquad s=a/q.
\tag{28}
\]

In particular a>delta>0. Its two individual radial weights remain
unrestricted.

For completeness, a diagonal channel from this radial C to any
physical boundary B is impossible at delta>0, independently of
the degree or circle-weight split of either endpoint. Original
diagonal avoidance makes the normal an axis at both endpoints.
Outer and tangential C axes are excluded by containment and width,
so its normal toward B would have to be -n.
The actual B n-interval is then

\[
               [d-\sqrt2-1,\ d-\sqrt2]
                    =[\delta-\sqrt2,\ \delta+1-\sqrt2].
\]

Both endpoints are negative. At its circle corner the larger
absolute n-coordinate is therefore delta-sqrt(2). If M_B is
the larger absolute f-coordinate of B's unit interval, then

\[
 M_B^2=R^2-(\delta-\sqrt2)^2
               =9/4+(4+2\sqrt2)\delta>9/4.
\tag{29}
\]

Thus its entire unit f-interval lies either strictly above 1/2
or strictly below -1/2. C's actual inner-axis application has
f-coordinate in [-1/2,1/2], and an exact diagonal transmission
preserves that transverse coordinate. The original two means
cannot agree, a contradiction. Hence w_V=1.

This completes (4). The local diagonal obstruction just proved
uses only a physical radial endpoint, a physical boundary endpoint,
the original diagonal endpoint axes, and d>1. No simple-cycle
force-polygon or concurrence-containment premise is needed.

## 6. Remaining original obligation

The entire aligned S-leaf load13 family is reduced to (4),(27)--(28),
the original m_x<0 or m_x=0 root alternative, and its actual side
transmitters. Every original radial weight and both actual transverse
sliders remain. This is a necessary geometry theorem; positive
six-body cores are not excluded by its conclusion.

The three-extra-square capacity and the tilted-root family still
require proofs. No original whole gate or load orbit is closed here.
No sampled sign, new normal, force deletion, replacement packing,
Lean compilation or CI is a premise.
