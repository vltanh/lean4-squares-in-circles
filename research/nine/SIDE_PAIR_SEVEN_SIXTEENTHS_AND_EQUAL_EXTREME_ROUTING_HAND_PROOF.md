# A seven-sixteenths side-pair cap and the equal-extreme full-side routing

November 2, 2026. Hand proof. One bounded exploratory evaluation checked
the candidate support direction. All accepted normal ranges, inequalities,
and rational constants are proved below; no Lean, CI, or proof script.

Put Q=1105/256, r=sqrt(Q), l=29/60, u=13/12. We use r<25/12.

## 1. A positive-normal side-pair cap at center height 7/16

There are no two interior-disjoint physical units U,V in the closed
Q-disk such that
\[
 l\le x_U,x_V\le u,\qquad 7/16\le y_U\le y_V,             \tag{1}
\]
and admitting a separating unit normal from U to V of the form
n=(a,b), a>=0, b>0, a^2+b^2=1.

Write H_S(w) for support halfwidth. The exact two-vector orientation
minimum gives
\[
 H_S(w)+H_S(z)\ge\frac12\left(K+
            \frac{|w\cdot z|+|\det(w,z)|}{K}\right),
 \qquad K=\max(|w|,|z|).                                 \tag{2}
\]
Its complete derivation is in `TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md`.
Also H_U(n)>=1/2. Set eta=7/16, t=1/2, m=(t,b), and
L=|m|=sqrt(5/4-a^2).

### 1.1. Normal range 0<=a<=1/2

Since t-a>=0, use the lower horizontal endpoint l for both centers
in the separating inequality. Adding H_V(m) and using (2) gives
\[
 r\ge F(a):=\frac12+\frac A L
             +\frac{t(a+b)+b^2-ab}{2L^2},
 \quad A=\frac{89}{120}+\eta b.                          \tag{3}
\]
Here L>=1. Put f(b)=(b-t)/(b^2+t^2). The last numerator in (3)
is L^2+(b-t)(t-a), so
\[
 F=1+A/L+G,
 \qquad G=\tfrac12(t-a)f(b).
\]
On sqrt(3)/2<=b<=1, the elementary estimates proved directly in
Section 3.1 of `FULL_SIDE_EXTREME_MAIN_THREE_FIFTHS_HAND_PROOF.md`
are
\[
 0<f\le2/5,quad 0<f'<3/8,quad b>6/7,
 \quad a(t-a)\le1/16.
\]
Consequently
\[
                      G'>-1/5-7/512>-7/32.               \tag{4}
\]
Direct differentiation gives
\[
 (A/L)'=\frac{a}{L^3}\left(\frac{89}{120}-\frac{\eta}{4b}\right).
\]
Because b>6/7 and L^3<3/2, the bracket divided by L^3 exceeds
\[
 \frac23\left(\frac{89}{120}-\frac{49}{384}\right)
 =\frac{131}{320}>\frac25.
\]
Thus (A/L)' >=(2/5)a, including a=0. Integrating this and (4)
from zero gives
\[
 F(a)\ge F(0)-\frac7{32}a+\frac15a^2
             \ge F(0)-\frac{245}{4096}.                 \tag{5}
\]
At zero,
\[
 F(0)=\frac{11}{10}+\frac{283}{120\sqrt5}
          >\frac{11}{10}+\frac{283}{270}=\frac{58}{27},
\]
using sqrt(5)<9/4. Finally,
\[
 \frac{58}{27}-\frac{245}{4096}-\frac{25}{12}
                          =\frac{553}{110592}>0.
\]
Equations (3)--(5) contradict r<25/12.

### 1.2. Normal range 1/2<=a<1

Now t-a<=0. Use x_U>=l and x_V<=u in the separator. Here L<=1,
and (2) gives
\[
 rL\ge N:=\frac{37}{24}-\frac7{20}a+\frac3{16}b
                              +\frac12ab+\frac12b^2.    \tag{6}
\]
We prove N>(25/12)L for 0<=b<=sqrt(3)/2.

For b<=7/10, the coefficient b/2-7/20 of a is nonpositive.
Use a<=1-b^2/2. This gives
\[
 N\ge\frac{143}{120}+\frac{11}{16}b+\frac{27}{40}b^2-\frac14b^3.
                                                                    \tag{7}
\]
On 0<=b<=1/4, combine (7) with L<=1/2+b^2 to obtain
\[
 N-\frac{25}{12}L
 \ge\frac3{20}+\frac{11}{16}b-\frac{169}{120}b^2-\frac14b^3
 \ge\frac3{20}+\frac{307}{960}b>0.                        \tag{8}
\]
On 1/4<=b<=7/10, use instead L<=5/8+b^2/2. The difference
is bounded below by the concave polynomial
\[
 P_1(b)=-\frac{53}{480}+\frac{11}{16}b-\frac{11}{30}b^2-\frac14b^3.
\]
Its endpoint values are
\[
 P_1(1/4)=\frac{133}{3840}>0,
 \qquad P_1(7/10)=\frac{253}{2400}>0.
\]

For 7/10<=b<=sqrt(3)/2, the coefficient of a in (6) is nonnegative.
Use the concavity bound a>=1-(2/3)b^2 and again L<=5/8+b^2/2.
Then
\[
 N-\frac{25}{12}L\ge
 P_2(b):=-\frac{53}{480}+\frac{11}{16}b-\frac{37}{120}b^2-\frac13b^3.
\]
This is concave on the larger interval [7/10,7/8], and
\[
 P_2(7/10)=\frac{253}{2400}>0,
 \qquad P_2(7/8)=\frac{61}{1920}>0.
\]
All b-ranges have now been covered. Equation (6) contradicts r<25/12,
proving the positive-normal cap (1).

## 2. A stronger side-pair cap when the actual-four endpoints are retained

Suppose an actual horizontal four-chain is present. Among the physical
units whose centers satisfy l<=x<=u, at most one can have center height
y>=7/16. The reflected statement holds below -7/16 and on the left.
The internal main square may be included among these side units.

Suppose otherwise that U,V are two such units, ordered by height.
The previously proved 9/16 side cap gives y_U<9/16. If U is an outsider,
the new low-center band gives x_U<47/80; if U is the internal main,
its actual-chain x-band gives x_U<31/60<47/80 directly.
Thus x_U<4/5 in either case.

Every separating normal from U to V has positive vertical component,
since their horizontal gap is at most 3/5 and the two supports sum to
at least one. A nonpositive horizontal component is excluded by the
oriented asymmetric cap in
`ORIENTED_SIDE_PAIR_CAP_AND_LOW_OUTSIDER_BAND_HAND_PROOF.md`, since
y_U>=7/16>37/100 and x_U<4/5. A positive horizontal component is
excluded by Section 1. This proves the stated 7/16 side-pair cap.

The outer endpoint is essential: it enters through the low-center
horizontal restriction. This result is not the false unconstrained
quadrant statement, nor the false isolated side-pair cap at height 1/2.

## 3. Both top-marker mains: exact zero-marker bands

Consider the actual-four occupancy (L,C,R)=(2,1,2), in a strict-radius
counterexample normalized to closed-disjoint units at Q. Suppose both
inner mains occupy the top markers of their respective full sides.
Write U_L,U_R for the two zero-marker outsiders, B_L,B_R for the
bottom-marker outsiders, and F for the sole central outsider.

The main-height theorem gives y_M1,y_M2>3/5. Every outsider lies below
both inner main centers, as proved in its equal-top corollary. The
near-aligned main corner bound gives |y_Mi|<27/20.

For either zero-marker unit U, the original 97/100 clearance implies
\[
 y_U<27/20-97/100=19/50<9/16.
\]
The 9/16 cap applied below to U and its bottom-marker companion gives
y_U>-9/16. Hence the low-center theorem applies and gives
\[
 l\le |x_U|<47/80.
\]
Its horizontal gap from the corresponding main is therefore less than
5/48, which is less than that main's proxy halfwidth g>15/31. The
outsider's radius-1/2 disk is disjoint from this proxy, so its vertical
center gap is at least g+1/2 and therefore greater than 61/62. Consequently
\[
 y_U<27/20-61/62=227/620.
\]
The stronger cap of Section 2, again applied below to U and its
bottom companion, improves its lower bound to -7/16. We have proved
the exact two-sided zero-marker bands
\[
 \boxed{-7/16<y_{U_L},y_{U_R}<227/620,
 \qquad 29/60\le |x_{U_L}|,|x_{U_R}|<47/80.}             \tag{9}
\]

## 4. The central outsider is below both zero-marker units

Assign F to the main in its own horizontal half-plane; at x_F=0
either assignment is valid. Because F is central, its clearance from
that main is greater than 59/60. Since it is below the main,
\[
                              y_F<27/20-59/60=11/30.     \tag{10}
\]
Let U be the zero-marker outsider on that same side. Since
|x_F|<29/60 and |x_U|<47/80, their horizontal center gap is less
than 47/80. Their inscribed disks are disjoint, so
\[
 |y_F-y_U|>\sqrt{1-(47/80)^2}>97/120.                    \tag{11}
\]
The last squared reserve is 83/57600.

If F were above U, equations (9) and (11) would give
\[
 y_F>-7/16+97/120=89/240>11/30,
\]
contradicting (10). The last difference is exactly 1/240.
Thus F is below its same-side zero unit by more than 97/120.

The two zero-marker heights differ by less than
\[
 7/16+227/620=1993/2480<97/120.
\]
It follows that F is below the other zero-marker unit as well. In
particular,
\[
 y_F<227/620-97/120=-329/744<-11/25.                      \tag{12}
\]
This is a joint nine-body routing theorem: the central outsider lies
below both zero-marker units, and its center belongs to the lower cap.

## 5. The two bottom-marker outsiders also have low centers

Each bottom-marker unit B has y_B<=-1+h_B<=-1+1/sqrt(2)<0.
Suppose y_B>=-9/16. Then |y_B|<=9/16, so its horizontal center,
like that of its same-side zero unit U, lies in [l,47/80) up to
horizontal reflection. Their horizontal gap is less than 5/48.
Their inscribed disks therefore give a vertical center gap exceeding
sqrt(1-(5/48)^2)>99/100. The squared comparison has numerator
208496 over denominator 23040000. Since U is above B and y_U<227/620,
\[
 y_B<227/620-99/100=-967/1550<-9/16,
\]
a contradiction. Therefore both B_L and B_R have center heights
less than -9/16.

Together with (12), the three selected outsiders satisfy
\[
 y_F<-329/744<-11/25,\qquad y_{B_L},y_{B_R}<-9/16.
\]
The entire argument reflects to the equal-bottom-marker pattern.

## 6. Both central-to-side separators have the required outward horizontal sign

Every side center has absolute y-coordinate less than 36/25, by the
established center norm bound and |x|>=29/60. The central center has
absolute y-coordinate less than 91/60. Thus the preceding bounds give
\[
 |y_F-y_{B_i}|<
 \max\{91/60-9/16,\ 36/25-329/744\}
 =\max\{229/240,\ 18559/18600\}<1.                       \tag{13}
\]
Since x_BL<x_F<x_BR, any genuine separating normal directed from F
toward B_L must have strictly negative horizontal component. Otherwise
its center-difference projection would be at most |y_F-y_BL|<1,
while the two unit-square supports sum to at least one. Similarly,
every separating normal from F toward B_R has strictly positive
horizontal component.

Consequently, after reflecting y to place the triple above the origin,
its physical separating normals have exactly the outward forms
(-1,eta_L s) and (1,eta_R t), with s,t>=0 and eta_i in {-1,1},
required by the shared-central-orientation terminal. There is no
infinite-slope or reversed-horizontal-normal alternative left.

## 7. What this routing does and does not supply

The equal-top pattern now has a fixed vertical order of its center
groups: the two top mains, the two zero-marker outsiders, and the central
unit below both zero-marker outsiders; its two side companions are also
in the lower center cap. The equal-bottom pattern is the reflection.

The three lower center bounds are not whole-square cap bounds. The outward
horizontal signs of both central-to-side physical separators are proved.
We have
not asserted actual vertical projection separation between the bottom
side companions and the two outer mains, nor actual horizontal projection
separation of B_L,F,B_R. Those physical relationships remain the next
sharp-terminal caller obligation. No unrestricted A.2 closure or new
canonical root count is claimed by this note alone.
