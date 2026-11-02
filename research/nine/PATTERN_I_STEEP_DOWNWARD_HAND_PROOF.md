# Pattern I: steep downward separating directions

Hand proof, November 1, 2026. No mathematical scripts, Lean, or CI.

This note closes two ranges in the normalized original-height-three
Pattern I: a downward normal owned by the outer exceptional square A
of slope at least 21/10, and one owned by B of slope at least 13/4.
The middle downward ranges remain a separate obligation.

## 1. Setup and the existing aggregate terminal

Use
\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 \rho=\frac{91}{60},\quad c_0=\frac{59}{60},\quad b_0=\frac1{60},
\]
and the normalized actual comparisons from
[PATTERN_I_NINE_SQUARE_CONTINUATION.md](PATTERN_I_NINE_SQUARE_CONTINUATION.md):
\[
 L<_xM<_xR,\quad B<_xC<_xD,\quad
 L<_yA,B,\quad R<_yD,
\]
\[
 x_B-x_A\ge g_A+g_B,\quad
 x_A<-c_0-g_A,\quad |c_S|<\rho.
\]
For any physical square put
\[
 h=h_S,\qquad g=\frac1{4h},\qquad k=\sqrt{\frac12-h^2}.
\]
In particular h+g≥1 and 1/2≤h≤1/√2.

The actual B,C,D suffix gives
\[
 x_B+h_B<b_0,\qquad d:=x_B-x_A<\frac{23}{15}-h_B.        \tag{1}
\]
Section 2 of
[PATTERN_I_STEEP_UPWARD_HAND_PROOF.md](PATTERN_I_STEEP_UPWARD_HAND_PROOF.md)
proves the uniform strict edge bound
\[
                         y_R+h_R<-\frac1{40}.           \tag{2}
\]
The bottom-three aggregate support theorem therefore excludes q≤Q
as soon as
\[
                         y_L+h_L\le-\frac{17}{20}.      \tag{3}
\]
In view of L<_yB, it will suffice below to put B's lower edge below
\(-17/20\).

## 2. A universal vertical edge bound for the outer square

**Lemma.** The outer square A satisfies
\[
                         |y_A|<h_A+\frac1{60}.          \tag{4}
\]

It suffices by reflection to exclude \(y_A\ge h_A+b_0\). Write
its center as \((-X,Y)\), and put h=h_A, g=g_A, k=k_A.
Then \(X>c_0+g\) and \(Y\ge h+b_0\).

The coordinate-only calculations in Sections 4.1--4.2 of
[ONE_EXCEPTION_TRANSVERSE_GRID_HAND_PROOF.md](ONE_EXCEPTION_TRANSVERSE_GRID_HAND_PROOF.md)
apply: their input is exactly \(X>c_0+g\), \(Y>h-b_0\).
They force the upper-left vertex offsets to be \((-k,h)\), the
left-lower offsets to be \((-h,-k)\), and
\[
                              \frac{13}{20}<h<\frac{17}{25}.
                                                               \tag{5}
\]
No actual perpendicular three-chain is being assumed here; only those
printed coordinate implications are used.

If \(h\le67/100\), the upper-left corner gives
\[
 q>G(h):=\left(c_0+\frac1{4h}+k\right)^2+(2h+b_0)^2.
\]
This function decreases on \([13/20,67/100]\). Indeed, writing
\(S=c_0+1/(4h)+k\), we have S>3/2, k<7/25, and
\[
 \frac12G'
 =-S\left(\frac1{4h^2}+\frac hk\right)+2(2h+b_0)
 <-\frac{195}{56}+\frac{407}{150}<0.
\]
At \(h=67/100\), one has k>9/40 and hence S>79/50. Thus
\[
 q>G(67/100)>
 \left(\frac{79}{50}\right)^2+
 \left(\frac{407}{300}\right)^2
 =\frac{15613}{3600}>Q.                                 \tag{6}
\]

If \(h\ge67/100\), both h+1/(4h) and h−k increase. At the split
point, k<17/75 and
\[
 c_0+h+\frac1{4h}\ge\frac{10183}{5025}>\frac{1621}{800},
 \qquad h+b_0-k>\frac{23}{50}.
\]
The lower-left corner now gives
\[
 q>\left(\frac{1621}{800}\right)^2+
       \left(\frac{23}{50}\right)^2
   =Q+\frac{113}{128000}>Q.                             \tag{7}
\]
Both alternatives contradict containment, proving (4).

## 3. A directional version of the outer-square bound

For every z≥1,
\[
                y_A-\frac{H_A((1,-z))}{z}<\frac1{60}.  \tag{8}
\]

If A's upper-left vertex has offsets \((-k,h)\), its opposite
lower-right vertex gives \(H_A((1,-z))\ge k+zh\).
Then (8) follows from (4).

Otherwise its upper-left vertex has offsets \((-h,k)\). Since
\(X>c_0+g\), its horizontal magnitude exceeds
\(c_0+g+h\ge119/60\). Its corner norm therefore gives
\[
                         y_A<\frac58-k,                \tag{9}
\]
because \(Q-(119/60)^2<25/64\).
Two other vertices yield
\[
             H_A((1,-z))\ge h+zk,
 \qquad      H_A((1,-z))\ge zh-k.
\]
For h≤5/8 we have \(k\ge\sqrt7/8>13/40\), so the first bound and
(9) give
\[
 y_A-\frac{H_A((1,-z))}{z}
 <\frac58-2k-\frac hz<-\frac1{40}<0.
\]
For h≥5/8, use the second bound and z≥1 to obtain
\[
 y_A-\frac{H_A((1,-z))}{z}
 <\frac58-h-k+\frac kz\le\frac58-h\le0.
\]
This proves (8) in every orientation.

## 4. B owns a downward normal of slope at least 13/4

Suppose a physical side axis of B gives a separating normal proportional
to \((1,-z)\), where z≥13/4. Put \(J=\sqrt{1+z^2}\). Then
\[
 h_B=\frac{1+z}{2J},\qquad H_B((1,-z))=\frac J2,
\]
and actual physical separation says
\[
                 d+z(y_A-y_B)\ge H_A((1,-z))+\frac J2.
\]
Using (1) and (8),
\[
 y_B-h_B
 <\frac1{60}
     +\frac{\displaystyle\frac{23}{15}
                  -\frac{1+z+z^2}{J}}{z}.              \tag{10}
\]

The right side is less than −17/20 for z≥13/4. After multiplication by
positive quantities, the required inequality is
\[
                  \frac{1+z+z^2}{\sqrt{1+z^2}}
                    >\frac{23+13z}{15}.
\]
Both sides are positive. Squaring reduces it to
\[
 P(z):=56z^4-148z^3-23z^2-148z-304>0.                   \tag{11}
\]
This is an elementary half-line check:
\[
 P(13/4)=\frac{4455}{32}>0,
 \quad P'(3)=1766>0,
 \quad P''(3)=3338>0,
\]
and \(P'''(z)=1344z-888>0\) for z≥3. Thus P increases on [3,∞),
and (11) holds on the required interval.

Equation (10) proves (3), because L is actually below B. The strict
aggregate terminal using (2) excludes q≤Q.

## 5. A owns a downward normal of slope at least 21/10

Suppose instead a physical side axis of A gives the separating normal
\((1,-z)\), with z≥21/10 and \(J=\sqrt{1+z^2}\). Then
\[
 h_A=\frac{1+z}{2J},\qquad k_A=\frac{z-1}{2J},
 \qquad H_A((1,-z))=\frac J2.
\]
Its upper-left vertex is \((-h_A,k_A)\), so the same corner estimate
as (9) gives \(y_A<5/8-k_A\). The other square's inscribed aligned
square gives
\(H_B((1,-z))\ge g_B(1+z)\). Separation and (1) imply
\[
\begin{aligned}
 y_B-h_B
 &<\frac58-k_A-h_B-g_B
       +\frac{23/15-h_B-g_B-J/2}{z}\\
 &\le-\frac38-k_A+\frac8{15z}-\frac J{2z},              \tag{12}
\end{aligned}
\]
using \(h_B+g_B\ge1\).

For z≥21/10,
\[
 \frac8{15z}\le\frac{16}{63},\qquad
 \frac J{2z}>\frac12,\qquad
 k_A\ge\frac{11}{2\sqrt{541}}>\frac7{30}.
\]
The last bound follows by monotonicity of \((z-1)/(2\sqrt{1+z^2})\)
and the squared comparison \(108900>106036\). Hence
\[
 y_B-h_B<-\frac38-\frac7{30}+\frac{16}{63}-\frac12
          =-\frac{2153}{2520}<-\frac{17}{20}.            \tag{13}
\]
Again L<_yB and (2) give the strict aggregate contradiction.

## 6. Scope

Both steep-direction conclusions cover all three normalized missing-top
positions and do not require the exceptional vertical union span to be
less than two. They complement the common-lower cap, which closes every
downward slope through 27/46. Together with the owned-axis range exclusion
in Section 10 of `PATTERN_I_NINE_SQUARE_CONTINUATION.md`, the two diagrams
whose first column has four squares only retain downward owned slopes
strictly between 27/46 and 18/25. The top-left-missing diagram still needs
the intervening middle slopes unless a further argument supplies its
missing vertical-span condition.
