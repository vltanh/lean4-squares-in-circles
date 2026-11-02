# Pattern I: downward owned separators through slope 18/25

November 2, 2026. Hand derivation. No mathematical program, Lean, Lake,
or CI is used as proof evidence.

This extends `PATTERN_I_COMMON_LOWER_CAP_HAND_PROOF.md` to every downward
owned separating normal with slope at most 18/25. The two possible owners
are treated explicitly. The physical hypotheses and the sharp Pattern I
caller are otherwise unchanged.

## 1. Constants and the existing support reduction

Write

\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 a=46,\quad b=\frac{27}{2},\quad k=\frac{207}{16},\quad
 T=\frac{211}{4}.
\]

Let L,A,B be physical squares with L below both A and B in actual
y-projection order. L and A are contained in the Q-disk. Suppose A,B
have a separating normal

\[
 n=\frac{(1,-z)}{J},\qquad J=\sqrt{1+z^2},\qquad z>0,
\]

which is a side axis of at least one of A,B. Put \(t=az\).
For \(t\ge k\), the earlier common-lower proof gives

\[
 \Phi:=b(-x_L-h_L)+a(1-x_B-h_B)
 \le F(t),
\]

\[
 F(t)=r\sqrt{b^2+t^2}+(r-1)\sqrt{a^2+t^2}-2t-b.
 \tag{1}
\]

Its disk vectors are \((-b,-t)\) on L and \((-a,t)\) on A;
the B vector vanishes. The three penalties are

\[
 P_L=(b+t)h_L+H_L((-b,-t))\ge b+t,
\]

\[
 P_A=2H_A((a,-t))\ge\sqrt{a^2+t^2},
\]

\[
 P_B=(a+t)h_B+H_B((a,-t))\ge a+t.                       \tag{2}
\]

The function F is convex, and the earlier proof already establishes
\(F(27)<T\), with \(\Phi<T\) for every \(0<z\le27/46\).
We improve (1) on the remaining interval

\[
 27\le t\le\frac{828}{25},\qquad
 \frac{27}{46}\le z\le\frac{18}{25}.                  \tag{3}
\]

## 2. Support in an owned side-normal direction

If a physical unit square is contained in a disk of radius R and e is
one of its unit side normals, then

\[
 e\cdot c+\frac12\le\sqrt{R^2-\frac14}.                \tag{4}
\]

Indeed the two vertices of its supporting side have common e-coordinate
\(s=e\cdot c+1/2\), and their coordinates along the perpendicular
side axis differ by one. At least one has perpendicular coordinate of
absolute value at least 1/2. Containment gives \(s^2+1/4\le R^2\),
which implies (4), including when s is negative.

Set

\[
 r_e=\sqrt{Q-1/4}=\frac{\sqrt{1041}}{16}<\frac{121}{60}.
 \tag{5}
\]

The squared comparison in (5) is
\(121^2\cdot256>1041\cdot3600\).

## 3. A owns the downward normal

Here \((-a,t)\) is a positive multiple of A's owned side normal,
so (4) replaces the A disk-support term by
\(r_e\sqrt{a^2+t^2}\). Its penalty P_A in (2) is exactly
\(\sqrt{a^2+t^2}\). Therefore

\[
 \Phi\le F_A(t):=
 r\sqrt{b^2+t^2}+(r_e-1)\sqrt{a^2+t^2}-2t-b.
 \tag{6}
\]

This is convex, since both square-root coefficients are positive.
At k it is strictly smaller than the already proved \(F(k)<T\).
At \(t=828/25\), use

\[
 r<\frac{133}{64},\quad r_e<\frac{121}{60},\quad
 \sqrt{b^2+t^2}<\frac{179}{5},\quad
 \sqrt{a^2+t^2}<\frac{227}{4}.
\]

The two radicands at this endpoint are \(3197961/2500\) and
\(2008084/625\), respectively, so both root comparisons are direct
integer comparisons. Substitution gives

\[
 F_A(828/25)
 <\frac{133}{64}\frac{179}{5}
   +\frac{61}{60}\frac{227}{4}
   -\frac{1656}{25}-\frac{27}{2}
 =T-\frac{1907}{4800}<T.
\]

Convexity closes every \(k\le t\le828/25\). The earlier
small-slope proof covers \(0<t\le k\), so the entire A-owner case
through slope 18/25 is strict.

## 4. B owns the downward normal

In this case

\[
 h_B=\frac{1+z}{2J},\qquad H_B((a,-t))=\frac{aJ}{2}.
\]

Retaining its exact penalty gives

\[
 \frac{P_B}{a}=\frac{1+z+z^2}{J}=1+z+D(z),
 \quad D(z)=J+\frac zJ-1-z.
\]

Consequently (1) improves to

\[
 \Phi\le F(t)-aD(z).                                  \tag{7}
\]

On \(1/2\le z\le18/25\),

\[
 D'(z)=\frac zJ+\frac1{J^3}-1,
 \qquad D''(z)=\frac{1+z^2-3z}{J^5}<0.
\]

At the upper endpoint, \(J<5/4\), hence

\[
 D'(18/25)>\frac{72}{125}+\frac{64}{125}-1
 =\frac{11}{125}>0.
\]

Thus D increases throughout that interval. Also

\[
 D(1/2)=\frac7{2\sqrt5}-\frac32>
 \frac{252}{161}-\frac32=\frac3{46},                   \tag{8}
\]

using \(\sqrt5<161/72\), whose squared comparison is simply
\(25920<25921\). In particular \(aD(z)>3\) throughout (3).

It remains to bound F by T+3. It is convex and \(F(27)<T\).
At the other endpoint the sharper root bounds

\[
 \sqrt{b^2+(828/25)^2}<\frac{17883}{500},\qquad
 \sqrt{a^2+(828/25)^2}<\frac{14171}{250}
\]

have squared reserves \(5589/250000\) and \(8841/62500\),
respectively. Therefore

\[
\begin{aligned}
 F(828/25)
 &<\frac{133}{64}\frac{17883}{500}
   +\frac{69}{64}\frac{14171}{250}
   -\frac{1656}{25}-\frac{27}{2}\\
 &=T+3-\frac{1643}{32000}<T+3.
\end{aligned}
\]

Convexity gives \(F(t)<T+3\) on (3). Combining this with (7)–(8)
proves \(\Phi<T\). The previously proved range up to 27/46 covers
all smaller positive slopes.

## 5. Actual Pattern I consequence

Both possible owners now give the same strict transfer cap whenever
\(0<z\le18/25\). Add the ordinary matched cap for D,R. The actual
chains B,C,D and L,M,R make the sum at least \(2a+b=2T\), as in
the original common-lower caller, contradicting strictness.

Thus every normalized Pattern I with an owned right/down exceptional
separator of slope at most 18/25 is excluded even at q=Q. The statement
uses the actual common lower square L; it does not assume a common square
above the exceptional pair or a bound on the pair's vertical union span.
