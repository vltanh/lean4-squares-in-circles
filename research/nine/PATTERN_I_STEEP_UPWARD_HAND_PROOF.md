# Pattern I: every upward exceptional separator is excluded

November 1, 2026. Complete hand derivation for the normalized original-height-three
Pattern I. No mathematical program, Lean, Lake, or CI is used in the proof.

This note completes the upward-sign case left by
`PATTERN_I_UPWARD_CAP_HAND_PROOF.md`. The separating normal may be an axis
of either physical square. All three missing-top-cell positions are covered.

## 1. Actual geometry and the bottom-chain terminal

Use the normalized nine-square arrangement and notation of
`PATTERN_I_NINE_SQUARE_CONTINUATION.md`. In particular,

\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad \rho=\frac{91}{60},
 \quad h_S\in[1/2,1/\sqrt2],\quad g_S=\frac1{4h_S}.
\]

The actual comparisons include

\[
 L<_xM<_xR,\qquad B<_xC<_xD,
 \qquad L<_yA,B,\qquad R<_yD,
 \qquad B<_yT,
\]

where T is the first square of the actual top two-chain. Also

\[
 x_A<-\frac{59}{60}-g_A,\qquad |c_S|<\rho.
 \tag{1}
\]

The B suffix and its upper neighbor give

\[
 x_B+h_B<\frac1{60},\qquad y_B+h_B<\frac{61}{60}.
 \tag{2}
\]

For example, the first follows from
\(x_D-x_B\ge h_B+2h_C+h_D\) and \(x_D<\rho\); the second
follows from \(B<_yT\), \(y_T<\rho\), and \(h_T\ge1/2\).
Consequently, with \(d=x_B-x_A\),

\[
 d<\frac{23}{15}-h_B.                                  \tag{3}
\]

The aggregate support bound for the actual bottom three-chain says that
if the sum of its endpoint top edges is at most \(-7/8\), then
\(q\ge Q\). More generally, if those edges are at most \(-u,-v\),
with \(2+u+v>0\), then

\[
 4q\ge9+(2+u+v)^2.                                     \tag{4}
\]

The same bound holds with independent signs at the two endpoints: it is
enough that \(|y_L|-h_L\ge u\) and \(|y_R|-h_R\ge v\).
Use the two disk-support directions
\((-p,\operatorname{sgn}(y_L)s)\) and
\((p,\operatorname{sgn}(y_R)s)\). The actual x-three-chain and
\((p+s)h+H((\pm p,\pm s))\ge p+s\) give
\(2\sqrt q\sqrt{p^2+s^2}\ge3p+(2+u+v)s\), exactly as before.
Thus a later caller may replace \(R<_yD\) by either actual y-order
between R and D.

We first prove a uniform strict bound for the right endpoint edge. It
will be useful for both signs of the exceptional separator.

## 2. The far ordinary square has lower edge below -1/40

**Lemma.** In the weak four-chain,

\[
 y_D-h_D<-\frac1{40},\qquad y_R+h_R<-\frac1{40}.
 \tag{5}
\]

The second inequality follows immediately from \(R<_yD\), so prove
the first. The weak-chain sum gives

\[
 x_D>h_D+a_0,
 \qquad a_0=\frac{29}{60}+\frac1{2\sqrt2}>\frac{251}{300}=:c.
 \tag{6}
\]

Here \(1/(2\sqrt2)>53/150\), by the squared comparison
\(1/8>2809/22500\).

Suppose instead \(y_D-h_D\ge-1/40\). Write \(h=h_D\),
\(k=\sqrt{1/2-h^2}\), and \(\varepsilon=1/40\). Then
\(x_D>h+c\) and \(y_D\ge h-\varepsilon>0\).

If \(h\ge3/5\), the center alone gives

\[
 |c_D|^2>
 \left(\frac{431}{300}\right)^2+\left(\frac{23}{40}\right)^2
 >\left(\frac{91}{60}\right)^2,
\]

a contradiction. It remains to consider \(1/2\le h\le3/5\).
The outward-quadrant corner inequality, using the separate positive
coordinate lower bounds, gives

\[
 q\ge F(h):=(c+h+k)^2+(2h-\varepsilon)^2.                \tag{7}
\]

Indeed the two possible outward corners have offsets \((h,k)\) and
\((k,h)\); at the lower center coordinates \((h+c,h-\varepsilon)\)
the second expression is smaller, since \(h+c>h-\varepsilon\).
Both corner expressions increase in the two nonnegative center coordinates.

Direct differentiation gives

\[
 k^3F''(h)=4k^2(2k-h)-c-h<0.
\]

For instance, \(k\le1/2\), \(h\ge1/2\), and therefore the first
term is at most \(1/2\), while \(c+h>1/2\). Thus F is strictly
concave on the indicated interval. Its two endpoint values exceed Q:

\[
 F(1/2)=\left(\frac{551}{300}\right)^2+
             \left(\frac{39}{40}\right)^2
       =Q+\frac{10891}{1440000}>Q,
\]

and, since \(k(3/5)=\sqrt{7/50}>37/100\),

\[
 F(3/5)>
 \left(\frac{271}{150}\right)^2+
 \left(\frac{47}{40}\right)^2
 =Q+\frac{472699}{1440000}>Q.
\]

Concavity contradicts (7) throughout the interval, proving (5).
Applying the same argument after reflection in y also gives
\(|y_D|<h_D-1/40\). Therefore, whenever R is actually y-comparable
with D in either direction, \(|y_R|-h_R>1/40\); the independently
signed form of (4) is available in that broader caller as well.
In particular, by (4), it now suffices to prove

\[
 y_L+h_L\le-\frac{17}{20},                             \tag{8}
\]

because \(17/20+1/40=7/8\), and (5) makes the final contradiction
strict even at Q.

## 3. Owned upward normals and their exhaustive split

The square separating-axis theorem supplies a separating normal that is
an axis of A or B. Fatness and genuine vertical overlap force its
x-component to be positive, as proved in the capacity and rank notes.
Here consider an upward normal. Write

\[
 n=\frac{(1,z)}{J},\qquad z>0,\qquad J=\sqrt{1+z^2}.
\]

The physical separation inequality, scaled by J, is

\[
 d+z(y_B-y_A)\ge H_A((1,z))+H_B((1,z)).                 \tag{9}
\]

If square S owns this normal, then

\[
 H_S((1,z))=\frac J2,
 \qquad h_S=\frac{1+z}{2J}.                            \tag{10}
\]

For either square, its inscribed aligned square gives

\[
 H_S((1,z))\ge(1+z)g_S,
 \qquad h_S+g_S\ge1,
 \qquad g_S\ge\frac1{2\sqrt2}>\frac7{20}.              \tag{11}
\]

The earlier upward-cap theorem already excludes \(0<z\le7/10\).
We treat every remaining z by the owner of the normal. When both squares
own it, either applicable argument may be used.

## 4. B owns the normal: every z at least 7/10 is excluded

Combining (2), (3), and (9), and using (10) for B and (11) for A, gives

\[
\begin{aligned}
 z(y_A-h_A)
 &<\frac{23}{15}+\frac{61z}{60}
       -(1+z)h_B-z h_A-H_A((1,z))-H_B((1,z))\\
 &\le\frac{23}{15}+\frac z{60}
       -\frac{1+z+z^2}{J}-g_A.
\end{aligned}                                         \tag{12}
\]

Here
\((1+z)h_B+J/2=(1+z+z^2)/J\) and
\(z h_A+(1+z)g_A=z(h_A+g_A)+g_A\ge z+g_A\).

For all \(z\ge7/10\), we claim

\[
 \frac{1+z+z^2}{\sqrt{1+z^2}}
 >\frac{71}{60}+\frac{13}{15}z.                        \tag{13}
\]

Both sides are positive. Squaring and multiplying by \(3600(1+z^2)\)
reduces the comparison to

\[
 P(z):=896z^4-184z^3+3055z^2-184z-1441>0.
\]

For a direct hand coefficient check, subtract
\((71+52z)^2(1+z^2)\) from \(3600(1+z+z^2)^2\).
The respective coefficient lists in descending order are
\((2704,7384,7745,7384,5041)\) and
\((3600,7200,10800,7200,3600)\), giving exactly P.
Moreover

\[
 P''(z)=10752z^2-1104z+6110>0\quad(z\ge1/2),
 \qquad P'(1/2)=3181>0,
\]

and

\[
 P(7/10)=\frac{197919}{2500}>0.
\]

Thus P is increasing and positive on the required half-line, proving
(13). Insert it and \(g_A>7/20\) into (12). The constant terms cancel,
since \(23/15=71/60+7/20\), and yield

\[
 y_A-h_A<\frac1{60}-\frac{13}{15}=-\frac{17}{20}.
\]

Since L is actually below A, condition (8) follows. Equations (4)–(5)
exclude this entire owner case.

## 5. A owns the normal: every z at least one is excluded

Use (10) for A and (11) for B in (9). Equations (2)–(3) give

\[
 z y_A<\frac8{15}+\frac z{60}-\frac J2.
\]

Consequently

\[
 y_A-h_A<-F_A(z),
 \quad F_A(z)=\frac{1+z}{2J}+\frac{J}{2z}
                    -\frac8{15z}-\frac1{60}.          \tag{14}
\]

The function F_A is strictly increasing for z>0, because

\[
 2J^3z^2 F_A'(z)=\frac{16}{15}J^3-z^3-1>0.
\]

Indeed \(J^3>z^3+1\): after squaring the positive sides, their
difference is \(z^2(3z^2-2z+3)>0\). At one,

\[
 F_A(1)=\sqrt2-\frac{11}{20}>\frac{17}{20},
\]

using \(\sqrt2>7/5\). Thus for z≥1 the top edge of L is below
\(-17/20\), and the same strict bottom-chain terminal applies.

## 6. A owns the normal: the remaining interval 7/10 to one

This interval is closed by retaining the outer square's actual x-location
in the upward-cap calculation. Put

\[
 a=46,\quad b=27/2,\quad k=207/16,\quad
 T_0=211/4,\quad \mu=k/a=9/32,
 \quad v=z-\mu\ge67/160.
\]

The upward-cap proof uses disk vectors \((-b,-k)\) on L,
\(a(-1,-v)\) on A, and \((0,az)\) on T; the B vector cancels.
Because A owns \((1,z)\), its exposed vertex for \((-1,-v)\) has
offset

\[
 (-h_A,j_A),\qquad
 h_A=\frac{1+z}{2J},\qquad j_A=\frac{1-z}{2J}.
\]

To check the signs, its side axes can be taken as
\((1,z)/J,(-z,1)/J\). Their dot products with \((-1,\mu-z)\)
are \(-(1+z^2-\mu z)/J<0\) and \(\mu/J>0\), respectively.
Thus this is the actual supporting vertex, not a virtual corner.

Throughout \(7/10\le z\le1\),

\[
 h_A\ge\frac{17}{2\sqrt{149}}>\frac{69}{100}.
\]

For example \(\sqrt{149}<123/10\) gives the stricter lower bound
\(85/123>69/100\). Since \(h+1/(4h)\) increases for h≥1/2,

\[
 h_A+g_A>\frac{69}{100}+\frac{25}{69}
 =\frac{21}{20}+\frac4{1725}.
\]

By (1), the supporting vertex has negative x-coordinate of magnitude

\[
 X=-x_A+h_A>\frac{59}{60}+g_A+h_A>\frac{61}{30}=:c_1.
\]

Write its negative y-coordinate as Y. Actual containment gives
\(X^2+Y^2\le Q\). We have

\[
 \sqrt{Q-c_1^2}<\frac7{16},
\]

because \(Q-49/256=33/8<(61/30)^2\). The function
\(X+v\sqrt{Q-X^2}\) decreases for X≥c_1: its derivative is
\(1-vX/\sqrt{Q-X^2}<0\), since
\((67/160)(61/30)>7/16\). Therefore the actual A support obeys

\[
 (-1,-v)\cdot c_A+H_A((-1,-v))
 =X+vY<c_1+\frac7{16}v.                               \tag{15}
\]

This replaces its unrestricted circular support value in the earlier
upward-cap proof. Since A owns the triangle edge \((1,z)\), its
normalized triangle penalty is exactly

\[
 N(z)=J+\frac\mu J.
\]

The same support sum as that proof now yields the desired strict transfer
cap

\[
 b(-x_L-h_L)+a(1-x_B-h_B)<T_0                          \tag{16}
\]

provided

\[
 c_1+\frac7{16}(z-\mu)+(r-2)z
 <N(z)+\frac{449}{512}.                               \tag{17}
\]

For completeness, the other support costs are at least
\(b+k\) on L, \(a+az\) on B, and \(az\) on T. The L disk
support is \(9Q\), and the T disk support is at most \(raz\).
The constant in (17) is
\((T_0-9Q+b+k)/a=449/512\), so no extra cost is omitted.

Use \(r-2<5/64\) and
\(7\mu/16+449/512=1\). It suffices to show

\[
 N(z)-\frac{33}{64}z>c_1-1=\frac{31}{30}.
\]

The elementary unit-vector bound gives \(J\ge(4+3z)/5\).
Also \(J\le\sqrt2<10/7\), hence \(\mu/J>63/320\). Thus

\[
 N(z)-\frac{33}{64}z
 >\frac{319}{320}+\frac{27}{320}z
 \ge\frac{3379}{3200}
 =\frac{31}{30}+\frac{217}{9600}>\frac{31}{30}.
\]

This proves (17) and (16). Add the ordinary right matched cap
\(a(x_D-h_D)+b(x_R-h_R)\le T_0\). The actual chains B,C,D
and L,M,R make their sum at least \(2a+b=2T_0\), contradicting
the strict inequality (16). This closes the final A-owner interval.

## 7. Completed upward-sign conclusion

Every owned upward separating normal has slope either at most 7/10,
covered by the earlier upward cap, or at least 7/10. In the latter range,
Sections 4–6 cover both possible owners and every slope. Therefore the
entire normalized original-height-three Pattern I is impossible in the
closed Q-disk whenever the exceptional pair has an upward owned separator.

The right/down sign remains a separate obligation. This theorem does not
assume that the physical centers in one rank row have equal heights and
does not assert a one-exception cover for unrestricted packings. The lower-edge
lemma (5) and the aggregate-depth criterion (8) are available independently
for the remaining sign.

The proof also supplies the following explicit broader caller. The original
rank-height assumption may be replaced by the actual relations
\(L<_xM<_xR\), \(B<_xC<_xD\), \(L<_yA,B\), one actual
upper neighbor \(B<_yT\), the outer bound (1), and an actual
y-comparison between R and D in either direction. The small-slope and
middle-slope cap additions use the unrestricted physical pair cap for D,R;
the large-slope alternatives use the independently signed aggregate bound
above. No other property of the three rank rows enters those arguments.
