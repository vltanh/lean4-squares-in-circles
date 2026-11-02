# A low-floor right central unit is blocked by a high right shoulder

November 2, 2026. Complete hand proof after numerical direction checks.
The exact standard-library rational replay checks every scalar reserve.
No numerical optimizer verdict is a premise. No Lean or CI.

Set

\[
 l=29/60,\quad u=13/12,\quad \rho=91/60,
 \quad J=23/150,\quad A_0=18911/59520,
\]

\[
 c=A_0-1/10=12959/59520,\quad v_0=223/372,
 \quad g=7/20,\quad G=J+1/60=17/100.
\]

## 1. The complete original-square predicate

Retain an actual horizontal main four-chain in the closed disk of squared
radius \(Q=1105/256\). Retain distinct original outsiders S,F,R, each
physically interior-disjoint from the main squares and from the other
outsiders. Suppose the left helper S has aligned inset halfwidth gS and
center \((-Z,y_S)\), with

\[
 Z>0,\qquad Z-g_S<J,\qquad y_S<7/16,
 \qquad y_S+g_S>A_0.
 \tag{1}
\]

Suppose F is a right central outsider above the right inner main M2,
whose center and whole floor satisfy

\[
 0<X=x_F\le l,\qquad Y=y_F>v_0,
 \qquad T=Y-h_F\le1/10.
 \tag{2}
\]

Suppose the original right inner main's proxy top is above one tenth:

\[
                            y_2+g_2>1/10.
 \tag{3}
\]

Finally suppose the original right outsider R satisfies

\[
                         l\le x_R<u,\qquad y_R\ge3/5.
 \tag{4}
\]

These complete predicates are incompatible. No short-chain comparison,
frame assumption, or separator owner is imposed on any square. The result
also holds after either coordinate reflection with the corresponding
reflected predicates.

The actual-four bounds supply

\[
 l<x_2<31/60,\qquad x_2-g_2<1/60,
 \qquad x_2+g_2>59/60,\qquad |c_R|<\rho.
 \tag{5}
\]

Every unit square contains an aligned square of halfwidth
\(1/(4h)\ge1/(2\sqrt2)>g=7/20\). Thus in particular \(g_S>g\),
and we may use the fixed aligned inset of halfwidth g inside R.

## 2. The right main forces an upward left F-owned separator

Write

\[
 a\ge b\ge0,\quad a^2+b^2=1,\quad h=(a+b)/2,
 \quad k=(a-b)/2
\]

for the unsigned components of the one original F frame. Define
\(c_R=y_2+g_2-T>0\). For F and the right main inset, the center gaps
are \(D_R=x_2-X>0\), \(V_R=Y-y_2>0\). Then

\[
 D_R-g_2<1/60-X<1/2,\qquad V_R-g_2=h-c_R<h.
 \tag{6}
\]

Both coordinate axes fail. Every physical separator must be an F side
axis and have positive vertical component: a nonpositive vertical component
would require \(|n_x|(D_R-g_2)\ge1/2+g_2|n_y|\), contrary to (6).

Its horizontal component must point left. An upward right F axis with
vertical component b has adjusted projection below \(bh\le1/2\).
For vertical component a the adjusted projection is below

\[
 ah-b(D_R+g_2)=1/2+b\{k-(D_R+g_2)\}\le1/2,
\]

since \(D_R+g_2>59/60-l=1/2\ge k\). Thus these alternatives also fail.
An aligned F has no remaining side axis; hence \(b>0\). Put
\(t=b/a\in(0,1]\). The two remaining original F side normals are

\[
 (-a,b)\quad\hbox{or}\quad(-b,a).
\]

Their respective necessary inequalities are

\[
 X<1/60-k-tc_R,
 \qquad X<1/60+k-c_R/t.
 \tag{7}
\]

## 3. The left helper leaves two complete alternatives

F is above S because \(Y>v_0>7/16>y_S\). Set
\(D_L=X+Z>0\), \(V_L=Y-y_S>0\), and \(c_L=A_0-T\ge c\).
The original S inset obeys

\[
 D_L-g_S<X+J,\qquad V_L-g_S<h-c_L.
 \tag{8}
\]

Vertical coordinate separation is impossible. If horizontal separation is
possible, (8) gives the first alternative

\[
                         \mathcal H:\quad X>h-J.
 \tag{9}
\]

Suppose it is impossible, so \(D_L-g_S<h\). Every remaining separator
is F-owned. Its vertical component must be positive. Indeed

\[
 V_L+g_S>v_0-7/16+7/20>1/2,
 \qquad v_0-47/80=89/7440>0.
\tag{10}
\]

A downward F axis with horizontal component a has adjusted projection less
than \(ah-b/2=1/2+b(k-1/2)\le1/2\). One with horizontal component b
has projection below \(bh-a/2<1/2\). Both fail.

An upward axis pointing left also fails. With vertical component b its
projection is below \(bh\le1/2\); with vertical component a it is below

\[
 1/2+b(k-D_L-g_S)-ac_L<1/2,
\]

because \(g_S>1/3\), \(k\le1/2\), and \(c_L\ge c>1/6\).
The left separator therefore points up and right.

It is the other orthogonal F axis from the upward left separator in
Section 2. If its components were \((b,a)\), the right components would
be \((-a,b)\), and summing their two necessary inequalities would give

\[
 Z-g_S+x_2-g_2>c_L/t+tc_R\ge c>G.
\]

This contradicts (1) and (5), which give the same sum less than G.
Thus in this oblique alternative the actual left and right F normals are
\((a,b)\), \((-b,a)\), and the left inequality gives

\[
 \mathcal O:\quad X>k+t(A_0-T)-J,
 \qquad aX+bY>1/2+bA_0-aJ.
 \tag{11}
\]

In alternative \(\mathcal H\), the first right-axis choice in (7)
is equally impossible: together with (9) it would imply
\(a=h+k<J+1/60=G\), whereas \(a\ge1/\sqrt2\). Therefore the
actual F axes in \(\mathcal H\) are also \((a,b)\), \((-b,a)\).

We have exhausted every original helper/main separator. Both alternatives
have the same original frame chirality; it has been deduced, not imposed.

## 4. Both alternatives give a small tangent and a horizontal overlap

In alternative \(\mathcal O\), add the left and right oblique
inequalities to obtain

\[
                    tc_L+c_R/t<G,
 \qquad t<G/c<4/5.
 \tag{12}
\]

In alternative \(\mathcal H\), (9) and \(X\le l\) give
\(h<l+J=191/300\). The function
\(h(t)=(1+t)/(2\sqrt{1+t^2})\) increases on \([0,1]\), and
\(h(4/5)^2=81/164>(191/300)^2\). Hence again \(t<4/5\).

We claim that the horizontal center gap from F to R obeys

\[
                         0\le D=x_R-X<h+g.
 \tag{13}
\]

In \(\mathcal H\), it is below \(u+J-h\), which is below \(h+g\)
because \(2h\ge1>u+J-g=133/150\).

In \(\mathcal O\), it is below \(u+J-k-tc\). For \(0\le t\le4/5\),

\[
 a\ge1-t/3,\qquad c>3/14,
 \qquad a+tc>1-(5/42)t\ge19/21>133/150.
 \tag{14}
\]

The first inequality follows by positive squaring:

\[
 1-(1-t/3)^2(1+t^2)=
 \frac{t}{9}(6-10t+6t^2-t^3)\ge0.
\]

The cubic decreases on \([0,4/5]\) and its right-endpoint value is
\(166/125>0\). Equation (14) proves (13), since \(h+k=a\).
The final strict margin in (14) is \(19/1050\).

## 5. All four axes fail against the original right shoulder's inset

Let \((s,z)\) be R's center, and put \(\delta=z-Y\). Its universal
center bound and \(s\ge l\) imply

\[
 z<\sqrt{\rho^2-l^2}<36/25,
 \qquad \delta<36/25-v_0<17/20.
 \tag{15}
\]

In the opposite vertical order, the assumed central floor and (4) give

\[
                 -\delta=Y-z\le h-1/2<5/24<g.
 \tag{16}
\]

Thus \(|\delta|<17/20\le h+g\). Together (13), (15)--(16) exclude
both coordinate-axis separators between F and R's fixed aligned inset.

### 5.1. The F axis with components (a,b)

Because \(t<4/5\), the maximum of \(as+bz\) on
\(s^2+z^2\le\rho^2\), \(s\le u\), \(s,z\ge0\) occurs at s=u.
Indeed the unconstrained maximizing coordinate is \(a\rho>u\);
the exact reserve \(\rho^2/(1+(4/5)^2)-u^2\) is positive. Also

\[
 \sqrt{\rho^2-u^2}<17/16,
 \quad (17/16)^2-(\rho^2-u^2)=43/19200>0.
\]

Consequently

\[
                         as+bz<au+(17/16)b.
 \tag{17}
\]

In alternative \(\mathcal O\), the positive (a,b) separator from F
to R would require, by (11) and (17),

\[
 a\underbrace{(u+J-g)}_{A}
 +b\underbrace{(17/16-A_0-g)}_{B}>1.
 \tag{18}
\]

But \(A^2+B^2<1\). Since \(a^2+b^2=1\), Cauchy--Schwarz makes
(18) impossible.

In alternative \(\mathcal H\), (9), \(Y>v_0\), and \(h\ge1/2\)
give \(aX+bY>a(1/2-J)+bv_0\). The same necessary separator
would therefore require

\[
 a\underbrace{(u+J-g-1/2)}_{A_H}
 +b\underbrace{(17/16-v_0-g)}_{B_H}>1/2.
 \tag{19}
\]

Here \(A_H^2+B_H^2<1/4\), so Cauchy--Schwarz again excludes it.
All constants in these two strict square comparisons are rational and
are recomputed by the companion arithmetic checker.

For the opposite sign of this same F axis, its center projection is
\(-aD-b\delta\le b\max(-\delta,0)<5b/24\), which is less than
its required support \(1/2+g(a+b)\). Thus neither sign separates.

### 5.2. The other original F axis

The other side normal is \((-b,a)\). If \(\delta\ge0\), its
positive projection is \(-bD+a\delta\le\delta<17/20\), below
\(1/2+g(a+b)\). Its negative projection is at most
\(bD<b(h+g)\le1/2+bg<1/2+g(a+b)\), using \(bh\le1/2\).

If \(\delta<0\), the positive projection is negative. The negative
projection is, by (13) and (16),

\[
 bD+a(-\delta)<b(h+g)+5a/24
             \le1/2+bg+5a/24<1/2+g(a+b).
\]

Both signs fail again. Every coordinate and original F side axis has now
failed, contradicting the physical disjointness of F and the inset inside
R. This proves the complete statement in Section 1.

## 6. Caller in the full-side-bottom occupancy

Suppose the left side is full with its inner main at the bottom, and the
lone right-side outsider R lies above its main. The established zero-helper
lemma supplies (1) from the lower left outsider. If R is below three fifths,
`TWO_LOW_MAINS_CENTRAL_EXCLUSION_HAND_TABLE.md` excludes a central outsider
below both inner mains. Thus in the residual one-upper/one-lower central
case we have (4).

If the upper central F has \(X\le0\), the left low-side extraction
already gives its whole floor above one tenth. Otherwise X>0. The same
two-low-mains theorem, applied to the original lower central unit, gives
\(y_2>-119/310\). The physical central clearance and the inner inset
bound therefore imply

\[
 Y>y_2+59/60>223/372=v_0,
 \qquad y_2+g_2>-119/310+15/31=1/10.
\]

All predicates (1)--(4) would hold if this upper F had floor at most one
tenth. The theorem excludes that alternative. Therefore the upper central
floor is above one tenth throughout the remaining branch. The original
higher left outsider and original R are both above three fifths, so the
accepted widened five-square cap applies with these two shoulders and F.
It contradicts the normalized strict endpoint span D>2.

This discharges the final one-upper/one-lower central branch when the full
side's main is at the bottom. The complete full-bottom occupancy caller
records the other central and right-side orders separately.

## 7. Exact arithmetic replay and scope

`verify_low_floor_right_central.py` uses only Python's standard-library
Fraction arithmetic. It reconstructs the positive-squaring identity,
checks the cubic endpoint and derivative bound, and checks all rational
height, tangent, inset, and Cauchy--Schwarz reserves in the proof.
Its saved output is `low_floor_right_central_arithmetic_replay.json`.

The physical coverage is the exhaustive separator argument above. The
replay is an arithmetic audit of that hand proof, not a sampled pose search.
No original pair or frame is replaced by an independently selectable
configuration; the same original F axes serve all three physical pairs.
