# A full side column forces its middle main center into |y|<7/20

November 2, 2026. Hand proof. No coordinate-cover assumption, numerical
certificate, mathematical script, Lean, or CI is used.

Let physical unit squares have disjoint interiors and lie in the closed
disk of squared radius

\[
 Q=\frac{1105}{256}.
\]

Suppose four of the squares form an actual horizontal projection chain
\(M_0<_xM_1<_xM_2<_xM_3\). Write

\[
 l=\frac{29}{60},\qquad u=\frac{13}{12}.
\]

## 1. The one-sided statement

Let S be any physical square other than the main squares, with center
\((X,y_S)\) and \(l\le X\le u\). If \(y_S<y_{M_2}\), then

\[
                         y_{M_2}>-\frac38.              \tag{1}
\]

If \(y_S>y_{M_2}\), reflection in the horizontal axis gives
\(y_{M_2}<3/8\). The corresponding statements for M1 and the left
side follow by horizontal reflection.

Consequently, if a side column contains its internal main square and
two outsiders, one with center above the main and one below it, then

\[
                            |y_M|<\frac38.              \tag{2}
\]

Section 6 strengthens (1) to y_M>−7/20, and consequently strengthens
(2) to |y_M|<7/20. Sections 2--5 retain the first, independently
checkable bound before that improvement.

In the closed-disjoint normalization used in
[UNRESTRICTED_ACTUAL_FOUR_CHAIN_SIDE_CAPACITY_HAND_PROOF.md](UNRESTRICTED_ACTUAL_FOUR_CHAIN_SIDE_CAPACITY_HAND_PROOF.md), the marker
order lemma identifies exactly this configuration when the full side's
main square occupies its middle marker. Thus (2) strengthens the earlier
71/150 bound for that marker pattern.

## 2. Retaining the near-aligned main's orientation in the center clearance

The actual four-chain gives

\[
 l<x_{M_2}<\frac{31}{60},\qquad
 \frac12\le h_{M_2}<\frac{31}{60}.
\]

For any square put

\[
 h=\frac{a+b}{2},\quad k=\frac{a-b}{2},\quad
 a\ge b\ge0,\quad a^2+b^2=1.
\]

Thus \(k=\sqrt{1/2-h^2}\). For the internal main,

\[
 k_M>\frac{193}{400},\qquad
 b_M=h_M-k_M<\frac{41}{1200}<\frac7{200},\qquad
 a_M>\frac{999}{1000}.                                  \tag{3}
\]

The first comparison follows from
\(839/3600>(193/400)^2\). The last follows from
\(1-(7/200)^2>(999/1000)^2\).

Two physical unit squares with reduced relative angle Δ have center
distance at least

\[
                    \frac{1+\cos\Delta+\sin\Delta}{2}.
                                                               \tag{4}
\]

Indeed a separating axis can be chosen normal to a side of one square,
and the sum of support halfwidths on every such axis is the expression
in (4). For S and M, irrespective of the two chiralities,

\[
 \cos\Delta+\sin\Delta\ge 2h a_M-2k b_M.                \tag{5}
\]

To check (5), represent their unsigned orientation angles by β and α.
For equal chiralities,
\(\cos(\beta-\alpha)+|\sin(\beta-\alpha)|\) is at least
\(\cos(\beta-\alpha)+\sin(\beta-\alpha)
 =2h a_M-2k b_M\), including β<α. For opposite chiralities the sum is
\(2h a_M+2k b_M\). Reduction modulo a quarter-turn preserves the sum
of absolute cosine and sine.

By (3)--(5), the center distance is strictly greater than

\[
 \frac12+\frac{999}{1000}h-\frac7{200}k
                         >h+\frac{12}{25}.              \tag{6}
\]

For the final comparison it suffices that h<1 and k≤1/2:
\(h/1000+7k/200<1/1000+7/400<1/50\).

Set

\[
 D=X-\frac9{20},\qquad m=h+\frac{12}{25},\qquad
 s=\sqrt{m^2-D^2}.
\]

The main's x-band gives \(|X-x_M|<D\). If X≥x_M this follows from
\(x_M>l>9/20\); if X<x_M, it follows from
\(31/60-X\le X-9/20\), since X≥l. Here

\[
 \frac1{30}\le D\le\frac{19}{30},\qquad
 s^2\ge\left(\frac{49}{50}\right)^2
                -\left(\frac{19}{30}\right)^2
       =\frac{12584}{22500}
       >\left(\frac{37}{50}\right)^2.                   \tag{7}
\]

Assume contrary to (1) that \(y_M\le-3/8\), with S below M, and
write \(Y=-y_S\). The physical center clearance (6) implies

\[
 Y>\frac38+s>\frac{223}{200}>u\ge X.                    \tag{8}
\]

## 3. Two actual corner constraints

For a square centered at (X,Y) with Y≥X≥0, either chirality gives

\[
 q\ge\max\left\{
       (X+h)^2+(Y+k)^2,\ (X-k)^2+(Y+h)^2\right\}.       \tag{9}
\]

For one chirality the two displayed terms are the squared norms of
actual corners. For the other, the actual corner (X+k,Y+h) dominates
both: its squared-norm difference from the first term is
\(2(h-k)(Y-X)\), and from the second is 4Xk. Reflection of S in the
horizontal axis before applying (9) is harmless.

Put c=3/8 and define

\[
 A(X,h)=(X+h)^2+(c+k+s)^2,\qquad
 B(X,h)=(X-k)^2+(c+h+s)^2.
\]

Equations (8)--(9) give \(q>\max\{A(X,h),B(X,h)\}\).

## 4. Orientations with 1/2≤h≤13/20

For fixed h, differentiation gives

\[
 \frac12 A_X=\frac9{20}+h-\frac{D(c+k)}s
       >\frac{19}{20}-\frac{665}{888}>0,                 \tag{10}
\]

using (7), D≤19/30, and c+k≤7/8. Thus A(X,h)≥A(l,h).
At X=l, the inequality \(\sqrt{1-z}>1-z\), for 0<z<1, gives

\[
 s>m-\frac1{900m}\ge m-\frac1{882}>m-\frac1{800}.
\]

Consequently

\[
 A(X,h)>
 F(h):=(l+h)^2+\left(h+k+\frac{683}{800}\right)^2.      \tag{11}
\]

This function is strictly concave on [1/2,13/20]. Indeed

\[
 F''=2+2(1-h/k)^2-\frac{h+k+683/800}{k^3}.
\]

On this interval, 1≤h/k<5/2, k≤1/2, h+k>7/10, and
683/800>17/20. The positive terms are below 13/2, while the
subtracted term exceeds 62/5. Hence F''<0, and it suffices to check
the endpoints. They satisfy

\[
 F(1/2)>
 \left(\frac{59}{60}\right)^2+\left(\frac{37}{20}\right)^2
       =Q+\frac{4207}{57600},                            \tag{12}
\]

and, using \(k(13/20)=\sqrt{31}/20>27/100\),

\[
 F(13/20)>
 \left(\frac{17}{15}\right)^2+\left(\frac{177}{100}\right)^2
       =Q+\frac{145351}{1440000}.                       \tag{13}
\]

Both contradict q≤Q.

## 5. Orientations with h≥13/20

For fixed h, the other corner expression is strictly concave in X:

\[
 B_{XX}=-\frac{2(c+h)m^2}{s^3}<0.                       \tag{14}
\]

Its minimum on [l,u] is therefore at an endpoint. At X=l,
\(s>9/8\), since \(m\ge113/100\) and D=1/30. Hence

\[
 B(l,h)>(c+h+s)^2>\left(\frac{43}{20}\right)^2>Q.       \tag{15}
\]

At X=u, the expression B(u,h) increases with h: k decreases, s
increases, and u−k>0. At h=13/20, we have k<7/25 and s>93/100;
the latter squared comparison has reserve 49/4500. Therefore

\[
 B(u,h)>
 \left(\frac{241}{300}\right)^2+\left(\frac{391}{200}\right)^2
       =Q+\frac{217387}{1440000}.                       \tag{16}
\]

This also contradicts q≤Q. The endpoint h=1/√2 follows either
directly from these increasing expressions or by continuity; the
derivative of k at that endpoint is not needed.

All possible orientations have been excluded under the contrary
assumption y_M≤−3/8. This proves (1), its reflected form, and (2).

The conclusion is a necessary main-height restriction. It does not
assert actual vertical projection separation, and it does not by itself
exclude the full actual-four-chain five-outsider configuration.

## 6. The stronger constant 7/20

We now prove the stronger form

\[
 y_S<y_M\quad\Longrightarrow\quad y_M>-\frac7{20},
 \qquad
 \text{a full side with its main at the middle marker}
       \quad\Longrightarrow\quad |y_M|<\frac7{20}.
\tag{17}
\]

Keep the notation of Sections 2--5, but put c=7/20 and suppose
y_M≤−c. In addition to (6), the two inscribed radius-1/2 disks give
center distance at least one. Therefore

\[
 Y>c+\sqrt{m_*^2-D^2},\qquad
 m_*:=\max\{1,h+12/25\}.
\tag{18}
\]

Strictness follows from the strict horizontal-gap bound |X−x_M|<D,
even when only the non-strict center-distance bound one is used.
Since m_*≥h+12/25, the square root is still greater than 37/50.
Thus Y>109/100>u≥X, and the same two-corner bound (9) applies.

For fixed h, the first corner expression again increases with X:
the derivative calculation (10) is unchanged with m_* in place of m,
and c+k≤7/8 and the same lower bound on the square root suffice.
Its minimum is therefore at X=l.

### 6.1. Small tilts: 1/2≤h≤13/25

Here m_*=1. Put s_0=√899/30. At X=l the first corner expression is

\[
 F_0(h)=(l+h)^2+(c+k+s_0)^2.
\]

It decreases with h on this interval. Indeed F_0'(h)<0 is equivalent
to \(lk<h(c+s_0)\), and the left side is at most 29/120, while the
right side is greater than 1/2. At the upper endpoint,

\[
 s_0>\frac{999}{1000},\qquad
 k(13/25)=\frac{\sqrt{574}}{50}>\frac{479}{1000}.
\]

The squared reserves for these two comparisons are respectively
7991/9000000 and 159/1000000. Consequently

\[
 F_0(h)\ge F_0(13/25)>
 \left(\frac{301}{300}\right)^2+\left(\frac{73}{40}\right)^2
       =Q+\frac{30091}{1440000}>Q.
\tag{19}
\]

For the second term, c+999/1000+479/1000=457/250>73/40.

### 6.2. Intermediate tilts: 13/25≤h≤13/20

Now m_*=h+12/25. The same estimate at X=l used in (11) gives

\[
 A(X,h)>(l+h)^2+\left(h+k+\frac{663}{800}\right)^2
                         =:F_1(h).
\]

This function is concave on the interval: the formula for F'' in
Section 4 still holds, with 663/800 in place of 683/800. Its positive
terms are less than 13/2, while the subtracted term exceeds 12.
At h=13/25, use k>479/1000 to get the same strict endpoint lower
bound in (19). At h=13/20, use k=√31/20>11/40 to obtain

\[
 F_1(13/20)>
 \left(\frac{17}{15}\right)^2+\left(\frac74\right)^2
       =Q+\frac{1759}{57600}>Q.
\tag{20}
\]

Concavity excludes the whole intermediate interval.

### 6.3. Larger tilts: h≥13/20

Use the second corner expression B. It remains concave in X by (14).
At X=l the estimates h≥13/20 and s>9/8 give

\[
 B(l,h)>\left(\frac{17}{8}\right)^2
                           =Q+\frac{51}{256}>Q.
\]

At X=u it increases with h as before. The same k<7/25 and s>93/100
bounds at h=13/20 now give

\[
 B(u,h)>
 \left(\frac{241}{300}\right)^2+\left(\frac{193}{100}\right)^2
       =Q+\frac{77527}{1440000}>Q.
\tag{21}
\]

The endpoint h=1/√2 again follows by continuity. These three ranges
prove (17), including both reflected statements.

## 7. Scope of this recovered source

This recovery retains the complete one-sided and two-sided height proofs
through Section 6. The subsequent whole-floor and three-plus-two routing
sections are not included here; they additionally require the adjacent-proxy
barrier and horizontal-strip pair-gap sources. No unrestricted A.2 closure
is asserted. The stronger extreme-main theorem appears separately in
[FULL_SIDE_EXTREME_MAIN_THREE_FIFTHS_HAND_PROOF.md](FULL_SIDE_EXTREME_MAIN_THREE_FIFTHS_HAND_PROOF.md).
