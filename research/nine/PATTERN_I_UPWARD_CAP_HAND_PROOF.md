# Pattern I: an upper neighbor closes a range of upward separating directions

Hand proof, November 1, 2026. No mathematical scripts, Lean, or CI.

This note proves a four-square cap and its normalized Pattern I caller.
The separator range is explicit; steeper upward directions remain outside
this theorem.

## 1. Hypotheses and exact target

Use the constants
\[
 Q=\frac{1105}{256},\quad r=\frac{\sqrt{1105}}{16},\quad
 a=46,\quad b=\frac{27}{2},\quad k=\frac{207}{16},\quad
 T_0=\frac{211}{4}.
\]
As in the common-lower cap,
\[
 \sqrt{a^2+k^2}=23r,\quad\sqrt{b^2+k^2}=9r,
 \quad32r^2-(a+b+2k)=T_0.                               \tag{1}
\]
Let L,A,B,T be four distinct physical unit squares. L,A,T lie in the
centered disk of radius at most r. Assume the actual vertical comparisons
\[
             y_A-y_L\ge h_A+h_L,
 \qquad      y_T-y_B\ge h_T+h_B.                         \tag{2}
\]
Suppose A and B have a right/up physical separating normal
\[
 n=(p,s),\quad p>0,\quad s\ge0,\quad p^2+s^2=1,
 \quad \frac{s}{p}\le\frac7{10},
\]
\[
        n\cdot(c_B-c_A)\ge H_A(n)+H_B(n).                \tag{3}
\]
Then
\[
                  b(-x_L-h_L)+a(1-x_B-h_B)\le T_0.       \tag{4}
\]
This is strict for s>0 or when the containing radius is below r.
As usual H_S is the centered physical support function, and h_S is
either coordinate projection halfwidth.

We use the elementary orientation bound
\[
       (u+v)h_S+H_S((\pm u,\pm v))\ge u+v\quad(u,v\ge0),
                                                               \tag{5}
\]
which follows from the inscribed aligned square of halfwidth
\(g_S=1/(4h_S)\) and \(h_S+g_S\ge1\).

## 2. Cancel the inner exceptional square

Put \(t=as/p\). Multiply the actual comparisons LA and BT by k and t,
respectively, and multiply (3) by \(a/p\). Combining with the desired
horizontal center terms gives
\[
\begin{aligned}
 &-b x_L-a x_B+k(y_A-y_L)+t(y_T-y_B)
                  +a(x_B-x_A)+t(y_B-y_A)\\
 &\hspace{20mm}=-b x_L-k y_L-a x_A+(k-t)y_A+t y_T.
\end{aligned}
\]
The only disk vectors are consequently \((-b,-k)\) on L,
\((-a,k-t)\) on A, and \((0,t)\) on T. The vector on B is zero.
Circle support gives
\[
\begin{aligned}
 b(-x_L-h_L)+a(-x_B-h_B)
 \le{}&r\left(\sqrt{b^2+k^2}+\sqrt{a^2+(k-t)^2}+t\right)\\
      &-P_L-P_A-P_B-P_T,                                \tag{6}
\end{aligned}
\]
where
\[
 P_L=(b+k)h_L+H_L((-b,-k))\ge b+k,
\]
\[
 P_A=k h_A+H_A((a,t))+H_A((-a,k-t)),
\]
\[
 P_B=(a+t)h_B+H_B((a,t))\ge a+t,
 \qquad P_T=t h_T+H_T((0,t))=2t h_T\ge t.               \tag{7}
\]
Thus (4) follows if
\[
 r\left(\sqrt{a^2+(k-t)^2}-\sqrt{a^2+k^2}\right)
             +(r-2)t+a+k-P_A\le0.                     \tag{8}
\]

## 3. Three triangle edge costs

The three support vectors in P_A are
\((0,-k),(a,t),(-a,k-t)\), whose sum is zero. Therefore P_A is the
sum of the two side lengths of the bounding rectangle of the triangle
with vertices \(0,(a,t),(0,k)\), in A's physical frame.

As proved in the common-lower cap, this sum has its minimum when one
triangle edge is parallel to a frame axis: between changes of a projected
extreme vertex it is a positive sine-cosine expression with strictly
negative second derivative.

Normalize by a, and put
\[
 \mu=\frac ka=\frac9{32},\qquad z=\frac ta=\frac sp,
 \qquad L(z)=\sqrt{1+(z-\mu)^2},\qquad
 J(z)=\sqrt{1+z^2}.
\]
The three possible normalized edge costs are
\[
 E(z)=1+\max(\mu,z),\qquad
 N(z)=J(z)+\frac{\mu}{J(z)},                             \tag{9}
\]
and
\[
 D(z)=
 \begin{cases}
 L(z)+\mu/L(z),&0\le z\le\mu,\\
 L(z)+\mu(1+z-\mu)/L(z),&z\ge\mu.
 \end{cases}                                            \tag{10}
\]
For the edge giving N, the projection of \((0,\mu)\) lies between
the two endpoint projections because
\(\mu z\le1+z^2\). For D in its first range the analogous condition
is \(z(\mu-z)\le1\). Both hold since \(\mu<1\); the formulas in
the other range include the additional outside projection. These checks
justify the stated edge lengths without an ordering assumption on centers.

The identities
\[
 r=2\sqrt{1+\mu^2},\qquad
 r\sqrt{1+\mu^2}-(1+\mu)=\frac{449}{512}
\]
show that it suffices, for each \(m\in\{E,N,D\}\), to prove
\[
        rL(z)+(r-2)z\le m(z)+\frac{449}{512}
              \qquad(0\le z\le7/10).                  \tag{11}
\]

## 4. The initial interval

For \(0\le z\le\mu\), all three edge costs are at least \(1+\mu\).
For N and D this follows because \(x+\mu/x\) increases for x≥1.
Writing \(s_0=\sqrt{1+\mu^2}\), we have
\[
 r(s_0-L(z))
 =\frac{r z(2\mu-z)}{s_0+L(z)}\ge\mu z.
\]
Since \(r<133/64\),
\[
                 \mu-(r-2)>\frac{13}{64}>0.
\]
This proves (11), strictly for z>0, throughout the initial interval.

## 5. Concavity on the remaining interval

For \(\mu\le z\le7/10\), define
\[
 G_m(z)=m(z)+\frac{449}{512}-rL(z)-(r-2)z.
\]
Each of the three functions G_m is strictly concave on this interval.

For E this is immediate, because E is linear here and \(L''=1/L^3>0\).

For N, direct differentiation gives
\[
 N''(z)=\frac{(1-\mu)+(1+2\mu)z^2}{(1+z^2)^{5/2}},
\]
\[
 N'''(z)=
 \frac{z\bigl((-3+9\mu)-3(1+2\mu)z^2\bigr)}{(1+z^2)^{7/2}}<0
 \quad(z>0),
\]
because \(-3+9\mu=-15/32<0\). Thus
\(N''\le N''(0)=23/32<1\). On the entire interval,
\(L(z)<11/10\) and r>2, so
\[
                     \frac r{L(z)^3}>\frac{2000}{1331}>1.
\]
Hence \(G_N''<0\).

For D, put \(v=z-\mu\in[0,67/160]\) and \(L=\sqrt{1+v^2}\).
The second derivative of the nonlinear part of G_D is
\[
 -\frac{r-1}{L^3}
       +\mu\frac{2v^2-3v-1}{L^5}<0,
\]
since \(0\le v<1\) makes \(2v^2-3v-1<0\). Thus \(G_D\) is also
strictly concave.

It is enough to check the two interval endpoints. The first endpoint
z=μ is already strictly positive by Section 4.

## 6. Exact rational check at z=7/10

At this endpoint \(v=67/160\), and
\[
                         L<\frac{217}{200}.
\]
For example \(v<21/50\), and
\(1+(21/50)^2<(217/200)^2\). Together with r<133/64 this gives
\[
 rL+(r-2)z
 <\frac{133}{64}\frac{217}{200}
       +\frac5{64}\frac7{10}
 =\frac{29561}{12800}.
\]
After subtracting \(449/512\), the quantity to dominate is exactly
\[
                         \frac{573}{400}.              \tag{12}
\]

The N cost is greater than \(29/20=580/400\). Indeed
\(J=\sqrt{149}/10>61/50\), and the increasing function
\(x+\mu/x\) gives
\[
 N>\frac{61}{50}+\frac{225}{976}>\frac{29}{20}.
\]
The final rational comparison is \(22500>22448\). Thus the N endpoint
has margin at least \(7/400\) over (12).

For D, use
\[
 L>\frac{27}{25},\qquad L<\frac{11}{10},\qquad
 \frac{1+v}{L}>\frac{227}{176}>\frac{32}{25}.
\]
The first is a direct squared comparison with \(L^2=30089/25600\),
and the last is \(5675>5632\). Therefore
\[
                    D>\frac{27}{25}+\frac9{25}
                     =\frac{36}{25}=\frac{576}{400},
\]
giving margin at least \(3/400\).

Finally E=17/10 exceeds both required endpoint bounds. All three
G_m are strictly positive at the endpoint. Concavity and Section 5 prove
(11) throughout [μ,7/10]. Together with Section 4 this completes the cap
(4), with the asserted strictness.

## 7. Normalized Pattern I caller

Section 9 of
[PATTERN_I_NINE_SQUARE_CONTINUATION.md](PATTERN_I_NINE_SQUARE_CONTINUATION.md)
proves that the first square T of the actual top two-chain satisfies
\(B<_yT\), for every one of the three missing-top-cell positions.
The same normalized rows give \(L<_yA\), \(R<_yD\),
\(B<_xC<_xD\), and \(L<_xM<_xR\).

Apply (4) and the ordinary right-pair support cap
\[
                    a(x_D-h_D)+b(x_R-h_R)\le T_0.
\]
The two actual horizontal chains give
\[
 (x_D-h_D)-(x_B+h_B-1)\ge2,
 \qquad (x_R-h_R)-(x_L+h_L)\ge1.
\]
Thus their sum is at least \(2a+b=2T_0\). A genuine exceptional
pair has s>0 in (3), so (4) is strict, a contradiction. The entire
normalized Pattern I subcase with an upward separator of slope at most
7/10 is consequently excluded even at q=Q.

The proof uses an actual upper neighbor and its circle support; it does
not assume that the top centers have equal heights. It leaves larger
upward separator slopes open and makes no unrestricted cover claim.

## 8. Extension of the slope bound to 18/25

The same cap and caller hold with the larger slope bound
\[
                              s/p\le18/25.              \tag{13}
\]
Only the far endpoint check changes. All three concavity arguments in
Section 5 remain valid on \([\mu,18/25]\): now
\(v=z-\mu\le351/800<1\), and still \(L<11/10\).

At \(z=18/25\), use \(v=351/800<11/25\) to obtain
\(L<1093/1000\). Then
\[
 rL+(r-2)z
 <\frac{133}{64}\frac{1093}{1000}
      +\frac5{64}\frac{18}{25}
 =\frac{148969}{64000}.
\]
Subtracting \(449/512\) leaves
\[
                         \frac{23211}{16000}.           \tag{14}
\]

Both N and D are strictly greater than \(73/50\). For N,
\[
 J=\frac{\sqrt{949}}{25}>\frac{154}{125},
 \qquad
 N>\frac{154}{125}+\frac{1125}{4928}>\frac{73}{50}.
\]
The squared comparison for J is \(23725>23716\). The second comparison
reduces to \(281250>280896\).

For D, the bounds \(L>109/100\) and \(L<1093/1000\) give
\[
 \frac{1+v}{L}>\frac{5755}{4372}>\frac{296}{225}.
\]
The last comparison is \(1294875>1294112\). Consequently
\[
             D>\frac{109}{100}
                  +\frac9{32}\frac{296}{225}
               =\frac{109}{100}+\frac{37}{100}
               =\frac{73}{50}.
\]
The lower bound on L is a direct comparison with
\(L^2=763201/640000\). The upper bound follows from
\(1+(11/25)^2<(1093/1000)^2\).

Finally \(E=43/25>73/50\). Since
\[
                    \frac{73}{50}-\frac{23211}{16000}
                     =\frac{149}{16000}>0,
\]
all three endpoint residuals are positive. The same concavity proof
extends (11), hence (4), through slope 18/25, with strictness retained.
