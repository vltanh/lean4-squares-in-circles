# Pattern I: closing an actual four-chain in the fat direction

November 1, 2026. Complete hand bridge. No scripts, Lean, or CI.

## 1. Hypotheses

Let nine physical unit squares with disjoint open interiors lie in the
centered disk \(q\le Q=1105/256\). All pairs except a genuine pair
A,B are separated by coordinate projections. Put \(\rho=91/60\),
\(g_S=1/(4h_S)\), and assume Pattern I:

\[
 x_B-x_A\ge g_A+g_B,\quad B<_xC<_xD,
 \qquad L<_xM<_xR.
\]

All seven displayed squares are distinct. In a branch not already
settled by an actual four-plus-three terminal, the earlier localization
gives

\[
 L<_yA,\quad L<_yB,\qquad
 x_A<-\frac{59}{60}-g_A<-\frac43.
\]

This note proves that if there is **any actual x-four-chain**, the
sharp lower bound \(q\ge Q\) follows. The chain may initially contain
one exceptional square; disjointness from A,B is not assumed.

We use the universal center bound \(|c|<\rho\), the sharp transverse
budget for actual four-chain endpoints, and the ordinary-outsider strip
bound proved in `PATTERN_II_NINE_SQUARE_CONTINUATION.md`.

## 2. A small right cap contains at most one ordinary square

Two ordinary squares S,T cannot both satisfy

\[
 x_S-h_S>\frac56,
 \qquad x_T-h_T>\frac56.
\]

Indeed their centers both lie in \((4/3,\rho)\), so their x-gap is
less than one and their x-projections overlap. The coordinate cover
therefore forces an actual y-separation. Use circle supports in
directions \((u,-v),(u,v)\), with \(u,v>0\). The separation
and the support inequality
\((u+v)h+H((\pm u,\pm v))\ge u+v\) give

\[
 2R\sqrt{u^2+v^2}>
 \frac{11}{3}u+2v.
\]

Choosing \((u,v)=(11/3,2)\) gives

\[
 q>\frac{157}{36}>Q,
\]

a contradiction. Only the actual coordinate cover of the pair is used
to obtain its y-separation.

## 3. Every actual x-four-chain has endpoints A,D

Let P,T be the left and right endpoints of any actual x-four-chain.
Then

\[
 x_P<-\frac{89}{60},\qquad x_T>\frac{89}{60},
 \qquad |y_P|,|y_T|\le\frac18.
\]

P cannot be B, because

\[
x_B\ge x_A+\frac1{\sqrt2}>-\rho+\frac1{\sqrt2}>-1.
\]

Also \(B<_xC<_xD\) gives \(x_B<\rho-2=-29/60\).

If \(P\ne A\), the pair A,P is ordinary. Both x-centers are in
\((-\rho,-4/3)\), so they cannot be x-separated. Their actual
y-separation then gives

\[
 |y_A|\ge h_A+h_P-|y_P|\ge\frac78.
\]

This contradicts the center-radius bound because

\[
 |c_A|^2>\left(\frac43\right)^2+\left(\frac78\right)^2
 >\rho^2.
\]

Thus P=A.

The weak-chain span also gives

\[
 x_D>-\rho+g_A+2+h_D
 \ge h_D+\frac{29}{60}+\frac1{2\sqrt2}
 >h_D+\frac56.
\]

The actual right endpoint satisfies
\(x_T>h_T+59/60>h_T+5/6\). If \(T\ne D\), this ordinary
pair contradicts Section 2. Neither can be an exceptional square,
since A,B both have negative x-coordinates. Consequently T=D.

Write the actual four-chain as

\[
 A<_xU<_xV<_xD.
\]

Its internal centers satisfy

\[
 -\frac{31}{60}<x_U<-\frac{29}{60},\qquad
 \frac{29}{60}<x_V<\frac{31}{60}. \tag{1}
\]

## 4. The bottom three-chain is disjoint from this four-chain

The bottom endpoints L,R are distinct from A,D. Every bottom-chain
member that is outside the actual four-chain is an **ordinary outsider**:
it is not A or B and has actual coordinate separation from both
four-chain endpoints. The outsider-strip proof therefore applies to it,
giving

\[
 |x|<\frac{13}{12}. \tag{2}
\]

For clarity, that proof uses only the actual four-chain, its endpoint
transverse bounds, and the outsider's ordinary separation from the
endpoints. It does not require that every other outsider be ordinary;
the exceptional square B can remain present elsewhere.

If L equals U or V, the actual bottom chain puts
\(x_R\ge x_L+2>89/60\). R is then outside the four-chain, by (1)
and its being distinct from A,D, contradicting (2). If R equals U or
V, the reflected argument puts the ordinary outsider L below \(-89/60\).

If M=U, then \(x_L\le x_M-1<-89/60\); L is an ordinary outsider
and contradicts (2). If M=V, then \(x_R\ge x_M+1>89/60\), and R
gives the same contradiction.

These are all possible intersections with the two internal squares.
Therefore the actual chains \((A,U,V,D)\) and \((L,M,R)\) are
disjoint. The existing physical four-plus-three terminal proves
\(q\ge Q\).

## 5. Scope

This closes every Pattern I instance having an actual four-chain in
its fat x-direction, including one containing an exceptional square.
It supplies the bridge that cannot be inferred merely from the
Pattern II theorem's disjointness hypotheses.

An actual perpendicular y-four-chain is not covered by this proof.
That case still requires its own extraction or capacity argument before
one may restrict all remaining Pattern I configurations to original
heights at most three in both directions.
