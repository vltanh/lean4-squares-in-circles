# Pattern I: closing every actual perpendicular four-chain

November 2, 2026. Complete hand bridge. No mathematical scripts, Lean,
Lake, or CI are used.

## 1. Statement and actual hypotheses

Let nine physical unit squares with disjoint open interiors lie in a
centered disk of squared radius \(q\le Q=1105/256\). All pairs except
the genuine exceptional pair A,B are separated by coordinate projections.
Put

\[
 \rho=\frac{91}{60},\quad c_0=\frac{59}{60},\quad b_0=\frac1{60},
 \qquad h_S\in[1/2,1/\sqrt2],\quad
 g_S=\frac1{4h_S},\quad j_S=\sqrt{1/2-h_S^2}.
\]

Every center has norm strictly below \(\rho\). An actual comparison
\(S<_xT\) means \(x_T-x_S\ge h_S+h_T\); define \(<_y\) likewise.
Assume the residual Pattern I relations

\[
 d:=x_B-x_A\ge g_A+g_B,\qquad B<_xC<_xD,
 \qquad L<_xM<_xR,                                    \tag{1}
\]

with all seven displayed squares distinct. The earlier localization gives

\[
 L<_yA,\qquad L<_yB,\qquad x_A<-c_0-g_A<-\frac43.     \tag{2}
\]

We set aside branches already handled by the sharp physical
four-plus-three endpoint terminal. The actual-fat-direction bridge
`PATTERN_I_ACTUAL_HEIGHT_FOUR_BRIDGE.md` handles any actual x-four-chain.
We may therefore assume the actual x-order has height at most three.

**Theorem.** If the actual y-order has a four-chain, the sharp lower bound
\(q\ge Q\) follows. Consequently the two height-four bridges together
justify restricting every still-unsettled Pattern I to original heights
at most three in both directions.

This proof does not assume that the exceptional pair is fat in y. It
retains the original coordinate cover throughout.

## 2. The actual x-ranks and two endpoint facts

The comparisons \(A<_xC<_xD\) are actual as well. The three-chains
A,C,D; B,C,D; and L,M,R, together with the x-height bound, give

\[
 r_x(A)=r_x(B)=r_x(L)=1,\qquad
 r_x(C)=r_x(M)=2,\qquad r_x(D)=r_x(R)=3.                \tag{3}
\]

In particular R,D have overlapping x-projections, so the ordinary
coordinate cover makes them actually y-comparable in one direction.
The weak span also gives

\[
 x_D>h_D+a_0,
 \qquad a_0=\frac{29}{60}+\frac1{2\sqrt2}>\frac56.    \tag{4}
\]

We use the following two previously proved facts.

* Every endpoint E of an actual y-four-chain satisfies
  \(|x_E|\le1/8\), \(h_E<8/15\), and
  \(|y_E|>h_E+c_0\). These are the sharp transverse budget and elementary
  chain bounds from `PATTERN_II_NINE_SQUARE_CONTINUATION.md`.
* A weak four-chain with the same exceptional first edge A,B has a unique
  nonexceptional far endpoint. Thus if \(B<_xS<_xT\), then \(T=D\).
  This is Section 9 of `PATTERN_I_NINE_SQUARE_CONTINUATION.md`; its proof
  uses only (1), the center bound, and the ordinary coordinate cover.

### A sharper lateral extent for a y-four-chain endpoint

Every such endpoint satisfies

\[
                         |x_E|+h_E<\frac{17}{27}.       \tag{5}
\]

Write \(X=|x_E|\), \(Y=|y_E|\), \(h=h_E\), and
\(j=\sqrt{1/2-h^2}\). Here \(Y>X\). In the outward quadrant, one
of the square's vertices has offsets h,j in one order. The smaller of
the two resulting squared-norm bounds is therefore

\[
 q\ge (Y+j)^2+(X+h)^2.
\]

On \([1/2,8/15]\), the concave function h+j is greater than 997/1000.
At the nontrivial endpoint this follows from

\[
 j(8/15)^2=\frac{97}{450}
 >\left(\frac{1391}{3000}\right)^2,
\]

whose numerator comparison is \(1940000>1934881\). Hence

\[
 Y+j>c_0+h+j>\frac{5941}{3000}>\frac{99}{50}.
\]

If \(X+h\ge17/27\), containment would give

\[
 q>\left(\frac{99}{50}\right)^2+
       \left(\frac{17}{27}\right)^2
   =Q+\frac{49831}{116640000}>Q.
\]

This proves (5). In particular every y-four-chain endpoint lies actually
between A and D in x:

\[
                              A<_xE<_xD.                \tag{6}
\]

For the left comparison, (2) and monotonicity of h−1/(4h) give

\[
 x_A+h_A<-c_0+h_A-g_A
 \le-c_0+\frac1{2\sqrt2}<-\frac{17}{27}
 <x_E-h_E.
\]

The middle strict inequality follows from
\(c_0-17/27=191/540>1/(2\sqrt2)\); after squaring, the positive
difference is \(31/291600\). The right comparison follows from
\(x_E+h_E<17/27<5/6<x_D-h_D\). Thus every such endpoint has x-rank
exactly two.

## 3. B has an actual lower and upper neighbor

Let P,U be the bottom and top endpoints of any actual y-four-chain.
The fat comparison and center bound imply

\[
 -\rho+\frac1{\sqrt2}<x_B<-\frac{29}{60}.             \tag{7}
\]

Since \(|x_P|,|x_U|\le1/8\), B has overlapping x-projections with
both P and U: its x-center gap to either is less than
\(\rho+1/8-1/\sqrt2<1\). Neither pair is exceptional. Thus both
pairs are actually y-comparable.

B cannot be below P or above U, since either would extend the four-chain
to an actual five-chain. Such a chain is impossible: its extreme centers
would be at least four units apart, whereas both have norm below
\(\rho<2\). Consequently

\[
                              P<_yB<_yU.                \tag{8}
\]

This gives the actual upper neighbor required by the broader upward-sign
caller at the end of `PATTERN_I_STEEP_UPWARD_HAND_PROOF.md`. Together
with (1), (2), and the actual R,D y-comparison from (3), that theorem
closes every upward owned separating normal of A,B. It allows either
y-order of R,D, by its independently signed endpoint-depth estimate.

## 4. Coordinate guards on A and D

The following strict guards will determine which squares can occur in an
actual y-four-chain:

\[
                 |y_A|<h_A-b_0,
                 \qquad |y_D|<h_D-b_0.                 \tag{9}
\]

### 4.1. The far-square guard

The calculation in Section 2 of
`ONE_EXCEPTION_TRANSVERSE_GRID_HAND_PROOF.md` proves more than its
three-chain statement. Its only numerical input is
\(x_D>h_D+a_0\). If \(|y_D|\ge h_D-b_0\), the outward vertex gives

\[
 q>(a_0+h_D+j_D)^2+(2h_D-b_0)^2>Q.
\]

The last inequality is exactly the strict concavity and two endpoint
checks printed there. This proves the second assertion in (9).

### 4.2. The lower guard on A

If \(y_A\le-h_A+b_0\), then (2) puts

\[
 y_L+h_L\le y_A-h_A\le-2h_A+b_0
 \le-\frac{59}{60}<-\frac9{10}.
\]

The actual bottom three-chain gives \(x_L+h_L<b_0\). These two
inequalities contradict the negative-offset quadrant exclusion in
Section 3 of `PATTERN_I_NINE_SQUARE_CONTINUATION.md`. Hence
\(y_A>-h_A+b_0\).

### 4.3. The upper guard on A, using the actual upper neighbor of B

Suppose instead that \(y_A\ge h_A-b_0\). The common-point proof in
Section 4 of `ONE_EXCEPTION_TRANSVERSE_GRID_HAND_PROOF.md` applies in
its coordinate form. Its inputs are precisely

\[
 -x_A>c_0+g_A,\qquad y_A\ge h_A-b_0.
\]

Although that section states its lemma using an actual three-chain ending
at A, its proof uses that chain only to obtain the displayed y-coordinate
bound. Replacing the strict y-bound by a weak one leaves all its needed
inequalities strict because the x-bound is strict. The printed argument
therefore gives

\[
 Z:=(-c_0,1/3)\in\operatorname{int}(A),
 \qquad |y_D|<\frac15.                                \tag{10}
\]

The x-coordinate of Z is strictly inside B's inscribed aligned square.
Indeed B,C,D actual gives

\[
 x_B-g_B<b_0-(h_B+g_B)\le-c_0,
\]

while the fat comparison gives

\[
 x_B+g_B> -\rho+g_A+2g_B
 \ge-\rho+\frac3{2\sqrt2}>-\frac{31}{60}>-c_0.
\]

The actual successor U in (8) also gives

\[
 y_B-g_B<\rho-\frac12-(h_B+g_B)\le b_0<\frac13.
\]

Physical nonoverlap with A now forces \(y_B+g_B\le1/3\): otherwise
Z would lie inside both physical squares. It follows that

\[
                  y_B-h_B\le-\frac23,
                  \qquad y_L+h_L\le-\frac23.           \tag{11}
\]

R is actually y-comparable with D. By (10), if R is below D, then its
upper edge is below −3/10; if R is above D, then its lower edge is above
3/10. The first quadrant exclusion of Section 3 of the transverse-grid
note, reflected in y when necessary, therefore gives

\[
                            x_R-h_R<\frac23.
\]

The actual bottom x-three-chain yields

\[
 x_L+h_L\le x_R-h_R-2h_M<-\frac13.
\]

Together with (11), this is the second quadrant exclusion in that note,
which forces \(q\ge41/9>Q\). This contradiction proves the upper
guard on A and completes (9).

The proof of (9) uses an actual y-four-chain only to supply B's upper
neighbor. The same guards are available in any Pattern I having that
neighbor and the ordinary actual R,D y-comparison.

## 5. Every y-four-chain member except possibly B has x-rank two

A cannot be an endpoint of an actual y-four-chain, since \(|x_A|>4/3\)
whereas an endpoint has \(|x|\le1/8\). It cannot be an internal member
either. Every internal member S of an actual y-four-chain has

\[
 h_S<\frac{31}{60},\qquad
 \frac{29}{60}<|y_S|<\frac{31}{60}.                    \tag{12}
\]

If S=A, then \(g_A>15/31\) and (2) gives
\(|x_A|>c_0+15/31>22/15\). Thus

\[
 |c_A|^2>\left(\frac{22}{15}\right)^2+
          \left(\frac{29}{60}\right)^2
 =\frac{8585}{3600}>\rho^2,
\]

a contradiction.

D cannot occur anywhere in such a four-chain. Every member of an actual
four-chain is an endpoint of one of its three-element subchains, whereas
the weak-four far-endpoint theorem excludes D as either endpoint of an
actual perpendicular three-chain.

Endpoints already have rank two by (6). Let S now be an internal member
distinct from B. It is also distinct from A,D, as just proved. The
coordinate guard \(|y_A|<h_A-b_0\) and the two intervals in (12)
show that A,S cannot be actually y-separated. For example, if S is the
upper internal member, \(A<_yS\) would give
\(y_A<b_0-h_A\), while \(S<_yA\) would give
\(y_A>c_0+h_A\); the lower internal position is the reflected calculation.
The ordinary cover therefore forces an actual x-comparison. The extreme
left location of A rules out \(S<_xA\), so \(A<_xS\).

The same calculation using \(|y_D|<h_D-b_0\) rules out actual
y-separation of S,D. Their ordinary cover and the extreme right location
of D imply \(S<_xD\). Hence

\[
                              A<_xS<_xD,
\]

and S has x-rank exactly two. This proves the assertion of this section.

## 6. A downward separator restores the long span when B's lower edge is higher

We record the following short physical lemma. Suppose A,B have a
separating normal proportional to \((1,-z)\), with \(z\ge0\), and

\[
                            y_B-h_B\ge y_A-h_A.         \tag{13}
\]

Then

\[
                             d+h_B\ge1+h_A.             \tag{14}
\]

To prove it, let \(H_S\) be the centered support function of S.
Physical separation and (13) give

\[
\begin{aligned}
 d+h_B
 &\ge H_A((1,-z))+H_B((1,-z))-zh_A+(1+z)h_B\\
 &\ge 1+H_A((1,-z))+z(1-h_A).
\end{aligned}
\]

The second line uses
\((1+z)h_B+H_B((1,-z))\ge1+z\), the elementary inscribed-square
support bound. A positive-x vertex of A has offsets \((h_A,\pm j_A)\),
so

\[
 H_A((1,-z))\ge h_A-zj_A.
\]

Since \(h_A+j_A\le1\), the preceding inequalities give (14).
Combined with B,C,D actual, it restores the full physical long span:

\[
 x_D-x_A\ge d+h_B+2h_C+h_D\ge2+h_A+h_D.              \tag{15}
\]

The disjoint actual chain L,M,R supplies the short span
\(x_R-x_L\ge1+h_L+h_R\). The existing sharp physical endpoint
terminal now proves \(q\ge Q\).

## 7. Any y-four-chain containing B is closed

B cannot be a y-four-chain endpoint, by (7) and the transverse endpoint
bound. If it were the lower internal member, then
\(y_B<-29/60\). Since L is below B,

\[
 y_L< -\frac{29}{60}-h_B-h_L\le-\frac{89}{60}.
\]

Also \(x_L<-29/60\), by its actual x-three-chain. Consequently

\[
 |c_L|^2>\frac{89^2+29^2}{3600}
 =\frac{8762}{3600}>\rho^2,
\]

which is impossible. Thus B must be the upper internal member. The
actual predecessors in that four-chain give

\[
                         y_B-h_B>-b_0.
\]

The upper guard on A in (9) says \(y_A-h_A<-b_0\). Hence (13)
holds strictly.

Every physical separating normal oriented from A toward B points right.
For completeness, \(g_S\ge j_S\), since

\[
 g_S^2-j_S^2=\frac{(4h_S^2-1)^2}{16h_S^2}\ge0.
\]

For a prospective normal \((-p,s)\), with \(p\ge0\) and \(s\ne0\),
the sum of physical supports is at least
\(|s|(h_A+h_B)-p(j_A+j_B)\). Its center projection is strictly smaller,
because \(d\ge g_A+g_B\ge j_A+j_B\) and the genuine exceptional
pair has \(|y_B-y_A|<h_A+h_B\). A horizontal left-pointing normal
also cannot separate. Thus the x-component of any separating normal is
positive. A horizontal right-pointing normal would be an actual
x-separation, contrary to the genuine exception.

Choose an owned physical separating normal, available from the elementary
separating-axis theorem for the two squares. Its upward sign is already
closed by Section 3 and the broader upward theorem. Its downward sign
satisfies the lemma in Section 6. Thus every y-four-chain containing B
is settled.

## 8. The remaining four-member middle column is impossible

Suppose now that no actual y-four-chain contains B. By Section 5, every
member of any actual y-four-chain has x-rank two. This rank level already
contains C,M and can contain at most the two additional squares beyond
the seven in (1). Therefore it has exactly four members, and they form
the actual chain

\[
                              P<_yS<_yT<_yU.            \tag{16}
\]

All four are distinct from A,B,L,D,R. Equivalently the x-rank column
profile is (3,4,2), but no assumption about a physical grid is used.

By (8), P is below B and U above B. B must have overlapping
y-projections with **both** internal squares S,T. Indeed, either y-order
between B and S creates an actual four-chain containing B: use B,S,T,U
if B is below S, and P,S,B,U if S is below B. The same argument with T
uses P,S,T,B or P,B,T,U. Each contradicts the present assumption.

The ordinary coordinate cover and x-ranks therefore give

\[
                              B<_xS,\qquad B<_xT.       \tag{17}
\]

Neither \(S<_xR\) nor \(T<_xR\) is possible. Together with (17),
either would make A,B,S,R or A,B,T,R a weak four-chain with the same
exceptional first edge, ending at R rather than D. This contradicts
far-endpoint uniqueness. The reverse x-comparisons are excluded by the
x-ranks. Thus R is actually y-comparable with both S and T.

There are only three possible orders, since S is below T:

* If R is below S, then R,S,T,U is an actual y-four-chain with endpoint R.
* If R is above T, then P,S,T,R is an actual y-four-chain with endpoint R.
* If S is below R and R below T, then P,S,R,T,U is an actual y-five-chain.

The first two alternatives contradict \(x_R>29/60\) and the endpoint
bound \(|x_R|\le1/8\). The third contradicts the center-radius bound.
All possibilities are exhausted, proving impossibility of this last
profile.

## 9. Completed scope

Sections 7 and 8 exhaust every actual perpendicular four-chain. Along
with the already proved actual-fat-direction bridge, they close all
Pattern I instances in which either original coordinate order has height
four. The remaining Pattern I analysis may therefore use the original
height-three rank normalization without a missing height-four branch.

This is a lower-bound bridge, using the existing sharp endpoint terminal
when (15) holds. It makes no new equality-classification claim and does
not assert that an arbitrary nine-square packing admits a one-exception
coordinate cover.
