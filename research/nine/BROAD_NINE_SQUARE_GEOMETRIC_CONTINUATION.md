# The middle-strip capacity of a four-chain's five-square complement

November 1, 2026. Hand proof; no scripts, Lean, or CI.

This note completes the lower bound in the actual-four-chain setting of
`PATTERN_II_NINE_SQUARE_CONTINUATION.md`, using the two physical transfer
caps named in Section 8 below. It retains all nine physical squares and
the one-exception hypothesis. It makes no unrestricted two-direction
cover assertion.

## 1. Hypotheses and established geometric bounds

Put

\[
 Q=\frac{1105}{256},\qquad \rho=\frac{91}{60}.
\]

Nine physical unit squares with pairwise disjoint open interiors lie in
the closed disk of squared radius \(q\le Q\). Fix orthonormal coordinates.
Every pair except one genuine exceptional pair \(A,B\) has an actual
x- or y-projection separation. The exceptional pair has overlapping
open projections in both directions. There is an actual chain

\[
 M_0<_xM_1<_xM_2<_xM_3,
\]

and both exceptional squares belong to its five-square complement.
For each square write \(h\in[1/2,1/\sqrt2]\) for its common x/y
projection halfwidth, and \(g=1/(4h)\). Label the exceptional pair so
that the x-direction is fat and

\[
 x_B-x_A\ge g_A+g_B\ge\frac1{\sqrt2}.                 \tag{1}
\]

The earlier four-chain and endpoint-budget proofs give the following
bounds, with their axes-interchanged versions as well:

\[
 |c|<\rho,\qquad
 \begin{array}{c|c}
 i&x_{M_i}\\ \hline
 0&(-91/60,-89/60)\\
 1&(-31/60,-29/60)\\
 2&(29/60,31/60)\\
 3&(89/60,91/60)
 \end{array}                                                     \tag{2}
\]

\[
 h_{M_1},h_{M_2}<\frac{31}{60},\qquad
 |y_{M_0}|+|y_{M_3}|\le\frac18.                    \tag{3}
\]

In particular, both endpoints of any actual y-four-chain have
\(|x|\le1/8\), and its two internal squares have \(h<31/60\).
There is no actual five-chain, since its endpoint-center distance is at
least four, whereas every pair of centers has distance less than
\(2\rho<4\).

For completeness, the internal halfwidth bound in (3) follows directly
from an actual four-chain's endpoint span:

\[
 h_0+2h_1+2h_2+h_3\le x_3-x_0<2\rho=\frac{91}{30}.
\]

All halfwidths other than a specified internal \(h_i\) contribute at
least two, so \(2h_i<31/30\).

Every outsider has \(|x|<13/12\). Partition the outsiders into

\[
 \mathcal L=\{S:x_S\le-29/60\},\quad
 \mathcal C=\{S:|x_S|<29/60\},\quad
 \mathcal R=\{S:x_S\ge29/60\}.
                                                               \tag{4}
\]

The side-column bounds already proved are

\[
 |\mathcal L|\le2,\qquad |\mathcal R|\le2.                      \tag{5}
\]

Every left outsider overlaps \(M_1\) horizontally, and every right
outsider overlaps \(M_2\) horizontally. Each corresponding side column
together with its main square is an actual y-chain. Every middle
outsider horizontally overlaps both \(M_1,M_2\), and every two middle
outsiders horizontally overlap one another: the relevant center gaps
are strictly less than one. Thus they are y-separated unless their pair
is exactly \(A,B\).

We use the established sharp four-plus-three terminal whenever three
outsiders form an actual x-chain. It proves \(q\ge Q\), with its
previously established equality conditions.

## 2. At most three outsiders can be middle

**Lemma.** Under the preceding hypotheses,

\[
 |\mathcal C|\le3.                                               \tag{6}
\]

*Proof.* If all five outsiders are middle, discard one exceptional
square. The remaining four outsiders together with \(M_1\) are
pairwise actually y-comparable. They give a prohibited y-five-chain.

Suppose now that exactly four outsiders are middle. If they do not
include both exceptional squares, all four together with \(M_1\)
again give an actual y-five-chain. Thus they are \(A,B,F,G\).

The y-projections of \(M_1,M_2\) must overlap in their open interiors.
Otherwise those two squares, \(F,G\), and either one of \(A,B\)
would give an actual y-five-chain.

Consider the four blocks

\[
 I=\{M_1,M_2\},\qquad E=\{A,B\},\qquad \{F\},\qquad \{G\}.
\]

The two nonsingleton blocks each have overlapping open y-projections.
Every pair belonging to different blocks is actually y-separated.
Consequently the four blocks are linearly ordered in y: the union of
the two overlapping intervals in either nonsingleton block is a
connected interval, so an interval separated from both must lie on one
common side of them. Every selection of one square from each block is
an actual y-four-chain.

Block I cannot be an end block, since selecting \(M_1\) as that
endpoint would require \(|x_{M_1}|\le1/8\), contrary to (2). Block E
cannot be an end block either: selecting A and then B in that endpoint
position would give \(|x_A|,|x_B|\le1/8\), contradicting (1).
Therefore I and E are the two internal blocks. Selecting A and B in
turn as the internal member shows

\[
 h_A,h_B<\frac{31}{60},\qquad
 g_A+g_B>\frac{30}{31}.
\]

But both centers are middle, whence

\[
 x_B-x_A<\frac{29}{30}<\frac{30}{31},\qquad
 \frac{30}{31}-\frac{29}{30}=\frac1{930}.
\]

This contradicts (1) and proves (6). QED.

## 3. Three middle outsiders: the exceptional pair is not wholly middle

**Lemma.** If \(|\mathcal C|=3\) and A,B are not both middle, three
outsiders form an actual x-chain.

*Proof.* The three middle outsiders form an actual y-chain. Also,
\(M_1,M_2\) must overlap in their open y-projections: otherwise these
five squares would form an actual y-five-chain. As in Section 2, their
overlapping pair I and the three middle singleton blocks have a linear
y-order. I cannot be an end block of this four-block order, by the
y-four-chain endpoint bound and (2). Reflect y if needed, and denote
the middle outsiders so that

\[
 F_0<_y\{M_1,M_2\}<_yF_1<_yF_2.                                \tag{7}
\]

Applying (2) with the axes interchanged to either choice from I yields

\[
 -\frac{31}{60}<y_{M_1},y_{M_2}<-\frac{29}{60},\quad
 \frac{29}{60}<y_{F_1}<\frac{31}{60},\quad
 \frac{89}{60}<y_{F_2}<\rho.                                    \tag{8}
\]

We will repeatedly use the elementary consequence of the center bound

\[
 |x_S|\ge\frac{29}{60}\quad\Longrightarrow\quad
 |y_S|<\frac{89}{60}.                                          \tag{9}
\]

Indeed,

\[
 29^2+89^2=8762>8281=91^2.
\]

Every left outsider is y-comparable with \(M_1\). It cannot lie below
\(M_1\), because (8) and a center gap at least one would give
\(y_S<-89/60\), contrary to (9). Thus it lies above \(M_1\), and
\(y_S>29/60\). The identical argument applies to right outsiders and
\(M_2\). Two outsiders on the same side, which are y-comparable by
the side-column result, would put the higher one at
\(y>29/60+1=89/60\), also contradicting (9). Therefore there is
exactly one outsider U on the left and one V on the right, and

\[
 y_U,y_V>\frac{29}{60}.                                        \tag{10}
\]

A side outsider not exceptional with \(F_1\) must be x-separated
from \(F_1\). Actual y-separation below \(F_1\) would give
\(y_S<31/60-1=-29/60\), contrary to (10); separation above it would
give \(y_S>29/60+1=89/60\), contrary to (9).

If neither U nor V is exceptional with \(F_1\), this proves the
required actual chain \(U<_xF_1<_xV\).

Otherwise reflect x, interchange \(M_i\) with \(M_{3-i}\), and
rename the side squares if necessary, so that the exceptional pair is
\(U,F_1\). Then \(F_1<_xV\), and

\[
 x_V>x_{F_1}+1>\frac{31}{60},\qquad
 x_{F_1}<\frac{13}{12}-1=\frac1{12}.
\]

The fat-direction condition gives

\[
 x_U\le x_{F_1}-\frac1{\sqrt2}
 <\frac1{12}-\frac1{\sqrt2}<-\frac{31}{60},                    \tag{11}
\]

where \(1/\sqrt2>3/5\). In conjunction with \(|x_U|,|x_V|<13/12\)
and (2), these inequalities show that U horizontally overlaps
\(M_0\), while V horizontally overlaps \(M_3\). Both pairs are
ordinary, so (3) and (10) imply

\[
 y_S\ge h_S+\frac38\qquad(S=U,V).                              \tag{12}
\]

Neither U nor V can be y-separated from \(F_2\). Separation above
\(F_2\) would already violate \(y_S<\rho\). Separation below it
would require

\[
 y_S\le y_{F_2}-h_{F_2}-h_S
 <\frac{61}{60}-h_S
 \le\frac{31}{60},
\]

contradicting (12), whose right side is at least \(7/8\).
These pairs are not exceptional, so both are actually x-separated.
Their column positions force

\[
 U<_xF_2<_xV.
\]

This proves the lemma. QED.

## 4. Three middle outsiders: both exceptional squares are middle

**Lemma.** If \(|\mathcal C|=3\) and A,B are both middle, three
outsiders form an actual x-chain.

*Proof.* Write F for the third middle outsider. From (1) and the middle
strip bounds,

\[
 x_A<\frac{29}{60}-\frac1{\sqrt2}<-\frac18,
 \qquad
 x_B>-\frac{29}{60}+\frac1{\sqrt2}>\frac18.                     \tag{13}
\]

Here \(1/\sqrt2>73/120\), since
\(1/2>73^2/120^2\). Every left outsider S horizontally overlaps A:
A lies to its right, and

\[
 x_A-x_S<\frac{29}{60}+\frac{13}{12}-\frac1{\sqrt2}
 =\frac{47}{30}-\frac1{\sqrt2}<1.                              \tag{14}
\]

The last inequality follows from \(1/\sqrt2>17/30\). Such S also
horizontally overlaps \(M_1\). Thus S is actually y-comparable with
both A and \(M_1\), which themselves are actually y-comparable.

If there were two left outsiders, those two, A, and \(M_1\) would
form an actual y-four-chain. All four have \(|x|>1/8\), by (2),
(4), and (13), contradicting its endpoint bound. Therefore there is at
most one left outsider. The reflected argument using B and \(M_2\)
gives at most one right outsider. Since two outsiders remain, there is
exactly one on each side; call them U and V.

Suppose U were not actually x-separated from F. This ordinary pair
would then be y-separated. Every pair among

\[
 U,\quad M_1,\quad A,\quad F
\]

would be actually y-separated: this follows from (14), the middle
strip overlaps, and the supposition. They would form an actual
y-four-chain. But its two endpoints cannot both have \(|x|\le1/8\),
since only F can satisfy that condition. This is impossible. Therefore
\(U<_xF\). Reflecting gives \(F<_xV\), proving the required chain

\[
 U<_xF<_xV.
\]

QED.

## 5. Completed consequence and the remaining scope

Combining Sections 2–4 proves the following finite capacity reduction.

**Theorem.** Under the hypotheses of Section 1, if at least three of
the five outsiders lie in \(|x|<29/60\), then three outsiders form an
actual x-chain. Together with the given actual four-chain, the sharp
four-plus-three terminal proves \(q\ge Q\).

The cases of four or five middle outsiders are impossible even before
applying that terminal. The case of three middle outsiders produces an
actual three-chain in every placement of the exceptional pair.

Together with the separate side-column analysis, an instance that has
not yet reached the sharp terminal must have either one or two middle
outsiders. Sections 6–12 supply the additional capacity estimates and
physical transfer arguments that close those branches.

## 6. A stronger vertical edge bound in either side column

**Lemma.** Every physical unit square in the Q-disk with
\(|x|\ge29/60\) satisfies

\[
 \boxed{y+h>-\frac56,\qquad y-h<\frac56.}                       \tag{15}
\]

*Proof.* It is enough to prove the first inequality. Suppose instead
that \(y+h\le-5/6\), and put \(X=|x|\), \(Y=-y\), and
\(k=\sqrt{1/2-h^2}\). Then

\[
 Y\ge h+\frac56\ge\frac43.
\]

The center-radius bound implies \(Y>X\). Indeed
\(X^2<\rho^2-16/9=1881/3600<16/9\).

For \(Y\ge X\ge0\), the following two-corner inequality holds for
either orientation sign:

\[
 q\ge\max\{(X+h)^2+(Y+k)^2,
              (X-k)^2+(Y+h)^2\}.                              \tag{16}
\]

To verify it directly, reflect the center into the positive quadrant.
For one orientation sign both displayed points are vertices. For the
other, the vertex with offsets \((k,h)\) has squared norm at least
both expressions: its excess over the first is
\(2(Y-X)(h-k)\ge0\), and its excess over the second is \(4Xk\ge0\).

If \(h\ge5/8\), the second expression in (16) is at least

\[
 (Y+h)^2\ge\left(2h+\frac56\right)^2
 \ge\left(\frac{25}{12}\right)^2>Q,
\]

a contradiction. On \(1/2\le h\le5/8\), the first expression is
at least

\[
 f(h)=\left(\frac{29}{60}+h\right)^2
      +\left(h+k+\frac56\right)^2.
\]

This function is strictly concave. In fact,

\[
 f''(h)=2+2\left(1-\frac h k\right)^2
          -\frac{h+k+5/6}{k^3}<0:
\]

on this interval \(1\le h/k\le5/\sqrt7<2\), \(k\le1/2\), and
\(h+k+5/6>3/2\). Thus the first two terms are less than four and
the subtracted term exceeds twelve.

Both endpoint values exceed Q. At the first,

\[
 f(1/2)=\left(\frac{59}{60}\right)^2
            +\left(\frac{11}{6}\right)^2
       =\frac{15581}{3600}>Q.
\]

At the second, \(k=\sqrt7/8>13/40\), so

\[
 f(5/8)>
 \left(\frac{11}{10}\right)^2
 +\left(\frac{107}{60}\right)^2
 =\frac{15805}{3600}>\frac{15581}{3600}>Q.
\]

Concavity now excludes the entire interval. Reflection in y proves the
other inequality in (15). QED.

**Consequence.** If \(S<_yT<_yE\) is an actual three-chain and
\(|x_S|\ge29/60\), then

\[
 y_E-h_E\ge y_S+h_S+2h_T>\frac16.                              \tag{17}
\]

In particular, the upper exceptional end block above two side-column
squares has both lower edges strictly above \(1/6\). The reflected
statement holds for a lower end block. If all three members of an actual
three-chain belong to side columns, its middle center lies in
\((-1/3,1/3)\), by applying (15) at both ends.

## 7. Two middle outsiders: only a middle-to-side exception remains

Suppose \(|\mathcal C|=2\). Reflect x if needed so that
\(\mathcal L=\{U,V\}\), \(\mathcal R=\{W\}\), and
\(\mathcal C=\{F,G\}\). The left triple
\(\{U,V,M_1\}\) is an actual y-three-chain.

Each middle outsider must either form the exceptional pair with a left
outsider or be actually x-separated from a left outsider. Otherwise it
would be y-comparable with all three squares of that left chain, giving
an actual y-four-chain whose two endpoints cannot both be middle: all
three left-chain squares have \(|x|>1/8\). Any actual x-separation
obtained in this way has the left outsider first, and implies

\[
 x_F>-\frac1{12}\quad\hbox{or}\quad x_G>-\frac1{12},             \tag{18}
\]

respectively, since every left center is above \(-13/12\) and the
necessary center gap is at least one.

The exceptional pair cannot be \(F,G\). In that case both have such
left separators, so their x-gap is less than

\[
 \frac{29}{60}+\frac1{12}=\frac{17}{30}<\frac1{\sqrt2},
\]

contrary to (1).

If the exceptional pair joins no middle square to a side outsider,
both F and G have left separators. If either is actually x-separated
from W, that separator, the middle square, and W give the sharp actual
x-three-chain. Otherwise both are y-separated from W. All six pairs in
\(\{F,G,M_2,W\}\) are then actually y-comparable. This gives an
actual y-four-chain disjoint from the actual y-three-chain
\(\{M_1,U,V\}\), so the same sharp terminal applies with axes
interchanged.

Consequently, any remaining two-middle instance has its unique
exceptional pair joining one middle outsider to one side outsider.
This statement includes both possibilities: the side member can lie in
the two-member side column or in the singleton side column. Neither
possibility is excluded by Section 7 alone. Both are closed below.

## 8. Two transfer facts and the sign of a physical separator

We use the completed physical cap theorems in
`DOWNWARD_THREE_SQUARE_CAP_HAND_PROOF.md` and
`UPWARD_THREE_SQUARE_CAP_ORIENTATION_PROOF.md`. Their combined caller is
as follows. Write

\[
 a=46,\quad b=\frac{27}{2},\quad T=\frac{211}{4}.
\]

Suppose M,N are the endpoints of an actual x-four-chain, and A,B,C are
three other physical squares. Suppose A is actually above M, C is
actually above N, \(B<_xC\), and A,B form a genuine exception with
\(x_B>x_A\). If their physical separating normal points right/up, the
upward transfer theorem applies provided \(y_A-h_A\ge3/8\). If it
points right/down, the downward transfer theorem applies provided
\(y_B-h_B\ge1/8\). The former floor is automatic from A being above
M and \(|y_M|\le1/8\).

In either case the left transfer cap is strict:

\[
 a(-x_M-h_M)+b(1-x_B-h_B)<T.
\]

The ordinary opposite matched cap gives

\[
 a(x_N-h_N)+b(x_C-h_C)\le T.
\]

Their sum is at least

\[
 a\bigl(x_N-x_M-h_M-h_N\bigr)
 +b\bigl(1+x_C-x_B-h_B-h_C\bigr)
 \ge2a+b=2T,
\]

a contradiction. Thus the displayed hypotheses exclude even the closed
Q-disk domain. The separate transfer manuscripts contain the exact
support and scalar proofs; no numerical cap assertion is being used.

### Every physical separating normal points right in the fat direction

The orientation sign needed by this caller is available under (1),
without assuming \(|x_B-x_A|\ge|y_B-y_A|\). For each square,

\[
 g^2-k^2=\frac{(4h^2-1)^2}{16h^2}\ge0,
 \qquad k=\sqrt{1/2-h^2},
\]

so \(g\ge k\). If a normal were \(n=(-p,s)\) with \(p\ge0\),
its top or bottom vertex would give

\[
 H_i(n)\ge |s|h_i-pk_i\ge |s|h_i-pg_i.
\]

Writing \(d=x_B-x_A\), \(e=y_B-y_A\), fatness and genuine
y-projection overlap imply, for \(s\ne0\),

\[
 n\cdot(c_B-c_A)
 \le-p(g_A+g_B)+|s||e|
 <-p(g_A+g_B)+|s|(h_A+h_B)
 \le H_A(n)+H_B(n).
\]

Such a normal cannot separate the physical squares. If \(s=0\), its
center term is nonpositive and cannot separate them either. Therefore
every separating normal directed from A to B has positive x-component.
A horizontal one would itself give an actual x-separation, contrary to
genuineness. Hence one of the two strict transfer cases applies.

### A second source for the lower edge \(1/8\)

Suppose two bottom squares \(U<_xG\) lie below main squares P,Q,
respectively, and B is above both P,Q. Then

\[
 y_B-h_B\ge1+\max(y_U+h_U,y_G+h_G)>\frac18.                    \tag{19}
\]

For the strict inequality, if both bottom top edges were at most
\(-7/8\), circle supports in directions \((-p,-s)\), \((p,-s)\)
and \((p+s)h+H\ge p+s\) would give

\[
 2\sqrt q\sqrt{p^2+s^2}\ge2p+\frac{15}{4}s.
\]

Choose \((p,s)=(2,15/4)\). This gives
\(\sqrt q\ge17/8>\sqrt Q\), a contradiction. Thus one of the two
bottom top edges exceeds \(-7/8\), proving (19).

## 9. Elementary three-chain routing facts

For any actual y-three-chain \(S<_yP<_yE\), the center-radius bound
implies

\[
 y_S<\frac1{60}-h_S,\qquad
 |y_P|<\frac{31}{60},\qquad
 y_E>h_E-\frac1{60}.                                           \tag{20}
\]

For example,
\(y_E> -\rho+h_S+2h_P+h_E\ge h_E-1/60\); the other two
inequalities follow in the same way.

We also retain (9): a side-column center cannot have
\(|y|\ge89/60\). Therefore if a middle square F is the top endpoint
of an actual y-three-chain, every side-column main square \(M_i\)
that is y-comparable with F lies below F. Otherwise

\[
 y_{M_i}>h_F-\frac1{60}+h_F+h_{M_i}
 \ge h_{M_i}+\frac{59}{60}\ge\frac{89}{60},
\]

contradicting (9). The reflected statement holds for a bottom endpoint.

Finally consider a side column containing two outsiders and its inner
main square, hence an actual y-three-chain. Suppose a middle F is above
that inner main square and is the top endpoint of some actual
y-three-chain. The top member S of the side column cannot be the main
square: then F would extend the side triple to an actual y-four-chain
with a forbidden side endpoint. For the same reason S cannot lie below
F in y. It cannot lie above F either, by (20) and (9), as in the preceding
calculation. Thus, provided S,F are an ordinary pair, they are actually
x-separated. If the side is left, \(S<_xF\); if it is right,
\(F<_xS\). In either case \(|x_S|>31/60\), so S horizontally
overlaps the corresponding outer main endpoint. By (20) S has positive
y-coordinate, and the ordinary separation from that endpoint must be
upward. This supplies the matched opposite top square in the transfer
caller.

## 10. The exceptional one-middle branch closes

The only one-middle branch not already giving an actual outsider
x-three-chain is the end-block arrangement of Section 6 of
`PATTERN_II_NINE_SQUARE_CONTINUATION.md`. Reflect x and y as there:
A is the exceptional left outsider, B is the unique middle outsider,
and both lie above two ordered members of the left side column.
The outer square A horizontally overlaps \(M_0\), and is actually
above it.

Section 6 of the present note gives

\[
 y_B-h_B>\frac16>\frac18.
\]

By (20), B is a top endpoint of an actual y-three-chain. It is therefore
above \(M_2\), by Section 9. The top outsider C of the right side
column is ordinary with B. Section 9 supplies

\[
 B<_xC,\qquad M_3<_yC.
\]

Together with \(M_0<_yA\), these are precisely the transfer-caller
hypotheses. Section 8 excludes the genuine exceptional branch at every
\(q\le Q\). This completes the one-middle case.

## 11. Two middle outsiders, exception on the two-member side

Use the notation of Section 7, but rename the exceptional left outsider
A, the other left outsider U, the exceptional middle outsider B, the
other middle outsider G, and the right singleton C.

The ordinary middle square G has an actual left separator. Unless an
outsider x-three-chain has already been obtained, G cannot be x-separated
from C. Thus G and C are actually y-separated.

If B were not x-separated from C, the ordinary pair B,C would be
y-separated. Then \(B,G,M_2,C\) would form an actual y-four-chain,
disjoint from the actual y-three-chain \(A,U,M_1\). This is the sharp
four-plus-three terminal. Hence in a remaining instance

\[
 B<_xC.                                                        \tag{21}
\]

If \(U<_xB\), the triple U,B,C is an actual x-chain, another sharp
terminal. Consequently B is actually y-separated from U. The three
blocks \(\{A,B\},\{U\},\{M_1\}\) are therefore linearly ordered
in y. The exceptional block is connected because A,B genuinely overlap
in y.

From (21), \(x_B<1/12\), and fatness gives

\[
 x_A<\frac1{12}-\frac1{\sqrt2}<-\frac{31}{60}.
\]

Thus A horizontally overlaps \(M_0\), and
\(|y_A|\ge h_A+3/8\). It cannot be the middle member of an actual
y-three-chain, by (20), so the exceptional block is an end block.
Reflect y so it is the upper end. Then A is above \(M_0\), and
Section 6 gives

\[
 y_B-h_B>\frac16.
\]

It remains to record the opposite matched separation. Since B is middle
and \(B<_xC\), we have \(x_C>31/60\), so C horizontally overlaps
\(M_3\). The pair B,C cannot be y-separated in a remaining instance:
otherwise \(B,G,M_2,C\) is the same disjoint actual y-four-chain
used above. Thus their open y-projections overlap. Since B is a top
endpoint of an actual y-three-chain, \(y_B>h_B-1/60\). If C were
below \(M_3\), then

\[
 y_C\le-h_C-\frac38,
 \qquad y_B-y_C>h_B+h_C+\frac{43}{120},
\]

contradicting that overlap. Hence \(M_3<_yC\).

All hypotheses of Section 8 are now present. It excludes the genuine
exceptional branch throughout \(q\le Q\).

## 12. Two middle outsiders, exception on the singleton side

Keep the notation \(\mathcal L=\{U,V\}\),
\(\mathcal C=\{F,G\}\), \(\mathcal R=\{W\}\), and let F,W be
the exceptional pair. Both F and G have actual left separators, by
Section 7, so

\[
 x_F,x_G>-\frac1{12}.
\]

If G is x-separated from W, its left separator, G, and W give the sharp
actual x-three-chain. Otherwise G is actually y-separated from W.
The three blocks

\[
 \{F,W\},\qquad \{G\},\qquad \{M_2\}
\]

are then linearly ordered in y. Fatness gives

\[
 x_W> -\frac1{12}+\frac1{\sqrt2}>\frac{31}{60}.
\]

Thus W horizontally overlaps \(M_3\), and
\(|y_W|\ge h_W+3/8\). By (20) the exceptional block cannot be
middle. Reflect y so it is the top block. In particular W is actually
above \(M_3\), and F is the top endpoint of an actual y-three-chain.

Section 9 gives \(M_1<_yF\). It also supplies an ordinary left
outsider S with

\[
 S<_xF,\qquad M_0<_yS.                                         \tag{22}
\]

Indeed S is the top member of the left actual y-three-chain. We now
prove the lower edge \(y_F-h_F>1/8\).

If \(M_2<_yG\), then \(M_2<_yG<_yF\), with bottom square
\(|x_{M_2}|>29/60\). Section 6 gives the stronger floor
\(y_F-h_F>1/6\).

The remaining order is

\[
 G<_yM_2<_yF.
\]

By (20), \(y_G<1/60-h_G\). The ordinary pair G,\(M_1\) is
y-comparable. If \(M_1<_yG\), then

\[
 y_{M_1}<\frac1{60}-2h_G-h_{M_1}
 \le-\frac{89}{60},
\]

contradicting (9). Therefore

\[
 G<_yM_1<_yF.                                                   \tag{23}
\]

The main square \(M_1\) must be the middle member of its left actual
y-three-chain. If it were bottom, G would extend that chain to an actual
y-four-chain with a forbidden side top endpoint. If it were top, F
would extend it with a forbidden side bottom endpoint. Relabel its two
outsiders so that

\[
 U<_yM_1<_yV.
\]

Neither y-order between U and G is possible. The order \(U<_yG\)
would give \(U<_yG<_yM_2<_yF\), whose bottom endpoint U is a side
square. The order \(G<_yU\) would give
\(G<_yU<_yM_1<_yV\), whose top endpoint V is a side square.
Both contradict the actual four-chain endpoint bound. The ordinary pair
U,G must therefore be actually x-separated, and its column positions
give

\[
 U<_xG.
\]

Now U,G are two bottom squares, \(M_1,M_2\) lie above them
respectively, and F lies above both main squares by (23). Formula (19)
applies and proves

\[
 y_F-h_F>\frac18.
\]

Reflect x and apply the transfer caller to the actual four-chain in
reverse order, with matched outer square A=W, next exceptional square
B=F, and opposite top square C=S from (22). The reflected exceptional
pair remains fat in x, and Section 8 supplies a rightward physical
separating normal. W is above \(M_3\), S is above \(M_0\), and the
reflected comparison is \(F<_xS\). All caller hypotheses hold, so
this last genuine exceptional branch is excluded throughout \(q\le Q\).

## 13. Completed Pattern II lower bound

**Theorem.** Under the hypotheses of Section 1, nine physical squares
require \(q\ge1105/256\).

*Proof.* The side capacities imply that there is at least one middle
outsider. Four or five are impossible by Section 2. Three yield an
actual outsider x-three-chain by Sections 3–4, so the sharp
four-plus-three terminal applies. With one or two middle outsiders,
the side-column and Section 7 reductions either give an actual sharp
terminal or one of the genuine exceptional branches closed in
Sections 10–12. This exhausts the five-square complement. QED.

In the newly closed exceptional branches, the transfer cap is strict
even at q=Q. Therefore every surviving equality instance in this
actual-four-chain class reaches an actual physical four-plus-three
endpoint terminal. This last statement is a reduction to the earlier
equality analysis; it does not supply an unrestricted equality
classification or an unrestricted geometric caller.
