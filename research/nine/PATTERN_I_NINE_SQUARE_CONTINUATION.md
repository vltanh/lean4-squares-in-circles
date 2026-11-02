# Pattern I with nine squares: rank reductions and new capacity terminals

Hand continuation after ec0d76e, November 1, 2026. No mathematical script,
Lean, or CI is used. The results below are proved reductions and terminals;
the remaining middle-duplicate cases are not asserted closed.

We use the notation and the actual projection orders from
[ONE_EXCEPTION_HEIGHT_FOUR_CONTINUATION.md](ONE_EXCEPTION_HEIGHT_FOUR_CONTINUATION.md).
Thus all nine physical unit squares lie in a disk of squared radius
\(q\le Q=1105/256\), and all pairs except the genuine exceptional pair
\(A,B\) are separated in at least one of two perpendicular projection
directions. Put
\[
 \rho=\frac{91}{60},\qquad h_S\in[1/2,1/\sqrt2],\qquad
 g_S=\frac1{4h_S},\qquad k_S=\sqrt{1/2-h_S^2}.
\]
Every center has norm strictly below \(\rho\). The physical square contains
an aligned square of halfwidth \(g_S\), and \(h_S+g_S\ge1\).

An actual comparison \(S<_xT\) means
\(x_T-x_S\ge h_S+h_T\); define \(<_y\) likewise. Pattern I is
\[
 x_B-x_A\ge g_A+g_B,\qquad B<_xC<_xD,
 \qquad L<_xM<_xR.                                      \tag{1}
\]
The seven displayed squares are distinct, and two further squares remain
present. The comparisons \(A<_xC,D\) are actual. We may exclude branches
already handled by the physical sharp four-plus-three endpoint terminal.
The localization proved in the cited note then gives, after a reflection
in y,
\[
 L<_yA,\quad L<_yB,\qquad x_A<-\frac{59}{60}-g_A.
                                                               \tag{2}
\]
In particular, \(|x_A|>4/3\) and hence \(|y_A|<3/4\).

## 1. The only three x-rank column profiles

Assume in this section that both original actual projection orders have
height at most three. Width five is already handled by the earlier sharp
terminal, so we restrict to width at most four in both directions.

The actual x-three-chains \(A,C,D\), \(B,C,D\), and \(L,M,R\) force
the following longest-chain x-ranks:
\[
 r_x(A)=r_x(B)=r_x(L)=1,
 \qquad r_x(C)=r_x(M)=2,
 \qquad r_x(D)=r_x(R)=3.                                  \tag{3}
\]
Both further squares cannot have rank one, since that would give an
x-antichain of size five. Both cannot have rank two or both have rank
three: such a four-element rank level contains neither exceptional square,
so its members form an actual y-four-chain. Therefore the column sizes,
from x-rank one to three, are exactly
\[
                  (3,3,3),\qquad(4,3,2),\qquad(4,2,3).    \tag{4}
\]

Every column not containing the exceptional pair is an actual y-chain.
In particular, a column of size three has y-ranks exactly 1,2,3.
Two squares with the same x-rank and the same y-rank must be the exceptional
pair: otherwise the coordinate cover would force a comparison in one of
the orders, contradicting equality of its ranks.

If the first column has size four, its exceptional squares consequently
share a y-rank, and its other two squares fill the other two ranks.
By (2), the duplicated rank is either two or three.

## 2. The full three-column profile reduces to a middle duplicate

The following arguments use the far-endpoint obstruction in Section 2 of
[ONE_EXCEPTION_TRANSVERSE_GRID_HAND_PROOF.md](ONE_EXCEPTION_TRANSVERSE_GRID_HAND_PROOF.md):
a weak chain \(A,B,C,D\) as in (1) cannot have its nonexceptional far
endpoint \(D\) at either end of any actual perpendicular three-chain.

Suppose the profile is \((3,3,3)\). Write the third column in y-order as
\(V<_yD<_yU\). This labeling is forced: its endpoints are excluded as
possible positions of \(D\), so \(D\) has y-rank two.

Neither \(C<_xV\) nor \(C<_xU\) is possible. Each would make
\(A,B,C,V\) or \(A,B,C,U\) a weak four-chain ending at an actual
y-three-chain endpoint. The reverse x-comparisons are impossible by the
x-ranks. Thus C is y-separated from V and U. The y-height bound forces
\[
                       V<_yC<_yU.                       \tag{5}
\]
Indeed, putting C below V or above U would give an actual y-four-chain.
It follows that C also has y-rank two. Write the second column as
\(S<_yC<_yT\).

Equal y-ranks and the original coordinate cover give the actual comparisons
\(S<_xV\) and \(T<_xU\). Neither \(B<_xS\) nor \(B<_xT\) can
hold: the weak chains \(A,B,S,V\) and \(A,B,T,U\) would have forbidden
far endpoints. The reverse x-comparisons are again excluded by x-ranks.
The y-ranks therefore force
\[
                        S<_yB<_yT.                      \tag{6}
\]
Thus B has y-rank two. By (2), L has y-rank one, and A has y-rank two
or three.

If A has rank three, all nine rank pairs are distinct. This is precisely
the full-grid transverse branch closed in Sections 4--5 of
`ONE_EXCEPTION_TRANSVERSE_GRID_HAND_PROOF.md` (with the outer exceptional
square called P there). Consequently the only remaining profile
\((3,3,3)\) has the rank diagram
\[
\begin{array}{ccc}
 \text{missing}&T&U\\
 A,B&C&D\\
 L&S&V
\end{array}.                                             \tag{7}
\]
These are rank cells, not coordinates of centers. All row comparisons
except A,B are actual, and the two right columns are actual y-three-chains.

## 3. A small negative-offset quadrant exclusion

No physical Q-contained unit square can satisfy
\[
                   x+h<\frac1{60},\qquad y+h<-\frac9{10}.
                                                               \tag{8}
\]
Here the first boundary is slightly to the right of the origin, so the
positive-offset quadrant lemma is not being invoked.

If \(h\ge3/5\), the lowest vertex satisfies
\(|y-h|>2h+9/10\ge21/10\), already giving \(q>441/100>Q\).
Otherwise \(1/2\le h\le3/5\), and
\[
 h+k\ge\frac35+\sqrt{\frac7{50}}>\frac{97}{100}.
\]
The square's outward bottom-left vertex has offsets \((-h,-k)\) or
\((-k,-h)\). Since \(-x>h-1/60\) and \(-y>h+9/10\), its squared
norm is respectively greater than
\[
 \left(\frac{59}{60}\right)^2+
 \left(\frac{187}{100}\right)^2
 =\frac{200873}{45000}>Q,
\]
or greater than
\[
 \left(\frac{143}{150}\right)^2+
 \left(\frac{19}{10}\right)^2
 =\frac{101674}{22500}>Q.
\]
The conclusion (8) follows in both orientation cases.

### An orthogonal-chain consequence

Suppose the outer exceptional square A in (1) is the upper endpoint of
an actual y-three-chain
\[
                              K<_yF<_yA.                \tag{9}
\]
Then K cannot also start an actual x-three-chain.

Section 4 of `ONE_EXCEPTION_TRANSVERSE_GRID_HAND_PROOF.md` gives
\(h_A>13/20\). Using (2) and the center-radius bound,
\(|y_A|<3/4\). Thus (9) gives
\[
 y_K+h_K\le y_A-h_A-2h_F
 <\frac34-\frac{13}{20}-1=-\frac9{10}.                   \tag{10}
\]
If K starts an actual x-three-chain, its far endpoint has center x below
\(\rho\), so
\[
                     x_K+h_K<\rho-\frac32=\frac1{60}.
\]
This contradicts (8). No simultaneous chain-partition assertion is used.

## 4. Every duplicated-top profile is closed

Suppose the first column has size four and A,B share y-rank three.
Name its other members K at rank one and F at rank two. Since all the
other pairs in that column are y-comparable,
\[
                   K<_yF<_yA,\qquad K<_yF<_yB.           \tag{11}
\]
Exactly one of the other columns has size two; the other has size three.

If the size-two column includes a member of y-rank three, the top rank
row has A,B and one square in each of the other two columns. Call those
two squares T and U in x-order. Equal y-ranks force the actual comparisons
\(B<_xT<_xU\). Therefore \(A,B,T,U\) is a weak four-chain.
But y-rank three means that U ends an actual y-three-chain, contradicting
the far-endpoint obstruction.

If the size-two column omits y-rank three, it contains both ranks one and
two. The entire bottom row is then present, so K starts an actual
x-three-chain. Equations (11) and the orthogonal-chain consequence of
Section 3 exclude this alternative.

Thus both column profiles \((4,3,2)\) and \((4,2,3)\) are closed when
the exceptional pair duplicates the top rank. Combined with Section 2,
every remaining original-height-three Pattern I configuration has A,B
duplicating the middle y-rank.

## 5. A vertical-span terminal for the four-member first column

For the remaining first-column size four, name its ranks
\[
                  L\ (1),\qquad A,B\ (2),\qquad F\ (3).
\]
Its actual comparisons give L below both exceptional squares and F above
both. Consequently
\[
 y_F-y_L\ge h_L+h_F+h_A+h_B+|y_A-y_B|.                   \tag{12}
\]
If
\[
                         h_A+h_B+|y_A-y_B|\ge2,          \tag{13}
\]
(12) supplies a physical long endpoint span \(2+h_L+h_F\).
The other full column is a disjoint actual y-three-chain and supplies
the short span. The already proved sharp endpoint terminal yields
\(q\ge Q\). If (13) is strict, it excludes even q=Q.

Thus a strict subcritical counterexample in either four-member-column
profile must obey
\[
                         h_A+h_B+|y_A-y_B|<2.            \tag{14}
\]
This is a necessary condition, not a contradiction. The horizontal
exceptional union span is greater than two by the physical pair-span
lemma; (14) says the perpendicular union span is still below two.

### All remaining profiles have a common three-row form

After a possible reflection in y and relabeling ordinary cells, every
remaining configuration from Section 1 has all the following actual rank
rows:
\[
\begin{array}{c|c}
 \text{y-rank}&\text{members in increasing x-rank}\\ \hline
 3&\text{two squares, with one of the three columns absent}\\
 2&A,B,C,D\\
 1&L,M,R
\end{array}.                                             \tag{20}
\]
The middle row is the weak x-four-chain in (1), and the bottom row is
an actual x-three-chain. The top row is an actual x-two-chain. All
within-column comparisons other than A,B are actual y-comparisons.

For profile \((3,3,3)\), this is already (7), with the top-left cell
absent.

For profile \((4,2,3)\), the far-endpoint argument used in Section 2
still forces D and C to y-rank two. The two-member middle column contains
C and exactly one endpoint rank. If that endpoint is above C, reflect y;
the two full columns reverse their ranks, while their middle members
remain middle. The new middle column then contains ranks one and two,
giving (20) with its top-middle cell absent.

For profile \((4,3,2)\), the first and second columns are full actual
y-three-chains (with the exceptional middle pair duplicated in the first).
The two members of the last column are actually y-comparable. The
far-endpoint obstruction says that D has neither two successive actual
y-predecessors nor two successive actual y-successors. Orient y so the
other member of its column is below D. Then D has y-rank exactly two,
and that other member has y-rank one. This argument remains valid even
if the old rank diagram's missing cell was its right-middle cell: ranks
in the reflected order are recomputed as longest-chain ranks, not merely
renamed by the rule \(j\mapsto4-j\).

Both full columns have all three ranks in either orientation. Let C now
denote the actual middle member of the second column. Since A,B,C,D
have equal y-rank, the original coordinate cover gives the actual
comparisons \(B<_xC<_xD\). The bottom row similarly gives the disjoint
actual chain \(L<_xM<_xR\). This is (20) with its top-right cell absent.
Relabeling C does not introduce any artificial comparison.

Thus (20) is a common nine-body geometric capacity target. It is not an
assertion that centers in one rank row have equal physical y-coordinates.

## 6. An aggregate support terminal for an actual three-chain

Let \(L<_xM<_xR\) be any actual physical three-chain, and suppose
\[
                  y_L+h_L\le-a,\qquad y_R+h_R\le-b,
                  \qquad 2+a+b>0.                       \tag{15}
\]
Then
\[
                         4q\ge9+(2+a+b)^2.              \tag{16}
\]
In particular, if the sum of the two endpoint top edges is at most
\(-7/8\), then \(q\ge1105/256\).

For a physical square S, let \(H_S\) denote its centered support function.
The inscribed aligned square and \(h_S+g_S\ge1\) imply, for p,s>0,
\[
 (p+s)h_S+H_S((\pm p,-s))
 \ge(p+s)(h_S+g_S)\ge p+s.                              \tag{17}
\]
Apply disk support to L and R in directions \((-p,-s)\) and \((p,-s)\).
The actual chain gives \(x_R-x_L\ge1+h_L+h_R\), and (15) gives
\(-y_L-y_R\ge h_L+h_R+a+b\). Therefore
\[
 \begin{aligned}
 2\sqrt q\sqrt{p^2+s^2}
 &\ge p(x_R-x_L)-s(y_L+y_R)
       +H_L((-p,-s))+H_R((p,-s))\\
 &\ge3p+(2+a+b)s.
 \end{aligned}
\]
Choose \(p:s=3:(2+a+b)\) to obtain (16).

This argument retains all physical orientations. In particular, it does
not require either endpoint to be aligned or the middle center to lie at
the origin. It can combine asymmetric estimates on the two top edges.

## 7. A stronger coordinate bound when the outer square ends a three-chain

If the outer square A of the weak chain (1) is the upper endpoint of any
actual y-three-chain, then
\[
                  x_A>-1-g_A,\qquad x_D>1+h_D,
                  \qquad x_B+h_B>0.                    \tag{18}
\]
The reflected statement holds for a lower endpoint.

Indeed y_A>h_A-1/60. If \(-x_A\ge1+1/(4h_A)\), the center norm
would exceed \(\rho\), as the following scalar inequality shows:
\[
 \left(1+\frac1{4h}\right)^2+
 \left(h-\frac1{60}\right)^2>\left(\frac{91}{60}\right)^2
 \quad\left(\frac12\le h\le\frac1{\sqrt2}\right).        \tag{19}
\]
For a direct hand verification put
\[
 f(h)=h^2+\frac1{2h}+\frac1{16h^2}-\frac h{30}.
\]
The difference in (19) is \(f(h)-13/10\). We have
\[
 f''(h)=2+\frac1{h^3}+\frac3{8h^4}>0,
 \quad f(7/10)=\frac{3847}{2940},
 \quad f'(7/10)=-\frac{187}{10290}.
\]
Since \(h\le1/\sqrt2<71/100\), the tangent bound for a convex function
gives
\[
 f(h)\ge\frac{3847}{2940}-\frac{187}{1029000}>\frac{13}{10}.
\]
Thus \(x_A>-1-g_A\). Summing the weak-chain comparisons gives
\(x_D\ge x_A+g_A+2+h_D>1+h_D\). Likewise,
\[
 x_B+h_B\ge x_A+g_A+(g_B+h_B)>-1+1=0.
\]
This strengthening uses only the center-radius bound and an actual
perpendicular three-chain. The narrower halfwidth and common-point
conclusions in the transverse-grid note remain available independently.

## 8. Exact scope still requiring a continuation

All reductions above retain the ninth physical square. They close every
duplicated-top rank arrangement, and the transverse-grid theorem closes
the remaining distinct full-grid arrangement. The unresolved
original-height-three Pattern I cases now have the exceptional pair
duplicating the middle y-rank. Their x-rank column sizes remain one of
(4), with the additional restrictions in Sections 2 and 5.

The aggregate support inequality (16) is a terminal available for those
cases; the necessary endpoint depth bound has not yet been deduced for
every remaining arrangement. The complete rank normalization (20) handles
even a rightmost column that initially omitted its middle rank, but does
not yet prove the required capacity bound for the resulting physical
three-row form. No global one-exception theorem, unrestricted geometric
caller, or equality classification is claimed by this note.

## 9. Uniqueness of the far endpoint and an additional actual comparison

Fix the exceptional edge A,B and its fat ordering in (1). There is at
most one square T that can be the far endpoint of a weak chain
\[
             x_B-x_A\ge g_A+g_B,\qquad B<_xS<_xT.        \tag{21}
\]
Here the intermediate square S may vary.

Every such T obeys
\[
 x_T\ge x_A+g_A+2+h_T>
 h_T+\frac{29}{60}+\frac1{2\sqrt2}>h_T+\frac56.          \tag{22}
\]
The last strict inequality uses \(1/(2\sqrt2)>7/20\). In particular
\(4/3<x_T<91/60\). Two distinct far endpoints cannot have separated
x-projections: their centers differ in x by less than \(11/60<1\).
Neither far endpoint is exceptional, so their pair must be actually
y-separated.

Suppose \(U<_yV\) were two such endpoints. Apply circle supports in
directions \((p,-s)\) and \((p,s)\), with p,s>0. Formula (17), the
y-separation, and (22) give
\[
 2\sqrt q\sqrt{p^2+s^2}
 >\frac53p+2(p+s)=\frac{11}{3}p+2s.
\]
Choosing \(p:s=11/6:1\) yields
\[
                      q>\left(\frac{11}{6}\right)^2+1
                       =\frac{157}{36}>Q,
\]
a contradiction. This proves uniqueness.

In the normalized three-row form (20), it follows that
\[
                              M<_yB.                    \tag{23}
\]
Indeed, \(B<_xM\) would give the second weak four-chain A,B,M,R,
with far endpoint R distinct from D. The reverse x-comparison is
excluded by x-ranks, and the y-ranks force the displayed direction.
Thus B is actually above both L and M. No virtual comparison is used
in (23).

Let \(T<_xU\) denote the two actual top-row squares. Then
\[
                              B<_yT.                    \tag{24}
\]
If T lies in the first column, this follows from that column's actual
y-order. Otherwise T has x-rank two. The comparison \(B<_xT\) would
produce the forbidden second far endpoint U, and \(T<_xB\) is
impossible by x-ranks. The coordinate cover and y-ranks give (24).

In particular, B has the actual lower neighbor M and upper neighbor T.
The center-radius bound therefore gives
\[
         |y_B|<\frac{61}{60}-h_B\le\frac{31}{60}.         \tag{25}
\]
Equivalently its entire y-projection lies strictly between
\(-61/60\) and \(61/60\). This uses actual comparisons in both
directions, independently of the relative center heights of A and B.

The subsequent common-lower-square cap in
[PATTERN_I_COMMON_LOWER_CAP_HAND_PROOF.md](PATTERN_I_COMMON_LOWER_CAP_HAND_PROOF.md)
closes every normalized configuration whose exceptional pair has a
right/down physical separating normal of slope at most 27/46. Its
proof is independent of any floor assumption on the exceptional pair.

The companion
[PATTERN_I_UPWARD_CAP_HAND_PROOF.md](PATTERN_I_UPWARD_CAP_HAND_PROOF.md)
uses the actual upper neighbor in (24) and closes upward physical
separators of slope at most 18/25.

## 10. Owned separating directions when the perpendicular union is short

The two profiles with a four-member first column have the necessary
condition (14), unless a previously proved sharp terminal already applies.
Write
\[
 d=x_B-x_A,\quad v=|y_B-y_A|,\quad H=h_A+h_B,
 \qquad W=d+H,\quad V=v+H<2.                             \tag{26}
\]
The weak middle chain gives the additional uniform bound
\[
                    W<\rho+r-\frac32<\frac{377}{180}.  \tag{27}
\]
Indeed the leftmost x-projection of A gives \(-x_A\le r-h_A\),
while \(x_D<\rho\). The actual suffix B,C,D then gives
\(d+H<\rho+r-2h_C-h_D\le\rho+r-3/2\). For the last rational
bound use \(r<187/90\), whose squared check is
\(34969\cdot256>1105\cdot8100\).

### All separating normals point right

Put \(k_S=\sqrt{1/2-h_S^2}\). Since
\[
            g_S^2-k_S^2=\frac{(4h_S^2-1)^2}{16h_S^2}\ge0,
\]
fat x implies \(d\ge g_A+g_B\ge k_A+k_B\).
For a prospective normal \((-p,\pm s)\), where p≥0 and s>0, the
sum of physical supports is at least
\[
                         sH-p(k_A+k_B).
\]
This follows by using each square's vertex of maximal signed y-offset;
its x-offset has absolute value k_S. The corresponding center dot
product is at most \(sv-pd\), strictly smaller because the actual
y-projections of the exceptional pair overlap, so v<H. If s=0 its
center dot is nonpositive. Thus no separating normal points left or
vertically. This conclusion only needs the genuine exception and fat x;
it does not require V<2.

### A whole interval of owned slopes is excluded

For two squares, the separating-axis theorem supplies a separating normal
parallel to a side axis of one of the squares. Call such a normal owned.
An elementary justification is to use the Minkowski difference of the
two squares: its edges are parallel to physical square sides, and an
exterior point violates at least one corresponding edge half-plane.

Write an owned separating normal as \(n=(p,\pm s)\), with
p>0, s≥0, and \(p^2+s^2=1\). Its owner has halfwidth
\((p+s)/2\) and support \(1/2\) in this direction. For the other
square, (17) gives
\[
                (p+s)h_{\mathrm{other}}+H_{\mathrm{other}}(n)
                 \ge p+s.
\]
Therefore physical separation implies
\[
                         pW+sV\ge1+p+s+ps.             \tag{28}
\]
This follows by adding \((p+s)H\) to the normal separation inequality;
the owner's contribution is
\(1/2+(p+s)^2/2=1+ps\).

Using (26)--(27) in (28), an owned separator must satisfy
\[
                    p\left(\frac{197}{180}-s\right)+s>1.
                                                               \tag{29}
\]
Put \(z=s/p\). Multiplying by positive denominators and squaring the
positive quantities in (29) gives the necessary condition
\[
 P(z):=6120z^3-25991z^2+6120z+6409>0.                    \tag{30}
\]

However
\[
                         P(z)<0
                 \qquad\left(\frac{18}{25}\le z\le\frac{15}{4}\right).
                                                               \tag{31}
\]
For a direct hand check, \(P'\) is an upward quadratic and
\[
                     P'(18/25)=-\frac{13618260}{625}<0.
\]
Hence, after that left endpoint, P first decreases and then increases,
with at most one intervening minimum. Its maximum on the interval is
at an endpoint. The exact endpoint values are
\[
 P(18/25)=-\frac{5844635}{15625}<0,
 \qquad P(15/4)=-\frac{214481}{16}<0.
\]
This proves (31), contradicting (30).

Consequently, in the two top-left-present diagrams subject to V<2,
no owned separating normal has slope between 18/25 and 15/4, for either
vertical sign. Together with the upward cap, all owned upward slopes
through 15/4 are excluded in these diagrams. Owned downward slopes
through 27/46 are already excluded by the common-lower cap; the interval
between 27/46 and 18/25 and slopes above 15/4 still require further
arguments. The top-left-missing diagram does not yet supply V<2, so this
section does not silently apply that hypothesis to it.
