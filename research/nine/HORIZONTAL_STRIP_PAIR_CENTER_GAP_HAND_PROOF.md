# Two unit squares in a strip of height below two have center x-gap >47/60

November 2, 2026. Complete hand proof. No mathematical program,
numerical sampling, Lean, Lake, or CI is used.

## 1. Statement and the strict strip hypothesis

Let two physical unit squares have disjoint interiors and both lie in
one horizontal strip of height strictly less than two. Their frames may
be arbitrary. Then

\[
                         |x_2-x_1|>\frac{47}{60}.
\tag{1}
\]

The strict strip-height premise is essential: two aligned squares
stacked vertically have center x-gap zero and fit a strip of height
exactly two. The constant 47/60 in (1) is sufficient for the intended
caller; no optimality claim is made for it.

Write \(H_S(w)\) for the support halfwidth of a centered physical unit
square S in vector direction w, and
\(h_S=H_S(e_x)=H_S(e_y)\).

## 2. A physical separating normal and both orientation costs

Put a=47/60, and suppose contrary to (1) that the horizontal center gap
d is at most a. Label the squares so that their vertical center gap v
is nonnegative, and reflect the horizontal coordinate if necessary so
their horizontal gap d is also nonnegative.

If the containing strip has height H<2, then

\[
 v+h_1+h_2\le H<2,
 \qquad 0\le v<1,
 \qquad 0\le d\le a<1.
\tag{2}
\]

The first inequality simply measures the distance from the lower-center
square's bottom point to the higher-center square's top point; both
points lie in the strip. It does not assume that these are the global
extremes of their union.

Choose a genuine separating unit normal directed from the lower center
toward the higher center. The sum of the two support halfwidths is at
least one. Since both center coordinate gaps in (2) are below one,
neither component of this normal can be nonpositive. Thus write

\[
 n=(p,q),\qquad p>0,\quad q>0,\quad p^2+q^2=1,
\]

with separating inequality

\[
 p d+q v\ge H_1(n)+H_2(n).
\tag{3}
\]

The exact two-vector orientation minimum proved in
`TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md` gives, for each square,

\[
 H_S(n)+q h_S\ge\frac12+\frac{q(p+q)}2.
\tag{4}
\]

Indeed the two vectors here are n and q e_y, with lengths one and q;
their absolute dot product plus absolute determinant is q(p+q).
This bound retains both squares' orientation costs, rather than
replacing either entire square by its inscribed disk.

Add q(h_1+h_2) to (3), sum the two inequalities (4), and use (2):

\[
 p d+q(v+h_1+h_2)\ge1+q(p+q),
\]

so

\[
 p d>1+q(p+q)-2q=(1-q)^2+pq.
\tag{5}
\]

If q≥a, (5) already gives d>q≥a, a contradiction. It remains to
show, for 0≤q≤a and p=√(1−q²), that

\[
                         (1-q)^2>p(a-q).
\tag{6}
\]

## 3. One cubic, with a complete hand positivity check

Both sides in (6) are nonnegative. The difference of their squares is

\[
 \begin{aligned}
 (1-q)^4-(1-q^2)(a-q)^2
  &=(1-q)\bigl((1-q)^3-(1+q)(a-q)^2\bigr)\\
  &=\frac{1-q}{3600}P(q),
 \end{aligned}
\tag{7}
\]

where the complete coefficient list is

\[
              P(q)=1391-7369q+12840q^2-7200q^3.
\tag{8}
\]

For clarity, expansion of the expression inside the large parentheses
in (7) gives

\[
 (1-a^2)+(-3-a^2+2a)q+(2+2a)q^2-2q^3.
\]

Substitution of a=47/60 and multiplication by 3600 gives exactly (8).

Its derivatives and the useful anchor values are

\[
 P'(q)=-7369+25680q-21600q^2,
 \qquad P''(q)=25680-43200q,
\]

\[
 P(1/2)=\frac{33}{2},\qquad P'(1/2)=71,
 \qquad P(a)=\frac{2197}{60}.
\tag{9}
\]

The first two anchors follow by direct substitution. For the last,
the unexpanded expression in (7) at q=a is (1−a)³, so
\(P(a)=3600(13/60)^3=2197/60\).

On 0≤q≤1/2, the second derivative is at least 4080. Integration
from the anchor 1/2 and completion of the square give

\[
 \begin{aligned}
 P(q)&\ge\frac{33}{2}+71(q-1/2)+2040(q-1/2)^2\\
     &\ge\frac{33}{2}-\frac{71^2}{8160}
      =\frac{129599}{8160}>0.
 \end{aligned}
\tag{10}
\]

On [1/2,107/180], P'' is nonnegative, so P'≥71 and P increases.
On [107/180,a], P is concave, since P''≤0. Its minimum on that
last interval is therefore at an endpoint. The first endpoint already
has value at least P(1/2)>0, and the other has the positive value P(a)
from (9). These intervals cover [0,a], proving P>0 there.

Equation (7) is strictly positive, and taking positive square roots
proves (6). Substitution into (5) now gives

\[
 p d>p(a-q)+pq=pa,
\]

so d>a, the final contradiction. This proves (1) for all physical
orientations and all relative center heights.

## 4. Application to the whole-cap reduction for an actual four-chain

Put \(Q=1105/256\), \(R=\sqrt Q\), and suppose a physical unit is
Q-contained and lies wholly above y=1/10. It lies in the horizontal
strip [1/10,R], whose height is less than two:

\[
                         R-\frac1{10}<2.
\]

For example, R<25/12<21/10 proves this strict comparison. Therefore
any two such units have center x-gap greater than 47/60. Reflection
gives the corresponding statement for units wholly below −1/10.

Now suppose these are outsiders of an actual horizontal four-chain.
Their established unrestricted center strip is

\[
                         -\frac{13}{12}<x<\frac{13}{12}.
\tag{11}
\]

If three upper outsiders are ordered by center x-coordinate as L,A,B,
then both adjacent gaps exceed 47/60. In particular the middle center
satisfies

\[
 -\frac3{10}
   =-\frac{13}{12}+\frac{47}{60}
   <x_A<\frac{13}{12}-\frac{47}{60}
   =\frac3{10}.
\tag{12}
\]

The two outer centers then satisfy

\[
 x_L<x_A-\frac{47}{60}< -\frac{29}{60},\qquad
 x_B>x_A+\frac{47}{60}>\frac{29}{60}.
\tag{13}
\]

Thus every three-unit upper cap consists of exactly one left-side
outsider, one middle outsider with |x|<3/10, and one right-side outsider.
This is a physical routing theorem. It does not assert that their full
horizontal projections form an actual three-chain.

There cannot be four upper outsiders: their center span would exceed
\(3(47/60)=47/20>13/6\), contrary to (11). The same holds below.

In the bounded-inner-height setting of
`UNRESTRICTED_ACTUAL_FOUR_CHAIN_FULL_SIDE_MAIN_HEIGHT_HAND_PROOF.md`,
all five outsiders belong to the upper or lower whole caps. Their
occupancy counts must therefore be three and two. The three-unit class
has precisely the routing (12)--(13). The two-unit class can contribute
at most two middle outsiders, so there are at most three middle
outsiders in total in this bounded-inner-height case.

The joint geometric exclusion of the routed three-unit cap beside the
two outer main squares remains a separate obligation. The present proof
does not replace oblique physical separators by coordinate comparisons.

## 5. A gap greater than four fifths in a slightly shorter strip

If the common containing strip has height

\[
                            H\le\frac{87}{44},
\]

then the stronger conclusion is

\[
                         |x_2-x_1|>\frac45.
\tag{14}
\]

Suppose contrariwise that d<=4/5. Since H<2, the same genuine
separating-normal argument as in Section 2 applies, with p,q>0.
Keeping H in that argument gives

\[
 p\left(d-\frac45\right)
 \ge 1+pq+q^2-\frac{87}{44}q-\frac45p.
\tag{15}
\]

Use the half-angle variable

\[
 w=\sqrt{\frac{1-q}{1+q}}\in(0,1),\qquad
 p=\frac{2w}{1+w^2},\qquad
 q=\frac{1-w^2}{1+w^2}.
\]

Multiplication of the right side of (15) by the positive denominator
\(220(1+w^2)^2\) gives exactly

\[
                    P(w)=875w^4-792w^3+88w+5.
\tag{16}
\]

Here is a complete positivity check on [0,1]. Its derivatives are

\[
 P'=3500w^3-2376w^2+88,\qquad
 P''=10500w^2-4752w.
\]

The sole positive zero of P'' is 396/875, which is less than 3/5.
Thus P is concave on [0,396/875]. On [396/875,3/5], P' increases
to the still-negative value

\[
                         P'(3/5)=-\frac{284}{25}.
\]

It follows that the minimum of P on [0,3/5] occurs at zero or at
3/5. Both values are positive:

\[
                         P(0)=5,\qquad P(3/5)=\frac{16}{125}.
\tag{17}
\]

On [3/5,1], P'' increases and
\(P''\ge P''(3/5)=4644/5>900\). At the rational anchor w0=5/8,

\[
                 P(w_0)=\frac{635}{4096},\qquad
                 P'(w_0)=\frac{1839}{128}.
\]

Integrating the second-derivative bound and completing the square gives

\[
 \begin{aligned}
 P(w)&\ge P(w_0)+P'(w_0)(w-w_0)+450(w-w_0)^2\\
     &\ge\frac{635}{4096}
            -\frac{(1839/128)^2}{1800}
       =\frac{1190079}{29491200}>0.
 \end{aligned}
\tag{18}
\]

Equations (16)--(18) make the right side of (15) strictly positive,
contradicting d<=4/5. This proves (14).

### The precise bounded-inner-height caller

The strengthened main-height and adjacent-proxy bounds in
`UNRESTRICTED_ACTUAL_FOUR_CHAIN_FULL_SIDE_MAIN_HEIGHT_HAND_PROOF.md`
give each upper outsider the whole lower edge

\[
                            y-h>\frac{187}{1860}.
\tag{19}
\]

Together with Q-containment, this puts the unit in a strip of height
less than 87/44. In exact arithmetic,

\[
 \sqrt Q<\frac{187}{90},\qquad
 \frac{187}{90}-\frac{187}{1860}
       =\frac{11033}{5580}<\frac{87}{44}.
\tag{20}
\]

The first squared comparison has numerator reserve
\(187^2\cdot256-1105\cdot8100=1564>0\); the last difference is
\(1/30690>0\).

Consequently three upper outsiders, ordered by x-center as L,A,B,
have both adjacent center gaps greater than 4/5. The unrestricted
outsider bound |x|<13/12 then gives

\[
                    |x_A|<\frac{17}{60},\qquad
                    x_L<-\frac{31}{60},\qquad
                    x_B>\frac{31}{60}.
\tag{21}
\]

In particular each outer upper center lies horizontally beyond the
corresponding internal main center, whose absolute x-coordinate is
strictly less than 31/60. The reflected conclusions hold for the lower
whole cap. These are center-order restrictions; no actual horizontal
projection chain or shoulder-to-endpoint vertical comparison is inferred.
