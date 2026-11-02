# Endpoint reserves survive an arbitrary weak middle link

November 2, 2026 UTC (November 1 in America/Chicago). Hand proof only;
no scripts, numerical search, Lean, Lake, or CI.

Let A,B,C,D be a completed x-four-chain in the closed disk
Q=1105/256. Assume only that A--B and C--D are actual x-projection
comparisons. The middle link may be weak. Put

\[
 \rho=\frac{91}{60},\quad
 g_S=\frac1{4h_S},\quad k_S=\sqrt{\frac12-h_S^2},\quad
 \eta_S=h_S+g_S-1,
\]

and set

\[
 U=h_A+h_D-1,\qquad V=\eta_B+\eta_C,\qquad
 S=|y_A|+|y_D|.
\]

The universal center bound |c|<rho and the physical pair-span theorem
are the previously proved inputs. The preceding note
`COMPLETED_MIDDLE_LINK_SHARP_TERMINAL_HAND_PROOF.md` gives

\[
                    x_D-x_A\ge3+U+V.
\tag{1}
\]

For an actual middle link the same quantitative inequality follows
from h>=g, so (1) holds in both cases.

## 1. Endpoint localization and the surviving transverse budget

From (1) and |c|<rho we obtain

\[
 -\rho<x_A<-\frac{89}{60},\qquad
 \frac{89}{60}<x_D<\rho,
 \qquad U+V<\frac1{30}.
\tag{2}
\]

In particular 1/2<=h_A,h_D<8/15. Their center heights satisfy
|y_A|,|y_D|<1/sqrt(10), since
rho^2-(89/60)^2=1/10. Thus each endpoint has X=|x|>Y=|y|.

An actual outward-quadrant corner has offsets either (h,k) or (k,h)
in coordinates directed toward the center's signs. The second choice
has the smaller squared norm when X>Y. Hence every endpoint satisfies

\[
                         (X+k)^2+(Y+h)^2\le Q.
\]

Adding their two nonnegative corner vectors and using the triangle
inequality, followed by (1), gives

\[
 4Q\ge
 (2+h_A+k_A+h_D+k_D+V)^2+(S+h_A+h_D)^2.
\tag{3}
\]

The concavity chord already used in the actual-four-chain strip proof is

\[
 h+\sqrt{\frac12-h^2}\ge
       1-\frac{73}{1000}\left(h-\frac12\right)
       \qquad\left(\frac12\le h\le\frac8{15}\right).
\tag{4}
\]

For completeness, the two sides agree at 1/2. At 8/15 the right-hand
comparison requires k>=13927/30000; squaring is justified because both
sides are positive, and the difference is

\[
 \frac{97}{450}-\left(\frac{13927}{30000}\right)^2
                 =\frac{38671}{900000000}>0.
\]

Concavity proves (4) on the interval. Substituting it into (3) yields

\[
       4Q\ge(4-73U/1000+V)^2+(S+1+U)^2.
\tag{5}
\]

**Theorem.** The endpoint heights and orientation excesses obey

\[
 \boxed{\ S+\frac{37}{50}U+\frac{32}{9}V\le\frac18.\ }
\tag{6}
\]

To prove it, suppose the left side is at least 1/8. Then
S+1+U>=9/8+13U/50-32V/9. This lower bound is positive:
V<1/30 from (2), so it is greater than
9/8-16/135=1087/1080. Thus squaring preserves the inequality. Equation
(5) implies

\[
\begin{split}
 4Q&\ge(4-73U/1000+V)^2+
               (9/8+13U/50-32V/9)^2\\
 &=4Q+\frac{U}{1000}
       +(V-73U/1000)^2+(13U/50-32V/9)^2.
\end{split}
\tag{7}
\]

Here 16+81/64=1105/64=4Q. The linear V terms cancel exactly, and
the linear U coefficient is -584/1000+585/1000=1/1000.
All added terms are nonnegative. Therefore U=0 and then V=0.
Equation (5) now forces S<=1/8. This proves (6), and shows that
equality in (6) is possible only with U=V=0. In particular, any genuine
weak middle link has V>0 and spends a strictly positive part of the
endpoint-height budget.

Discarding the V term recovers exactly the endpoint budget used by
the actual-four-chain outsider-strip proof. Consequently all conclusions
in that proof which require only the outer endpoints and this budget
extend unchanged to the present outer-actual-link setting.

## 2. A stronger endpoint inset reserve

For either endpoint E, (6) gives

\[
 |y_E|\le\frac18-\frac{37}{50}(h_E-1/2)-\frac{32}{9}V.
\]

The function 1/(4h)+(37/50)(h-1/2) decreases on [1/2,8/15],
because its derivative is -1/(4h^2)+37/50<0 there. Evaluating at
8/15 gives

\[
 \boxed{\quad
 g_E-|y_E|\ge\frac{4421}{12000}+\frac{32}{9}V
               >\frac{221}{600}+\frac{32}{9}V.\quad}
\tag{8}
\]

The constant calculation is
15/32+37/1500-1/8=4421/12000. This retains the middle-link orientation
reserve instead of erasing it.

In particular, every additional physical square disjoint from these
endpoints has |x|<13/12, by Sections 3--5 of
`UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md`.
Those sections use only the endpoint bounds (2), h_E<8/15,
g_E-|y_E|>221/600, and physical disjointness from the relevant endpoint.
All have now been supplied without assuming an actual middle link.
This extension does not use the later side-capacity theorem's
additional fact that an internal main square lies in a specified
side column.

## 3. The two internal centers

The completed middle link always has
x_C-x_B>=g_B+g_C. The actual right outer link therefore gives

\[
 \begin{split}
 x_B&\le x_D-h_D-h_C-g_B-g_C\\
    &<\rho-\frac12-(h_C+g_C)-g_B
     =\frac1{60}-g_B-\eta_C.
 \end{split}
\]

Similarly the actual left link gives

\[
        x_C>g_C+\eta_B-\frac1{60}.
\tag{9}
\]

In particular B has negative center x-coordinate and C positive,
with |x_B|,|x_C|>1/(2sqrt(2))-1/60. The other immediate bounds are

\[
       x_B>-\rho+\frac12+h_B=h_B-\frac{61}{60},
       \qquad
       x_C<\rho-\frac12-h_C=\frac{61}{60}-h_C.
\tag{10}
\]

Equations (9)--(10) retain both internal frames and are valid whether
or not their common completed link is actual. They do not put B,C
in the older side-column bands |x|>=29/60. The next argument supplies
their marker consumption directly instead of assuming that fact.

## 4. Each internal square still consumes a side marker

The right internal square C contains one of the three closed markers

\[
             (3/5,-1),\qquad(3/5,0),\qquad(3/5,1).
\tag{11}
\]

First, (2) gives eta_C<=V<1/30. The function
eta(h)=h+1/(4h)-1 is increasing for h>=1/2, and

\[
                 \eta(13/20)=\frac9{260}>\frac1{30}.
\]

Therefore h_C<13/20. It follows that

\[
 k_C>\frac14,\qquad g_C>\frac5{13},\qquad
 k_C+g_C>\frac{33}{52}>\frac{37}{60}.
\tag{12}
\]

The k bound uses 1/2-(13/20)^2=31/400>1/16. The last comparison
in (12) has positive difference 7/390. Equation (10) gives
x_C<61/60-h_C<=31/60<3/5, while (9) gives

\[
       0<\frac35-x_C<\frac{37}{60}-g_C-\eta_B<k_C.
\tag{13}
\]

For any unit square with absolute physical side-axis components
a>=b>=0, a^2+b^2=1, one has h=(a+b)/2 and k=(a-b)/2. Every
vertical section at horizontal center offset |z|<=k has length
exactly 1/a>=1. Indeed for one chirality its two endpoints in that
central region have heights (bz-1/2)/a and (bz+1/2)/a relative to
the center; vertical reflection treats the other chirality. When
b=0 the assertion is simply the ordinary aligned square section.

By (13) this central-section formula applies to C at x=3/5. The
entire section lies in -2<y<2 because the closed Q-disk there has

\[
 y^2\le Q-\frac9{25}=\frac{25321}{6400}<4.
\tag{14}
\]

A closed interval of length at least one, lying strictly between
-2 and 2, contains at least one of -1,0,1: otherwise it lies in one
of the four open unit gaps cut out by those three integers and the
endpoints -2,2. This proves (11). Reflecting horizontally gives the
left internal square B one of the three markers (-3/5,-1),
(-3/5,0),(-3/5,1).

## 5. Unrestricted side capacity with a weak middle link

The physical marker theorem in Sections 1--5 of
`UNRESTRICTED_ACTUAL_FOUR_CHAIN_SIDE_CAPACITY_HAND_PROOF.md` only
needs an outer endpoint E with

\[
 89/60<x_E<91/60,\qquad h_E<8/15,\qquad
                    g_E-|y_E|>221/600.
\]

It then captures every physical unit disjoint from E with center
29/60<=x<=13/12 at one of the three right markers (11). Equations
(2) and (8) provide these exact endpoint hypotheses with E=D, so
the same marker theorem applies here. Its proof never uses the
middle projection comparison. The left statement is its reflection.

Now assume q<Q and three outsiders have x>=29/60. Expand all physical
centers by one common factor t>1, retaining orientations, until the
largest squared corner norm reaches Q. The previously proved global
normalization ensures that all expanded closed physical squares are
pairwise disjoint. The two actual outer links persist. The middle
completed link also persists: an actual middle gap only increases;
otherwise its maximal-coordinate comparison is unchanged by the
common center scaling. It may become actual, which causes no problem.

The endpoint and outsider-strip results above apply afresh. The three
outsider centers stay at least 29/60 and are less than 13/12, so the
endpoint marker theorem captures all three. Section 4 captures C at
one of the same three markers, without requiring its center to be
in the side band. Four pairwise disjoint closed squares cannot each
contain a point from a fixed three-point set. This contradiction proves

\[
 \boxed{\quad
 \#\{\text{outsiders with }x\ge29/60\}\le2,
 \qquad
 \#\{\text{outsiders with }x\le-29/60\}\le2.
 \quad}
\tag{15}
\]

Consequently the same nine (left,central,right) occupancy triples
printed in `UNRESTRICTED_MARKED_CHAIN_EDGE_LEDGER_HAND_PROOF.md`
cover all five outsiders of any outer-actual-link completed four-chain
strictly below Q. This extends the full strip and side-capacity
reduction to the middle-weak case. It does not turn any marker
membership into an actual y-projection comparison.

## 6. Scope

The unrestricted outsider strip |x|<13/12 now applies to every packing
with a completed four-chain whose two outer links are actual. The
refined endpoint budget (6) and inset reserve (8) quantify the extra
cost of a tilted middle pair. The two internal-center intervals are
explicit. Both side capacities, and hence the nine outsider-occupancy
rows, also extend by the separate central-section marker proof.
These are complete conditional geometric statements and can be used
in the remaining marked-chain analysis.

They do not make the middle pair physically x-separated. Apart from
the already closed (010,00) sharp terminal, the joint geometry of the
other physical squares remains to be proved. No additional whole-mask
closure, canonical root exclusion, or global equality is claimed.
