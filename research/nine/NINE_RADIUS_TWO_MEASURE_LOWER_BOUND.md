# Every packing of nine unit squares has containing radius strictly greater than two

Date: October 26, 2026.

**Status: complete geometric theorem with an independently reviewed
analytic proof of all remaining fixed values.** The complete continuous
domain assembly is NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md.
Its five mass targets and derivative target now follow directly from
NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md, with full root and
separate independent acceptance in
ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md.

The new proof uses one signed Taylor lemma, thirteen displayed rational
angle comparisons, and explicit radical and rational inequalities.
No high-precision inverse-angle checker or stored charge margin is a
current dependency. The earlier rectangle Taylor comparisons and other
analytic arithmetic remain. Both the five-charge checkers and the
original 208-charge checkers are preserved as historical alternatives.
No adaptive subdivision or empty-domain test is required.

This remains one uniform proof for arbitrary square orientations,
with its finite arithmetic displayed. It does not use a force graph,
equilibrium, any chosen contact type, a smaller packing theorem or
numerical root isolation. No Lean compilation, CI or workflow dispatch
is used.

**Theorem.** Nine closed unit squares with pairwise disjoint open
interiors cannot all be contained in the closed disk of radius two.
Consequently every nine-square packing has containing radius R>2.

All nine actual squares are retained. Circle masks, individual weights,
contact normals, forces and application means are irrelevant to this
geometric theorem and are never changed. The theorem does not by itself
prove the desired stronger R^2>=1105/256 or classify its equality cases.

## 1. One measure, with total mass strictly less than nine

Let lambda_r be normalized uniform angular measure on the circle of
radius r about the original containing-disk center, and let delta_0
be the unit point mass at that center. Define the nonnegative measure

\[
 \mu=\frac1{1000}\left(
 292\delta_0+714\lambda_{1/10}+3858\lambda_1
       +2424\lambda_{11/10}+1709\lambda_{27/20}\right).
\tag{1}
\]

All four circles lie in the radius-two disk, and

\[
                         \mu(\mathbb R^2)=8997/1000<9.
\tag{2}
\]

We prove the following full orientation-independent statement:

\[
 \boxed{\mu(\operatorname{int} S)\ge1
       \quad\hbox{for every unit square }S\subseteq D_2.}
\tag{3}
\]

For nine interior-disjoint squares, their nine open interiors are
disjoint measurable sets. Additivity of this one nonnegative measure
then makes their total mass at least nine, contradicting (2).
This also handles a square with the origin on its boundary: it receives
no origin atom in (3). No boundary point is counted in two interiors.

The existing `ADDITIVE_MEASURE_OBSTRUCTION.md` concerns the larger
disk of squared radius 17/4. It does not obstruct (1)--(3) on D_2.
This source makes no independent-measure claim for that larger disk.

## 2. Complete own-frame normalization

Rotations and reflections about the disk center preserve (1). Choose
the actual square's own axes and reflect and interchange their labels
so that its center coordinates satisfy x>=y>=0. Put a=x+1/2 and
b=y+1/2. Its exact square in these coordinates is

\[
 S(a,b)=[a-1,a]\times[b-1,b],\qquad
 \frac12\le b\le a,\qquad a^2+b^2\le4.
\tag{4}
\]

The farthest vertex is (a,b), so the last condition is exactly disk
containment. In particular a<=2 and b<=sqrt(2)<3/2. This normalization
does not assume that any vertex is on the containing circle or that
the actual center is on an own axis. It covers every physical unit.

## 3. Analytic reductions before the finite certificate

### 3.1 All a<=9/10 are immediate

If a<=9/10, then also b<=9/10. The circle of radius 1/10 lies in
S(a,b), with at most finitely many tangent boundary points excluded
from its open interior. The origin lies strictly inside. Thus

\[
 \mu(\operatorname{int}S)\ge(292+714)/1000=1006/1000>1.
\tag{5}
\]

### 3.2 A whole two-dimensional inner region reduces to b=1/2

Suppose 9/10<=a<=11/10 and 1/2<=b<=9/10. We claim

\[
                 \mu(\operatorname{int}S(a,b))
                    \ge\mu(\operatorname{int}S(a,1/2)).
\tag{6}
\]

The origin contribution is the same in both squares, including a=1.
The vertical interval [b-1,b] contains [-1/10,1/10], so the small-circle
contribution is likewise independent of b.

For each of the three larger radii r>=1 and every |y|<=9/10, a circle
point has |x|>=sqrt(1-81/100)>1/10. Since |a-1|<=1/10, the negative
x branch is outside the square and the positive branch automatically
satisfies x>a-1. Its unnormalized angular density as a function of y is

\[
 f_{r,a}(y)=\frac{1}{\sqrt{r^2-y^2}}\,
       {\bf1}_{\{\sqrt{r^2-y^2}<a\}}.
\tag{7}
\]

Endpoint conventions affect only finitely many circle points. The
density (7) is even and nondecreasing as |y| increases on this interval:
the indicator can change only from zero to one, and the positive factor
increases. Passing from [-1/2,1/2] to [b-1,b] removes a segment whose
absolute coordinates are at most 1/2 and adds an equally long segment
whose coordinates are at least 1/2. Its angular measure cannot decrease.
This proves (6) for all three circles at once. The certificate therefore
needs only the one-dimensional a interval [9/10,11/10], with b=1/2.
It is split at a=1 to retain the origin-atom endpoint explicitly.

### 3.3 A whole middle strip has a direct two-circle lower bound

For the slightly larger domain

\[
             11/10\le a\le3/2,\qquad 1/2\le b\le1,
\tag{8}
\]
the two circles of radii 1 and 11/10 alone suffice. Write A=a-1,
so 1/10<=A<=1/2. At either radius r, the upper x bound is inactive
because a>=r. The lower bound is x>=A>0. Put
t=sqrt(r^2-A^2)>1/2. The exact unnormalized angular length is

\[
 g_r(b)=\arcsin\frac{\min(b,t)}r-\arcsin\frac{b-1}r.
\tag{9}
\]

For 1/2<=b<=t it is nondecreasing, since b>=|b-1|. For b>=t it
is decreasing. Thus its minimum over [1/2,1] is at an endpoint.
At b=1/2 its value is 2asin(1/(2r)). At b=1, if t>=1, convexity
of asin on [0,1] gives asin(1/r)>=2asin(1/(2r)). If t<=1, its
value is acos(A/r)>=acos(1/(2r))>=2asin(1/(2r)); the last comparison
uses asin(1/(2r))<=pi/6. Therefore

\[
 \mu(\operatorname{int}S)\ge
       \frac{3858}{6000}
        +\frac{2424}{1000}\frac{\arcsin(5/11)}\pi>1.
\tag{10}
\]

Here is an explicit rational reserve. The alternating sine bound gives

\[
 \sin(47/100)\le47/100-(47/100)^3/6+(47/100)^5/120<5/11,
\]

with last difference 21887804923/13200000000000. Hence asin(5/11)>47/100.
Using pi<22/7, the right side of (10) exceeds

\[
 \frac{3858}{6000}
 +\frac{2424}{1000}\frac{47}{100}\frac7{22}
                     =1+\frac{189}{34375}.
\tag{11}
\]

The exact checker independently verifies both rational identities and
its own pi upper enclosure is below 22/7. No rectangular subdivision
is used for this entire strip.

### 3.4 Every outer square reduces to a single disk-boundary curve

If a>=27/20, increase the comparison parameter a to

\[
                       a_* = \sqrt{4-b^2}.
\tag{12}
\]

For every circle in (1), x<=a is already inactive because its radius
is at most 27/20. Increasing a only strengthens x>=a-1. Thus none
of its four angular measures increases. The origin lies outside both
squares. Consequently

\[
              \mu(\operatorname{int}S(a,b))
                    \ge\mu(\operatorname{int}S(a_*,b)).
\tag{13}
\]

This is a comparison of values of one measure, not a displacement of
any original packing square. The comparison endpoint has
1/2<=b<=sqrt(2) and a_*>=sqrt(2)>27/20. Only this one-dimensional
curve remains to be verified for the entire outer domain.

### 3.5 Exhaustive remaining domains

The preceding reductions leave exactly the following five geometric
domains. Their overlaps cause no problem. Section3.6 gives their current
analytic reductions; Section6 preserves the original larger finite cover.

| Name | a interval or formula | b interval | Reason |
| --- | --- | --- | --- |
| line, first part | [9/10,1] | b=1/2 | (6), including the origin-atom boundary |
| line, second part | [1,11/10] | b=1/2 | (6) |
| corner | [9/10,11/10] | [9/10,11/10] | The part of the inner range with b>=9/10 |
| middle | [11/10,27/20] | [1,27/20] | The part beyond the strip (8) |
| outer | a=sqrt(4-b^2) | [1/2,3/2], with b<=sqrt(2) | (13) |

In the two rectangular rows, b<=a and a^2+b^2<=4 remain necessary.
For a between 11/10 and 27/20, b<=1 is already covered by (8).
For a<=9/10 use (5), and for a>=27/20 use (13). This proves
exhaustiveness directly from (4); no sampled pose supplies a cover.

### 3.6 Complete analytic reductions and the current fixed-value proof

NINE_RADIUS_TWO_MEASURE_LINE_ANALYTIC_REDUCTION.md locates the
minimum on each side of a=1 by an exact derivative sign. Two fixed
common rectangles cover the left critical enclosure and the exact
right critical point. The actual a=1 square is always atom-free.
This replaces all95 former line charges by two.

NINE_RADIUS_TWO_MEASURE_RECTANGLES_ANALYTIC_REDUCTION.md proves
the complete corner and middle domains directly. Four corner cases
retain every origin boundary and use actual open-rectangle inclusions
or an even-density comparison; two middle cases use the original
order b<=a. Fourteen displayed signed Taylor reserves and six final
rational mass reserves eliminate all16 rectangle charges and all
three former corner empty tests.

NINE_RADIUS_TWO_MEASURE_OUTER_CURVE_ANALYTIC_REDUCTION.md proves
the complete outer-curve branch cover. Uniform convexity of the capped
circle functions and a single tangent bound reduce its entire middle
interval to b=13/12. Its initial and final ranges reduce to b=1/2
and a=b=sqrt(2). These are three fixed charges, each exceeding201/200,
and one fixed derivative enclosure. The complete outer charge exceeds
3013/3000. This replaces97 charges and three empty tests.

The full exact normalized-domain assembly and historical five coordinate
enclosures are in NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md.
The subsequent NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md proves
the two actual scalar minima, all three actual outer values and the
derivative target directly. Its proof covers the complete closed domains
and the actual atom-free endpoints. The five-point checkers, the
comparison and inverse-angle theory in Sections4--5, and the old
Section6 adaptive forest remain valid historical alternatives. Their
stored margins and execution are not current proof dependencies.

## 4. Exact lower charge on an entire parameter rectangle

For a parameter rectangle a in [a_l,a_h], b in [b_l,b_h], every
actual open square contains the common open rectangle

\[
                  (a_h-1,a_l)\times(b_h-1,b_l).
\tag{14}
\]

Therefore its mass is a lower bound simultaneously for every unit
in that parameter rectangle. If a_h<1 and b_h<1, (14) contains the
origin and receives the atom; otherwise the checker adds no atom.
The weak a=1 or b=1 boundaries are never credited with that atom.

For a nonnegative quadrant portion [x_l,x_h] by [y_l,y_h], the exact
circle angles are bounded by

\[
 \theta_{\rm low}=\max\{\arccos(x_h/r),\arcsin(y_l/r)\},\qquad
 \theta_{\rm high}=\min\{\arccos(x_l/r),\arcsin(y_h/r)\},
\tag{15}
\]

with each argument clipped to [0,1]. A missing or degenerate quadrant
contributes zero. Otherwise its angular length is the positive part
of theta_high-theta_low. Reflect (14) into all four quadrants and
sum these lengths. The finitely many axis or boundary points have
zero uniform angular measure. This proves the exact formula used by
`rect_arc_lower`; independent square orientations have already been
covered by (4).

For an outer interval b in [b_l,b_h], integer square-root bounds enclose
(12) by

\[
 \frac{\lfloor\sqrt{4B^2-b_h^2B^2}\rfloor}{B}
       \le a_*\le
 \frac{\lfloor\sqrt{4B^2-b_l^2B^2}\rfloor+1}{B},
\tag{16}
\]

where all stored b coordinates are integer multiples of 1/B.
Equivalently the code uses the integer coordinate numerators directly
in the radicands. Even an interval straddling sqrt(2) is enclosed
outward. An outer interval is discarded only if b_l^2>2.

## 5. The arithmetic verifier uses only exact integer enclosures

The coordinate denominator and angular scale are

\[
                      B=5\,2^{24}=83886080,\qquad Q=2^{56}.
\tag{17}
\]

Every angle interval is represented by integer lower and upper
numerators over Q. Multiplication, division and square roots round
outward using integer floor, ceiling and `isqrt`. No machine
floating-point value enters the checker, even for its pi enclosure.

For 0<=x<=1/2 the verifier uses the first sixteen alternating terms
of atan(x). The last included term is negative, so this partial sum
is a lower bound and adding the next positive term x^33/33 gives
an upper bound. The exact identity

\[
 \arctan x=\sum_{k=0}^{15}\frac{(-1)^k x^{2k+1}}{2k+1}
      +\int_0^x\frac{t^{32}}{1+t^2}\,dt
\tag{18}
\]

justifies both bounds directly. All powers and terms are themselves
enclosed outward in the integer arithmetic.

Machin's identity

\[
               \pi=16\arctan(1/5)-4\arctan(1/239)
\tag{19}
\]

gives the initial pi interval without circular dependence. One elementary
verification is tan(2atan(1/5))=5/12, tan(4atan(1/5))=120/119, and
tan(4atan(1/5)-atan(1/239))=1. The difference lies in (0,pi/2), so
equals pi/4. The integer verifier obtains

\[
 \frac{226375608064909912}{Q}<\pi
       <\frac{226375608064910268}{Q}.
\tag{20}
\]

Weak bounds suffice throughout. To evaluate atan(x) for 1/2<x<=1,
use pi/4-atan((1-x)/(1+x)); its new argument is between zero and
1/3 and (18) applies. Finally

\[
 \arcsin t=2\arctan\frac{t}{1+\sqrt{1-t^2}},\qquad
 \arccos t=\pi/2-\arcsin t
\tag{21}
\]

provide bounds on the entire clipped domain 0<=t<=1. The code treats
t=0 and t=1 explicitly and rounds the square root and both divisions
outward. Monotonicity of atan and asin preserves these enclosures.

In (15), take a lower bound for theta_high and an upper bound for
theta_low. Their positive-part difference is a valid lower arc
numerator L_r/Q. If I is the exact Boolean that (14) contains the
origin, an entire box is accepted only when the integer inequality

\[
 714L_{1/10}+3858L_1+2424L_{11/10}+1709L_{27/20}
                         \ge(1000-292I)\,2P_+
\tag{22}
\]

holds, where P_+ is the upper pi numerator in (20). Dividing by
1000 times 2piQ proves (3) for the entire box. This is a rigorous
interval inequality, not evaluation at a representative square.

## 6. Historical 208-charge alternative and its complete audit

This section preserves the original accepted proof by
NINE_RADIUS_TWO_MEASURE_CERTIFICATE.py and its independent evaluator.
The current five-charge proof is in Section3.6 and its cited assembly;
the following forest is not an additional current obligation.

The original deterministic checker starts with the five domains of
Section3.5, using the enclosing outer interval[1/2,3/2] and its
explicit b<=sqrt(2) test. For a rectangle it discards a box only if b_l>a_h or
a_l^2+b_l^2>4; these strict tests cannot discard a valid point or
its equality boundary. For the outer curve it uses only b_l^2>2.
Every other box is either accepted by (22) or split into two closed
children covering the parent. A rectangle splits its longer side
(the a side at a tie); the outer curve splits only its b interval.
Every midpoint is an exact integer coordinate. A nonprogressing
split would raise an error, and no such split occurs.

Running the saved checker gives:

| Residual domain | Charged whole boxes or intervals | Empty leaves | Binary splits |
| --- | ---: | ---: | ---: |
| line, both parts | 95 | 0 | 93 |
| corner | 14 | 3 | 16 |
| middle | 2 | 0 | 1 |
| outer boundary curve | 97 | 3 | 99 |
| Total | 208 | 6 | 209 |

The maximum split depth is 12. The smallest accepted integer
margin in (22) is 4023192202688832, strictly positive. The leaf
count satisfies 208+6=209+5, consistent with the five initial
roots. Coverage follows from the actual recursive partition, not
from this count alone. The deterministic ordered leaf digest is

    d86a26a628643d32387e0ba9800dcfc1830335f7828d0335bcd9c2172767b0c5

The digest is a reproducibility check, not a substitute for the
arithmetic and coverage proof. The entire verifier is self-contained
and requires only the Python standard library. It generates and
checks the finite cover directly; no external numerical grid or
unverified certificate file is read.

This supplies (3) on the two remaining rectangles and two remaining
one-dimensional domains. Sections 3.1--3.4 cover everything else.
Together with Sections 1--2, it proves the stated uniform R>2 theorem.
Both independent full-source reviews passed. One reviewer also checked
every inverse-trigonometric input with fresh exact rational arithmetic;
the other saved NINE_RADIUS_TWO_MEASURE_INDEPENDENT_CHECK.py, a
standalone alternative exact evaluator for this same finite witness.

## 7. Intended joins and limits

The theorem uses no n=8 lower-bound input and can supply R>2 directly
for the original nine-square problem. It is compatible with any
original selected force graph and every physical circle mask.

In particular, the accepted
`TRIANGLE_MIXED_ONE_SHARE_COMMON_POINT_BOUND.md` proves R<2 for
every actual core in the sole remaining all-unique outgoing-share0
C6 orbit. The present theorem contradicts that inequality while retaining
all three extras, simultaneously eliminating every remaining completion
allocation. The complete original-gate join is independently accepted in
SIX_CYCLE_ALL_UNIQUE_SIDE_COMPLETE_EXCLUSION.md and
REVIEW_C6_ALL_UNIQUE_SIDE_COMPLETE_EXCLUSION_2026_10_26.md.

The current uniform proof replaces all five remaining mass-checker
dependencies and the derivative-checker dependency by displayed
analytic rational/Taylor comparisons. Its earlier complete continuous
reductions already removed all adaptive splits and empty tests.
Finite Taylor, radical and rational arithmetic remains, with unchanged
physical scope; no claim of an arithmetic-free theorem is made.
The four earlier coefficient packets remain replaced by analytic
proofs with zero coefficient-sign checks; this source does not claim
that the repository has become certificate-free. The global lower
bound R^2>=1105/256, its original equality packings, the older full
prerequisite audit and Lean integration remain separate obligations.
