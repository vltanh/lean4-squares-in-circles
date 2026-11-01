# One exceptional pair: the height-four reduction and its two remaining end patterns

November 1, 2026. Hand proof continuation. No scripts, Lean, or CI.

The reductions and local lemmas below are complete. They do **not** close
the full nine-square one-exception theorem. In particular, the two unused
squares remain part of the final mathematical obligation. The exact
eight-square example in `END_EXCEPTION_EIGHT_SQUARE_OBSTRUCTION.md`
shows why a terminal using only the displayed seven squares, or only
those seven and an arbitrary eighth, would be false.

## 1. Hypotheses and the previously proved terminal

There are nine physical unit squares with pairwise disjoint open
interiors in a disk of squared radius

\[
 q\le Q:=\frac{1105}{256}.
\]

Fix an orthonormal frame. Every pair except a genuine exceptional pair
\(A,B\) is separated by its x-projections or its y-projections. The
exceptional pair has overlapping open projections on both axes. Write
\(c_S=(x_S,y_S)\), let \(h_S\in[1/2,1/\sqrt2]\) be either coordinate
projection halfwidth of square \(S\), and put

\[
 g_S=\frac1{4h_S}.
\]

An **actual** comparison \(S<_xT\) means
\(x_T-x_S\ge h_S+h_T\), and similarly for y. Contact is permitted.
These are strict partial orders on the distinct squares, despite allowing
contact in the displayed geometric inequality.

We use the complete physical endpoint terminal already proved in
`PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`.
Four distinct endpoint squares satisfying

\[
 x_V-x_U\ge2+h_U+h_V,\qquad
 x_Z-x_W\ge1+h_W+h_Z \tag{1}
\]

force \(q\ge Q\). If one inequality in (1) is strict, they exclude the
whole domain \(q\le Q\). Consequently disjoint actual chains of lengths
four and three provide a sharp terminal. When discussing a remaining
case below, we may assume that no such actual four-plus-three terminal
has already occurred in either coordinate direction.

The pair-span lemma in
`ONE_EXCEPTION_PAIR_SPAN_AND_SHARP_TERMINAL_2026_11_01.md` gives

\[
 \max(|x_B-x_A|,|y_B-y_A|)\ge g_A+g_B,
\]
\[
 g_A+h_A+g_B+h_B
 =2+\frac{(2h_A-1)^2}{4h_A}
    +\frac{(2h_B-1)^2}{4h_B}. \tag{2}
\]

Choose an axis realizing the first inequality, call it x, and reflect x
if necessary so that

\[
 d:=x_B-x_A\ge g_A+g_B.
\]

Set

\[
 \delta:=d+h_A+h_B-2>0. \tag{3}
\]

Strictness follows from (2): equality would force both squares aligned
and \(d=1\), contrary to a genuine coordinate exception.

## 2. Adding just one comparison completes the coordinate cover

Let \(P\) be the actual x-order. Add only the relation \(A<B\), and
call the resulting relation \(P^+\). It is already transitive.

Indeed, if \(S<_xA\), then

\[
 x_B-x_S\ge d+h_A+h_S
 \ge(g_A+h_A)+g_B+h_S
 \ge1+g_B+h_S>h_B+h_S.
\]

Thus \(S<_xB\) was already actual. Similarly \(B<_xT\) implies
\(A<_xT\) was already actual. These are all transitivity checks involving
the added comparison. All its comparisons increase the x-coordinate,
so no cycle is introduced. In particular, **every comparison of
\(P^+\) other than \(A<B\) is an actual x-comparison**.

Together, \(P^+\) and the unchanged actual y-order cover every pair.
Their heights are at most four. Here is a geometric verification of the
only new point. Use auxiliary x-halfwidth \(g_S\) on \(A,B\) and
\(h_S\) on every other square. Each comparison of \(P^+\) separates
these auxiliary intervals. A five-chain would have endpoint center gap
at least

\[
 4-4\left(\frac12-\frac1{2\sqrt2}\right)
 =2+\sqrt2.
\]

This lower bound puts both potentially shortened halfwidths internally;
putting one at an endpoint only increases the lower bound. It contradicts
the center-radius bound proved in Section 5 below, since
\(2+\sqrt2>2(91/60)\). An actual y-five-chain has endpoint center
gap at least four and is likewise impossible.

The auxiliary x-intervals can be combined with the unchanged y-intervals
as bookkeeping rectangles. These mixed \(g\)-by-\(h\) rectangles are
**not** claimed to be contained in the physical rotated squares. The
inscribed \(g\)-by-\(g\) squares justify (2); actual comparisons and
their monotonicity justify the auxiliary order.

An antichain in either of the two completed orders is a chain in the
other, so both completed widths are at most four as well.

## 3. The global augmented-order dichotomy

If both completed heights are at most three, the entire configuration
is excluded by the four-corner argument in Sections 1--3 of
`ONE_EXCEPTION_RANK_BOUNDARY_CONTINUATION.md`. That proof covers every
position of the exceptional pair in the full three-by-three augmented
rank grid, including an exceptional adjacent pair on an outer row. Its
weak-corner bound is

\[
 q\ge\frac{825+200\sqrt2}{256}>Q.
\]

It remains to consider an order of height four and width at most four.
We use the nine-element consequence of Greene's partition theorem
proved and sourced in `TWO_DIRECTION_SEPARABLE_NINE_HAND_PROOF_2026_11_01.md`:
such an order has either two disjoint chains of lengths four and three,
or two disjoint antichains of lengths four and three. An antichain in
one completed order is a chain in the other. Therefore we obtain two
disjoint completed chains of lengths four and three in one direction.

If that direction is y, both chains are actual and (1) applies. If it
is x and the exceptional squares do not occur together in one chain,
both chains are again actual. If they occur together, they are
consecutive: an intervening square would give actual comparisons from
\(A\) through that square to \(B\), contradicting the genuine exception.

If \(A,B\) occupy the two internal positions of the four-chain, its
outside comparisons are actual. Formula (3) then gives

\[
 x_V-x_U\ge h_U+h_A+d+h_B+h_V
 =2+h_U+h_V+\delta.
\]

The other chain supplies the short span in (1), so this case is strictly
excluded even at \(q=Q\).

All remaining assignments consequently have one of the following forms,
up to reflecting x and relabeling the exceptional pair:

| Pattern | Chain containing the exception | Disjoint actual chain |
|---|---|---|
| I | \(A<B<_xC<_xD\) | \(L<_xM<_xR\) |
| II | \(A<B<_xC\) | \(M_0<_xM_1<_xM_2<_xM_3\) |

Here the unmarked comparison \(A<B\) is the sole added comparison;
every other comparison, including \(A<_xC\) and \(A<_xD\) where
applicable, is actual. Each row displays seven distinct squares. The
other two squares are still present and satisfy every original physical
and coordinate-cover hypothesis.

This reduction includes the branch in which both original widths are
at most four and some original height is four. It also includes the
remaining end-pair branch from
`ONE_EXCEPTION_RANK_BOUNDARY_CONTINUATION.md`. It makes no assertion
that the resulting seven-square pattern alone is impossible.

## 4. Exact span deficits and useful closed subcases

For Pattern I, summing its three center gaps gives

\[
 \begin{aligned}
 x_D-x_A
 &\ge d+h_B+2h_C+h_D\\
 &=2+h_A+h_D+\delta+2(h_C-h_A).
 \end{aligned} \tag{4}
\]

Thus this pattern is already covered by (1) whenever

\[
 \delta+2(h_C-h_A)\ge0. \tag{5}
\]

If (5) is strict the closed \(Q\)-disk is excluded. In particular,
\(h_C\ge h_A\) suffices, and then strictness follows from \(\delta>0\).
An unresolved Pattern I must therefore satisfy

\[
 h_A>h_C,\qquad 0<\delta<2(h_A-h_C). \tag{6}
\]

For Pattern II,

\[
 x_C-x_A\ge d+h_B+h_C
 =1+h_A+h_C+\delta-(2h_A-1). \tag{7}
\]

The actual four-chain supplies the long span in (1), so Pattern II is
already covered whenever

\[
 \delta\ge2h_A-1. \tag{8}
\]

An unresolved Pattern II has

\[
 h_A>\frac12,\qquad 0<\delta<2h_A-1. \tag{9}
\]

Neither (5) nor (8) may be assumed without proof. These formulas exhibit
the exact missing span, rather than replacing an exceptional comparison
by an actual projection separation.

## 5. Center bounds and localization of actual four-chain endpoints

For a physical unit square with center \(c\), choose its own orthonormal
side axes \(u,v\). Its largest vertex norm satisfies

\[
 q\ge |c|^2+\frac12+|c\cdot u|+|c\cdot v|
 \ge |c|^2+|c|+\frac12.
\]

Put

\[
 \rho:=\frac{91}{60}.
\]

Since

\[
 \rho^2+\rho+\frac12=\frac{15541}{3600}
 >\frac{1105}{256},
\]

every center has \(|c|<\rho\). This strengthens the convenient
\(61/40\) bound used in the earlier notes.

**Actual four-chain endpoint lemma.** If
\(S_0<_xS_1<_xS_2<_xS_3\), then

\[
 h_{S_0},h_{S_3}<\frac8{15},\qquad
 x_{S_0}<-h_{S_0}-\frac{59}{60},\qquad
 x_{S_3}>h_{S_3}+\frac{59}{60}, \tag{10}
\]
\[
 |y_{S_0}|<\frac15,
 \qquad |y_{S_3}|<\frac15. \tag{11}
\]

*Proof.* The endpoint gap is at least
\(h_{S_0}+h_{S_3}+2h_{S_1}+2h_{S_2}\), hence at least
\(h_{S_0}+5/2\), and also at least \(h_{S_3}+5/2\).
The center bound immediately gives (10), including the halfwidth bound.

For any square put

\[
 k=\sqrt{\frac12-h^2}.
\]

If its absolute side-axis components are \(a\ge b\ge0\), then
\(h=(a+b)/2\) and \(k=(a-b)/2\). Its vertices have coordinate
offsets given, up to reflections, by \((h,k),(-k,h),(-h,-k),(k,-h)\).
In each closed coordinate quadrant there is therefore a vertex whose
two coordinate offsets in that quadrant are both at least \(k\).
Choose the quadrant pointing away from the origin from the center.
Disk containment implies

\[
 q\ge (|x|+k)^2+(|y|+k)^2. \tag{12}
\]

For \(1/2\le h\le8/15\),

\[
 k>\frac{23}{50},\qquad h+k>\frac{99}{100}.
\]

The first follows by squaring at the largest h. For the second, the
function \(h+\sqrt{1/2-h^2}\) is concave, so its minimum is at an
endpoint of this interval; both endpoint values exceed \(99/100\).
If an endpoint square had \(|y|\ge1/5\), (10)--(12) would give

\[
 q>\left(\frac{59}{60}+\frac{99}{100}\right)^2
       +\left(\frac15+\frac{23}{50}\right)^2
 =\left(\frac{148}{75}\right)^2
       +\left(\frac{33}{50}\right)^2
 =\frac{97417}{22500}>Q,
\]

a contradiction. This proves (11). The argument is invariant under
reflections and interchange of x and y. QED.

## 6. Pattern I forces the left endpoint of the short chain to overlap both exceptional squares

Assume Pattern I has not already supplied an actual terminal. Its true
comparisons include \(A<_xC<_xD\), \(B<_xC<_xD\), and
\(L<_xM<_xR\).

If \(A<_xL\), the actual chains \((A,L,M,R)\) and \((B,C,D)\)
are disjoint and have lengths four and three. If \(B<_xL\), use
\((B,L,M,R)\) and \((A,C,D)\). Both cases are terminal.
The comparison \(L<_xA\) would give the augmented five-chain
\(L,A,B,C,D\), which Section 2 excludes.

It remains to rule out \(L<_xB\). Suppose it held. Then
\(L,B,C,D\) is an actual four-chain, so \(|y_L|<1/5\) by (11).
On the other hand, (3) and the actual comparisons after B give

\[
 x_D-x_A\ge\frac72-h_A+\delta,
 \qquad
 x_A<h_A-\frac{119}{60}<-\frac54. \tag{13}
\]

The final inequality uses \(h_A\le1/\sqrt2<11/15\).
The inscribed halfwidths give the further useful bound

\[
 x_D-x_A\ge(g_A+g_B)+h_B+2h_C+h_D
 \ge g_A+\frac52,
 \qquad
 x_A<-\frac{59}{60}-g_A. \tag{13a}
\]

Here \(g_B+h_B\ge1\), \(2h_C\ge1\), and \(h_D\ge1/2\)
give the second inequality. In particular the exceptional endpoint is
strictly left of \(-59/60-1/(2\sqrt2)\).
The actual four-chain also puts \(x_L<-89/60<-5/4\). Both x-centers
therefore lie in \((-\rho,-5/4)\), and their x-gap is less than
\(\rho-5/4=4/15<1\). Their x-projections overlap. Since the pair
\(A,L\) is not exceptional, it must be y-separated. Consequently

\[
 |y_A|>h_A+\frac3{10}. \tag{14}
\]

If \(h_A\ge3/5\), (13)--(14) imply

\[
 |c_A|^2>\left(\frac54\right)^2+
                \left(\frac9{10}\right)^2
 =\frac{949}{400}>\rho^2.
\]

If \(h_A\le3/5\), they imply

\[
 |c_A|^2>\left(\frac{83}{60}\right)^2+
                \left(\frac45\right)^2
 =\frac{9193}{3600}>\rho^2.
\]

Both contradict the center bound. Thus \(L<_xB\) is impossible.

We have proved that **L is actually x-incomparable with both A and B**.
Therefore L is y-separated from both. Since the exceptional y-intervals
overlap, L cannot lie between them: it lies wholly above both or wholly
below both in y. Reflect y if necessary to normalize

\[
 y_L+h_L\le\min(y_A-h_A,y_B-h_B). \tag{15}
\]

There is also a useful common bound on right endpoints:

\[
 x_A+h_A<\frac1{60},\qquad
 x_B+h_B<\frac1{60},\qquad
 x_L+h_L<\frac1{60}. \tag{16}
\]

The last two follow from the actual three-chains \(B,C,D\) and
\(L,M,R\). For the first, note that
\(d\ge g_A+g_B\ge1/\sqrt2>|h_A-h_B|\), so
\(x_A+h_A<x_B+h_B\).

These facts are exact localizations, not a seven-square contradiction.
The eight-square obstruction cited at the start satisfies this same-side
overlap geometry.

## 7. Pattern II has a common-overlap witness in the actual four-chain

Assume Pattern II has not already reached an actual or internal-pair
terminal. No \(M_i<_xA\) can hold: otherwise
\(M_i,A,B,C\) is an augmented four-chain with the exceptional pair
internal, and the other three M-squares form a disjoint actual
three-chain. Section 3 would exclude it.

Also neither \(A<_xM_0\) nor \(B<_xM_0\) can hold, since either
would extend the actual four-chain to an actual five-chain.
It follows in particular that A and \(M_0\) are x-incomparable, so

\[
 |y_A|>h_A+\frac3{10}. \tag{17}
\]

We now prove that at least one square

\[
 T\in\{M_0,M_1,M_2\}
\]

is actually x-incomparable with both A and B.

If \(M_0\) is x-incomparable with B, take \(T=M_0\). Otherwise the
only possible comparison is \(M_0<_xB\).

Suppose first \(M_1<_xB\). The comparison \(B<_xM_2\) would give
the actual five-chain \(M_0,M_1,B,M_2,M_3\); the comparison
\(M_2<_xB\) would give \(M_0,M_1,M_2,B,C\). Hence \(M_2\)
is x-incomparable with B. If \(A<_xM_2\), the disjoint actual chains
\((M_0,M_1,B,C)\) and \((A,M_2,M_3)\) give a terminal. The opposite
comparison \(M_2<_xA\) was already excluded. Thus \(T=M_2\) works.

Suppose instead \(M_1\not<_xB\). The opposite comparison
\(B<_xM_1\) would give the actual five-chain
\(M_0,B,M_1,M_2,M_3\), so \(M_1\) is x-incomparable with B.
If \(A<_xM_1\), the disjoint actual chains \((A,M_1,M_2,M_3)\)
and \((M_0,B,C)\) give a terminal. The comparison \(M_1<_xA\)
was already excluded. Therefore \(T=M_1\) works.

In every case T is y-separated from both A and B, and the overlapping
exceptional y-intervals again force T wholly above both or wholly below
both. This conclusion uses actual comparisons and enumerates all cases;
it does not assume a common geometric grid.

There is a further routing. If \(C<_xM_3\), the chains
\(A,B,C,M_3\) and \(M_0,M_1,M_2\) are a Pattern I instance.
The opposite comparison \(M_3<_xC\) would give an actual five-chain.
Thus a Pattern II instance that is not already routed to Pattern I has
C and \(M_3\) x-incomparable. By the endpoint lemma,

\[
 |y_C|>h_C+\frac3{10}. \tag{18}
\]

Both exposed ends A and C are therefore vertically outside the narrow
endpoint strip of the actual four-chain. This is additional usable
geometry; it is not yet a contradiction.

## 8. Precise remaining obligation

After the proved grid and internal-pair terminals, a nine-square packing
in the one-exception class can remain only in Pattern I or Pattern II,
with the following further information:

- Pattern I satisfies (6), has the common-overlap short endpoint L,
  the same-side ordering (15), and the bounds (13) and (16).
- Pattern II satisfies (9), has the common-overlap witness T from
  Section 7, and either routes to Pattern I or satisfies both (17)
  and (18).
- In both patterns, the two squares omitted from the displayed chains
  are physical unit squares in the same disk. Each is x- or y-separated
  from every other square, including both exceptional squares. They
  are also x- or y-separated from each other.

The remaining proof must use these two additional squares, or an equally
strong consequence of the full nine-square hypotheses, to obtain a
valid sharp terminal. The exact eight-square configuration in
`END_EXCEPTION_EIGHT_SQUARE_OBSTRUCTION.md` prevents dropping these
capacity conditions. No whole one-exception theorem, unrestricted global
caller, canonical root exclusion, or new equality classification is
claimed by this continuation.
