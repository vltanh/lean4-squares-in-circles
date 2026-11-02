# An unrestricted rotating-frame extraction of completed four-plus-three chains

November 2, 2026. Complete hand proof of the stated extraction. No mathematical
scripts, numerical enumeration, Lean, Lake, or CI are used.

Let nine pairwise interior-disjoint physical unit squares lie in the closed
disk of squared radius

\[
 Q=\frac{1105}{256}.
\]

**Theorem.** There is an orthonormal coordinate frame in which seven of the
squares form two disjoint completed coordinate chains of sizes four and
three, in one coordinate direction. The completion retains every actual
projection comparison and assigns any remaining pair to a coordinate of
maximal absolute center gap. Every nonconsecutive pair within either
extracted chain has an actual physical projection comparison.

The conclusion is unconditional. It does not assert that all consecutive
comparisons are physical, or bound their number of exceptions. The two
squares outside the displayed chains remain part of the nine-square
packing.

## 1. A closed choice of the completed orders

For frame angle \(\theta\), write the center coordinates of square \(S\) as
\((x_S(\theta),y_S(\theta))\), and let \(h_S(\theta)\) be its common
coordinate projection halfwidth. For distinct squares \(S\ne T\), define

\[
 \begin{split}
 S<_{P_x(\theta)}T\quad\Longleftrightarrow\quad&
 x_T-x_S\ge h_S+h_T\\
 &\text{or}\quad x_T-x_S\ge|y_T-y_S|,
 \end{split}
 \tag{1}
\]

and define \(P_y(\theta)\) by interchanging \(x,y\).

There are no self-comparisons. Distinct physical squares have distinct
centers, so the second alternative in (1) also has a
strictly positive horizontal gap. The first alternative is the actual
physical projection comparison. The second is the maximal-coordinate
comparison. At a tie between the absolute coordinate gaps, **both** maximal
comparisons are retained, with their respective coordinate directions.

This is the selective completion of
`UNRESTRICTED_FIVE_PROXY_CHAIN_HAND_PROOF.md`, with both choices retained
at ties. To check the equivalence away from ties, if the second alternative
holds and the pair already has an actual \(y\)-comparison, then

\[
 x_T-x_S\ge|y_T-y_S|\ge h_S+h_T,
\]

so it already has the actual \(x\)-comparison as well. Thus every
nonactual \(x\)-edge in (1) is genuinely uncovered by the original
coordinate orders and has a maximal horizontal center gap.

Each comparison belongs to the corresponding full order of the inscribed
aligned squares of halfwidth \(g_S=1/(4h_S)\). For an actual comparison,
this follows from \(h_S\ge g_S\). For a maximal-coordinate comparison,
the two inscribed aligned squares are interior-disjoint, so their larger
coordinate gap is at least \(g_S+g_T\).

Consequently the two-step estimate

\[
 x_U-x_S\ge g_S+2g_T+g_U\ge\sqrt2\ge h_S+h_U
 \tag{2}
\]

applies to every \(P_x\)-path \(S<T<U\), and likewise in \(y\).
Its extremes are already an actual comparison. Hence \(P_x,P_y\) are
strict partial orders, transitive without adding any further edges.
Every pair is covered by at least one order because one of its absolute
coordinate gaps is maximal.

Both heights are at most four. The proof in Sections 2--5 of
`UNRESTRICTED_FIVE_PROXY_CHAIN_HAND_PROOF.md` applies unchanged when both
tie choices are retained. A proposed five-chain has no actual consecutive
edge, since one actual gap would make its center span exceed \(91/30\).
Its first pair therefore satisfies the same maximal-gap inequality
\(|\Delta y|\le\Delta x\). The proved five-chain localization then gives
simultaneously

\[
 |c_B-c_A|<\frac{13\sqrt2}{16}<\frac{23}{20}
 \quad\text{and}\quad
 |c_B-c_A|>\frac{144}{125}>\frac{23}{20},
\]

the same contradiction. That argument does not require a strict inequality
between the coordinate gaps or a unique tie choice.

## 2. Some rotating frame has completed height four

Suppose, for a contradiction, that both completed heights are at most three
for every angle \(\theta\in[0,\pi]\). For each square \(S\), let

\[
 i_S(\theta)=\text{length of a longest }P_x(\theta)\text{-chain ending at }S,
\]

and define \(j_S(\theta)\) analogously for \(P_y\).

At each angle, the nine pairs \((i_S,j_S)\) are distinct: a comparison in
either order strictly increases that coordinate's ending rank, and every
pair is covered. All pairs lie in \(\{1,2,3\}^2\), so they occupy that
entire grid. In particular

\[
 \sum_S i_S(\theta)=18,\qquad \sum_S j_S(\theta)=18
 \quad\text{for every }\theta.
 \tag{3}
\]

For each fixed ordered pair \((S,T)\), the set of angles at which
\(S<_{P_x(\theta)}T\) holds is closed. Indeed the center coordinates,
projection halfwidths, and absolute coordinate gaps are continuous, and
(1) is a finite union of closed inequalities. The same is true for
\(P_y\). Retaining both choices at a tie is essential here.

Fix any \(\theta_0\). Each comparison absent at \(\theta_0\) remains
absent on a neighborhood of that angle. There are only finitely many
ordered pairs and two orders, so one common neighborhood has

\[
 P_x(\theta)\subseteq P_x(\theta_0),\qquad
 P_y(\theta)\subseteq P_y(\theta_0).
 \tag{4}
\]

Thus every square's nearby ranks satisfy

\[
 i_S(\theta)\le i_S(\theta_0),\qquad
 j_S(\theta)\le j_S(\theta_0).
\]

The two fixed sums (3) force equality for each square individually.
Therefore every rank label is locally constant. On the connected interval
\([0,\pi]\), each square's rank label is consequently constant.

Choose the square whose label at angle zero is \((1,1)\). It has no
predecessor in either initial order. A half-turn negates both coordinate
differences and preserves the projection halfwidths, so

\[
 P_x(\pi)=P_x(0)^{\mathrm{op}},\qquad
 P_y(\pi)=P_y(0)^{\mathrm{op}}.
\]

Its unchanged label \((1,1)\) at angle \(\pi\) therefore says it also
has no successor in either initial order. This contradicts pair coverage
with any of the other eight squares.

Equivalently, the full rank grid's fixed rows and columns give starting
ranks \(4-i_S,4-j_S\), so a half-turn sends every label to
\((4-i_S,4-j_S)\), which cannot leave all nine labels unchanged.

The contradiction proves that some frame has a completed chain of length
at least four. The uniform height bound in Section 1 makes its height
exactly four.

## 3. Extracting the two disjoint completed chains

At this frame, an antichain of either order is a chain of the other: every
pair in the antichain must be compared by the other order. Both widths are
therefore at most four.

Apply the nine-element chain/antichain extraction lemma recalled in Section
6 of `UNRESTRICTED_FIVE_PROXY_CHAIN_HAND_PROOF.md` to an order of height
four. It produces either disjoint completed chains of sizes four and three
in that order, or disjoint antichains of those sizes. In the latter case
they are completed chains in the other order. This is the stated
completed four-plus-three extraction.

Finally, every pair with at least one intervening square in a completed
chain has an actual projection comparison, by (2) and transitivity.
Only the consecutive comparisons can be added edges. An added edge still
comes with its full physical-pair hypotheses and the maximal-coordinate
inequality; it is not promoted to physical projection separation.

## 4. What the extraction does and does not finish

The earlier fixed-frame dichotomy had a full completed three-by-three rank
grid as one alternative. Rotating the frame removes that alternative as a
mandatory global case: some frame always supplies completed four-plus-three
chains.

The remaining geometric obligation is to use the actual nine-square
packing to close those chains when consecutive comparisons are added.
Neither this proof nor Greene's theorem replaces the two omitted squares,
removes any added edge, or supplies an actual four-plus-three terminal.

