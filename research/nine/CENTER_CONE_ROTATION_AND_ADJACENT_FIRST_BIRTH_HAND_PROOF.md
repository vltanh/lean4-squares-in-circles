# Pure center-cone chains and an adjacent diagonal first-birth normal form

November 2, 2026 UTC (November 1 in America/Chicago). Hand proof only.
No mathematical script, numerical search, Lean, Lake, or CI.

This is a strengthened choice of the auxiliary orders used in the
unrestricted rotating-frame reduction. It is not a geometric exclusion.
All nine physical squares and all their original pair constraints remain
in the problem throughout.

## 1. A smaller auxiliary order with more information on every edge

Let nine physical unit squares, with pairwise disjoint open interiors,
lie in the closed disk of squared radius Q=1105/256. In a rotating
orthonormal frame, define relations only by their center differences:

\[
 S\prec_x T\iff S\ne T\quad\hbox{and}\quad
                   x_T-x_S\ge|y_T-y_S|,
\]
\[
 S\prec_y T\iff S\ne T\quad\hbox{and}\quad
                   y_T-y_S\ge|x_T-x_S|.
\tag{1}
\]

Both choices are retained when the absolute coordinate gaps tie.
Physical separation makes distinct centers distinct. Therefore every
gap in the designated positive coordinate in (1) is strictly positive.

These relations are strict partial orders. Transitivity follows directly
from the triangle inequality; for example,

\[
 x_U-x_S=(x_U-x_T)+(x_T-x_S)
 \ge|y_U-y_T|+|y_T-y_S|\ge|y_U-y_S|.
\]

Every unordered physical pair is compared by at least one order,
with the sign of its larger coordinate gap determining the direction.
For every relation in either order, the inset argument gives the
corresponding coordinate gap at least g_S+g_T, where g_S=1/(4h_S).
Indeed otherwise both coordinate gaps would be smaller than this sum,
contradicting physical separation of the contained aligned squares.

Thus every two-step x-chain S\prec_x T\prec_x U has

\[
 x_U-x_S\ge g_S+2g_T+g_U\ge\sqrt2\ge h_S+h_U,
\tag{2}
\]

and its extremes are actually separated by physical x-projections.
The analogous statement holds in y. All nonconsecutive comparisons
inside the extracted chains will therefore still be actual.

Unlike the previous completion, (1) need not contain an actual
comparison when that comparison is in the smaller center-gap
coordinate. Such physical comparisons are not discarded from the
packing's hypotheses; they simply are not inserted into these auxiliary
orders. The useful strengthened conclusion is that **every** selected
edge, whether actual or weak, obeys the maximal-coordinate inequality.

For an alternative description put p=x+y and q=x-y. Then

\[
 S\prec_x T\iff p_T\ge p_S\ \hbox{and}\ q_T\ge q_S,
\]
\[
 S\prec_y T\iff p_T\ge p_S\ \hbox{and}\ q_T\le q_S,
\tag{3}
\]

with distinct centers. These are ordinary two-coordinate partial
orders, so no transitive-completion step is needed.

## 2. Both heights are at most four

The center-cone orders are subrelations of the closed completed orders
in `UNRESTRICTED_ROTATING_FRAME_EXTRACTION_HAND_PROOF.md`: they retain
exactly the second alternative in that source's definition. The proved
height bound for those larger orders immediately implies height at
most four for (1).

Equivalently, the geometric proof in
`UNRESTRICTED_FIVE_PROXY_CHAIN_HAND_PROOF.md` applies directly. A
hypothetical five-chain of inset projections has no actual consecutive
comparison, since one actual gap would give center span at least
1+3/sqrt(2)>91/30. Its first edge has the maximal-coordinate property
by (1), which is the only extra property used in that proof's final
contradiction. The proven opposite bounds on that pair's center
distance are incompatible. No new computational input is required.

## 3. Unconditional extraction in some frame

The rotating-rank proof also applies to these smaller orders. Here it
is stated explicitly to ensure that dropping some actual comparisons
has not lost the global extraction.

Suppose both heights were at most three at every angle in an interval
of length pi. Give each physical square its two ending ranks (i,j).
Every pair is covered, so all nine rank pairs are distinct and fill
{1,2,3} squared. The sum of each rank coordinate is consequently 18.

For each ordered physical pair, its comparison set in (1) is closed
in the rotation angle. At a fixed angle, all finitely many absent
comparisons therefore remain absent throughout a common neighborhood.
The nearby orders are subrelations of the order at the fixed angle.
Every nearby rank can only decrease. Since the two rank sums stay 18,
none decreases. Each physical square's two ranks are locally constant,
hence constant on the connected angle interval.

A half-turn reverses both orders. The square labeled (1,1) initially
would therefore have neither a predecessor nor a successor in either
initial order, contrary to pair coverage. Some frame has height four.
An antichain in one order is a chain in the other, so both widths are
at most four as well. The already cited nine-element Greene extraction
then supplies disjoint chains of lengths four and three in one of
the two orders. Equation (2) makes all their nonconsecutive comparisons
actual; every consecutive comparison has (1).

This proves an unconditional 4+3 extraction with all five consecutive
links in maximal center-gap coordinates, even when a selected link is
already physically actual. It does not make a weak link actual.

## 4. The first-birth premise and the retained full-nine array

Suppose a sequence of frames theta_n tends to theta_0, both cone-order
heights are at most three at theta_n, and the x-cone order has height
four at theta_0. Stabilize the full nine rank labels along a
subsequence, writing the physical squares S_ij, 1<=i,j<=3.

At every frame of that subsequence and at the limit,

\[
 S_{1j}\prec_x S_{2j}\prec_x S_{3j}\quad(j=1,2,3),
\]
\[
 S_{i1}\prec_y S_{i2}\prec_y S_{i3}\quad(i=1,2,3).
\tag{4}
\]

At the sequence frames these follow from equal ranks in the other
order and pair coverage. They persist at the limit by closedness.
The six comparisons between the extreme members of these rows and
columns are physical, by (2).

Any boundary x-comparison S_ij\prec_x S_kell has i<=k.
If i>k and j=ell it contradicts the retained reverse row order.
If i>k and the rows differ, prepend the first i members of row j and
append row ell from column k onward. The resulting distinct-square
chain has i+(4-k)>=5 members, impossible. Therefore a new four-chain
contains an x-comparison E=S_ij\prec_x F=S_iell of equal old i-rank.
It was absent at every theta_n, since an x-comparison there would
strictly increase the old i-rank.

Put d_x=x_F-x_E>0 and d_y=y_F-y_E at theta_0. The comparison's
absence at theta_n and presence at theta_0 give the exact equality

\[
                           d_x=|d_y|>0.
\tag{5}
\]

Thus every selected entering comparison is a diagonal center tie.
There is no separate entering case with d_x<|d_y| caused by adding
an actual comparison in a smaller coordinate.

## 5. The two old row labels must be adjacent, without a weakness premise

**Lemma.** The entering endpoints in Section 4 always satisfy
|j-ell|=1, even if their physical projections are actually separated.

Suppose instead they are the two outer rows. The retained old column
contains a middle square G and has either E\prec_y G\prec_y F or
F\prec_y G\prec_y E. First consider the former. Set

\[
 u=x_G-x_E,\quad v=x_F-x_G,\quad
 a=y_G-y_E>0,\quad b=y_F-y_G>0.
\]

The two cone comparisons give a>=|u| and b>=|v|. Equation (5),
together with d_x>0, gives u+v=a+b. Hence

\[
        a+b=u+v\le|u|+|v|\le a+b.
\]

Both inequalities are equalities, so u=a>0 and v=b>0. Thus
E\prec_x G\prec_x F as well. In the other case the same argument
with y negated gives the same x-chain E\prec_x G\prec_x F.

Now prepend the i-1 earlier members of E's old row and append the
3-i later members of F's old row. Those two rows and G's row are
distinct, so all five members are distinct. The x-chain has
(i-1)+3+(3-i)=5 members, contradicting the height bound. This proves
the lemma.

Consequently the entering edge always joins adjacent old rows and has
one of the following exact physical statuses:

\[
 \begin{array}{ll}
 d_x=|d_y|<h_E+h_F,&\text{genuinely weak in both coordinates};\\
 d_x=|d_y|\ge h_E+h_F,&\text{actual in both coordinates}.
 \end{array}
\tag{6}
\]

The second possibility is still retained. The new reduction does not
claim that every entering edge is weak or that any physical separator
must be diagonal. It only proves the diagonal **center** tie and the
adjacent old row labels in both physical cases.

## 6. Explicit 4+3 chains and the remaining two physical squares

The entering edge E=S_ij\prec_x F=S_iell gives the four-chain

\[
 S_{1j}\prec_x\cdots\prec_x S_{ij}=E
       \prec_x F=S_{i\ell}\prec_x\cdots\prec_x S_{3\ell}.
\tag{7}
\]

The third old row m supplies the disjoint three-chain
S_1m\prec_x S_2m\prec_x S_3m. The two omitted squares are exactly

\[
 \{S_{kj}:i<k\le3\}\ \cup\ \{S_{k\ell}:1\le k<i\}.
\tag{8}
\]

Their retained old row/column comparisons (4), all nine disk constraints,
and all original physical pairs remain hypotheses. No seven-square
rotation shortcut is invoked.

The unconditional alternatives remain: either some cone-order height
is four at every frame, or a first-birth frame with the complete
normal form above exists. The height-four set is closed, by finiteness
of the possible chains and closedness of each comparison. If it is
not the full rotation circle, a boundary approached from its open
complement gives the second alternative. Its nonemptiness follows
from Section 3.

Both alternatives still require a geometric exclusion or a valid
sharp-terminal caller. This result narrows the first-birth geometry
and strengthens the edge data in the unconditional extraction; it
does not close the persistent-height-four case or A.2, and it changes
no canonical root count.
