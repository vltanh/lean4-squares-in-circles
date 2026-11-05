# Nine unit squares in a circle: proof draft

This is a partial paper proof. The complete
[physical-and-cap foundation](FOUNDATION.md) and
[exhaustive extraction](EXTRACTION.md) are now written as separate chapters.
The [five-square cap](FIVE_SQUARE_CAP.md) adds a complete terminal with
all of its formerly computational scalar steps replaced by hand proofs.
Sections 1–4 below give their target, an attaining packing and the resulting
proof interface. Section 5 identifies the missing global implication.
No unrestricted lower bound is claimed.

## 1. Physical statement

Put

\[
Q=\frac{1105}{256},\qquad r=\sqrt Q=\frac{\sqrt{1105}}{16}.
\]

A unit square is
\(S_i=c_i+[-1/2,1/2]u_i+[-1/2,1/2]v_i\), where \(u_i,v_i\) are
orthonormal. Each of the nine squares has its own frame. Their open interiors
are pairwise disjoint; boundary contacts are permitted. Translate the disk
center to zero, and let its radius be \(R\ge0\).

The desired theorem is \(R\ge r\). Four-corner containment is equivalent to
whole-square containment because both the square and the disk are convex.
No common orientation, row structure, contact graph or separator owner is
assumed.

For a vector \(e\), write the centered support halfwidth as

\[
h_i(e)=\frac{|e\cdot u_i|+|e\cdot v_i|}{2}.
\]

For unit \(e\), \(1/2\le h_i(e)\le1/\sqrt2\), and
\(h_i(-e)=h_i(e)\). These are properties of the same original squares;
using their supports does not replace them with aligned squares.

## 2. An exact attaining packing

Take axis-aligned squares at the following centers:

| Group | Horizontal centers | Height |
|---|---|---|
| Four squares | \(-3/2,-1/2,1/2,3/2\) | \(1/16\) |
| Three squares | \(-1,0,1\) | \(-15/16\) |
| Two squares | \(-1/2,1/2\) | \(17/16\) |

Within a group the horizontal gaps are at least one. Between distinct
groups the vertical gap is at least one. Thus all open interiors are disjoint.
For an aligned square centered at \((x,y)\), its largest squared corner
radius is \((|x|+1/2)^2+(|y|+1/2)^2\). The group maxima are respectively

\[
4+(9/16)^2=Q,\qquad (3/2)^2+(23/16)^2=Q,
\qquad 1+(25/16)^2=881/256<Q.
\]

This proves attainability. It does not assert that every equality packing
has this layout; the retained [nonrigid examples](sources/NONRIGID_WITNESS.md)
and [oblique extras](sources/NO_GLOBAL_ORTHOGONAL_FRAME.md) prevent that inference.

## 3. The weighted endpoint criterion

The [physical two-square cap theorem](FOUNDATION.md#b-the-physical-weighted-two-square-cap)
states that, when \(R\le r\), two interior-disjoint original squares
\(M,B\) satisfy, in every unit direction \(e\),

\[
46[-e\cdot c_M-h_M(e)]
+\frac{27}{2}[-e\cdot c_B-h_B(e)]\le\frac{211}{4}.
\tag{1}
\]

The inequality is strict if \(R<r\). Its proof reduces physical separating
axes to five scalar inequalities and a four-interval rational convexity
table. The triangle bounding-rectangle lemma and all scalar estimates are
part of that argument, not assumptions supplied by a checker.

**Endpoint lemma.** For four distinct original squares \(A,D,E,G\), define

\[
L=e\cdot(c_D-c_A)-h_A(e)-h_D(e),\qquad
S=e\cdot(c_G-c_E)-h_E(e)-h_G(e),
\]
\[
W=46L+\frac{27}{2}S.
\]

If \(R\le r\), then

\[
W\le\frac{211}{2},
\tag{2}
\]

strictly when \(R<r\). Consequently, finding any such four squares and
direction with \(W\ge211/2\) proves \(R\ge r\).

*Proof.* Apply (1) to \((A,E)\) in direction \(e\), and to \((D,G)\) in
direction \(-e\). Add and use \(h_i(-e)=h_i(e)\). The sum of the left
sides is exactly \(W\); the right side is \(211/2\). Both inequalities
are strict below \(r\). If \(R>r\), the desired conclusion is immediate.
At \(R=r\), equality in (2) forces equality in both pair caps, so their
stated four-anchor equality conditions apply. \(\square\)

This lemma requires no projection-chain hypothesis. Two disjoint actual
chains of lengths four and three are one useful sufficient condition: their two
interior main squares give \(L\ge2\), and the short chain's interior
square gives \(S\ge1\). Hence
\(W\ge2\cdot46+27/2=211/2\).

### 3.1. A five-square criterion with arbitrary central separating directions

A second proved terminal is [FIVE_SQUARE_CAP.md](FIVE_SQUARE_CAP.md).
In a frame with two original endpoints near \(x=\pm3/2\), suppose
their absolute center heights are at most \(1/8\), their halfwidths
are at most \(8/15\), and there are three further originals L,U,R
with

\[
 -\frac{13}{12}\le x_L\le0\le x_R\le\frac{13}{12},\qquad
 |x_U|\le\frac{29}{60},\qquad
 y_L,y_R\ge\frac35,\qquad y_U-h_U\ge\frac1{10}.
\]

The endpoint center bands are the explicit intervals
\([-91/60,-89/60]\) and \([89/60,91/60]\). Under these physical
hypotheses their inward span is at most two, strictly less when
\(R<r\). The theorem retains every possible central separating
direction and independent frame. Its full outer support estimates,
central transfer, strictness and five-square equality family are printed
in the two cap chapters.

For an actual four-chain, the original endpoint bounds and inward span
at least two are already available. Thus a triple satisfying the
displayed upper-square conditions, or their vertical reflection,
immediately excludes a strict counterexample. Section 4.2 of
[ACTUAL_FOUR_CHAIN.md](ACTUAL_FOUR_CHAIN.md) states the complete caller.

## 4. What completed chains actually supply

For seven distinct labels \(A,B,C,D;E,F,G\) in a chosen unit direction,
write \(x_i=e\cdot c_i\), \(h_i=h_i(e)\), and define the **signed**
projection surplus on a designated edge by

\[
s_{ij}=x_j-x_i-h_i-h_j.
\]

Telescoping gives the exact identity

\[
\begin{aligned}
W-\frac{211}{2}
={}&46\bigl(2h_B+2h_C-2+s_{AB}+s_{BC}+s_{CD}\bigr)\\
&+\frac{27}{2}\bigl(2h_F-1+s_{EF}+s_{FG}\bigr).
\end{aligned}
\tag{3}
\]

This needs no alignment or cone assumption. Positive surpluses must be
retained: they can compensate for negative ones. Showing the right side
nonnegative for a suitable witness is sufficient for the endpoint criterion.
No such general compensation theorem has yet been proved.

Under \(R\le r\), the complete [center-cone extraction](EXTRACTION.md)
supplies some frame and disjoint chains \(A,B,C,D;E,F,G\) for which
\(\Delta x\ge|\Delta y|\) on the five consecutive edges. Its height
bound, rotating-rank argument and finite-poset dependency must be read
together. It does **not** give \(s_{ij}\ge0\) on each edge.

The extraction chapter, Section 6, rotates these five comparisons to an endpoint
of their common admissible angle interval. At least one then satisfies
\(\Delta x=|\Delta y|>0\). This also covers persistent height four;
the stronger first-birth grid in the
[retained source](sources/CENTER_CONE_ROTATION_AND_ADJACENT_FIRST_BIRTH_HAND_PROOF.md)
has additional hypotheses.
The possible event frames depend on the unknown centers.

The other two originals \(H,I\), all 36 original nonoverlap conditions,
and all 36 corner bounds remain available. Their information is essential
to any proposed argument beyond the selected-seven relaxation.

For comparison with the retained examples, the historical mask \(abc/de\)
records the five edges \(AB,BC,CD;EF,FG\). Bit 0 means
\(x_j-x_i\ge h_i+h_j\); bit 1 means \(x_j-x_i<h_i+h_j\).
Thus projection equality belongs to bit 0, while cone equality is always
retained. A full-nine mask predicate includes all nine independent frames,
36 corner bounds, 36 physical pair conditions and the five cone comparisons.
The notation \(D_m^{<}\) uses corners strictly inside the \(Q\)-disk;
\(D_m^{\le}\) permits corner equality. The strict corner condition is
equivalent to fitting some radius below \(r\), since there are only finitely
many corners; the mask and witness conditions remain separate conjuncts.

Reversing both coordinate axes and simultaneously relabeling
\((A,B,C,D;E,F,G;H,I)\) as \((D,C,B,A;G,F,E;H,I)\) sends
\(abc/de\) to \(cba/ed\). These are domains of a packing **and a chosen
witness**. Different witnesses of the same packing may have different masks.

## 5. The missing implication

One sufficient research target is the following **unproved** statement:

> Every hypothetical nine-square packing with \(R<r\) admits a choice
> of four originals and a direction with \(W\ge211/2\); or three whole
> original squares lying in a half-plane
> \(\{z:e\cdot z\ge7/16\}\) for some unit \(e\); or five originals
> satisfying every hypothesis of Section 3.1, whose two endpoint squares
> have inward span at least two.

The first alternative contradicts (2). The second contradicts the
[sharp three-square half-plane cap](FOUNDATION.md#e-the-sharp-three-square-whole-half-plane-cap).
The third contradicts the strict five-square cap of Section 3.1.
This would prove the lower bound. It is a proposed route, not an established
classification or a premise of the proof.

The terminal direction and labels may differ from those of the first
extracted witness. A stronger closed-\(Q\) routing statement can be tested
against the retained exact equality examples, but is not required for the
strict lower bound. If these three terminals do not suffice, the missing class
must be stated explicitly before proposing another terminal.

The first unchanged all-nine domain is now specified in
[the actual-four-chain analysis](ACTUAL_FOUR_CHAIN.md). Its stronger
endpoint budget retains every chain gap and its pair-cap consequence
forces the other seven originals to meet one common central band. The
note states the entire surviving predicate; it does not prove that domain
empty. It now also excludes the upper and lower five-square callers of
Section 3.1; the complementary geometric configurations remain in the
domain. Section 4.3 of that analysis links the completed full-side and
one-sided occupancy theorems, their exact additional cone hypotheses,
and the new central-height exclusions. They do not exhaust the original
domain. The [proof plan](PROOF_PLAN.md) keeps this research decision and
the unrestricted closure open. Global equality classification remains a
separate obligation.
