# Monotone outer-radius expansion and the sharp-capture interface

This is an elementary statement about the adjacent-pair boundary relaxation.
It uses no sampled pair-gap function or numerical certificate. It supplies
an independent way to transfer a capture at one rational circle ceiling
back to a hypothetical packing below the exact optimum.

## 1. Boundary states and radius derivative

Keep every center ray and every absolute square frame fixed. A core-boundary
center stays fixed. An outer-boundary square with relative frame angle
\(\alpha\in[-\pi/4,\pi/4]\) has center radius \(r=r(q,\alpha)\) determined by

\[
r^2+B r+\frac12=q,\qquad
B=\cos\alpha+|\sin\alpha|\in[1,\sqrt2].
\]

For \(5/2\le q\le4\),

\[
\frac45<r<\frac32,\qquad
\frac14\le\partial_q r
=\frac1{\sqrt{B^2+4q-2}}\le\frac13.
\tag{1}
\]

For the lower radius bound, at \(r=4/5\) the left side of the defining
equation is less than \(16/25+6/5+1/2=117/50<5/2\), using
\(B\le\sqrt2<3/2\). At \(r=3/2\) it is at least
\(9/4+3/2+1/2=17/4>4\). The defining quadratic is strictly increasing in
\(r\ge0\). The derivative denominator has square between 9 and 16,
which proves its bounds.

A core-boundary center has radius at most
\(\sqrt2/2+1/12<4/5\), as established in the no-adjacent-core lemma.

## 2. Every active separator is strengthened

Choose a signed SAT axis for a pair. Its unit direction stays fixed under
the radius change, because both square frames stay fixed. Write its signed
center projection as \(P\). The required sum of square half-widths is a
constant \(w\ge1\). We prove that whenever \(P\ge w\), increasing \(q\)
increases \(P\), unless both centers are core states and stay fixed.

For an outer--outer pair,

\[
P=u r_A+v r_B,\qquad -1\le u,v\le1.
\]

If both coefficients are nonnegative, \(P\ge1\) and \(r_A,r_B<3/2\)
give \(u+v>2/3\); hence \(P'\ge(u+v)/4>1/6\).
Both coefficients cannot be nonpositive. In the remaining case relabel
the two terms and write \(P=u r_A-s r_B\), with \(u,s\ge0\). Feasibility
and (1) give

\[
u>\frac23+\frac8{15}s,
\qquad
s<\frac58.
\]

The second inequality follows from \(s r_B\le u r_A-1<1/2\) and
\(r_B>4/5\). Therefore

\[
P'\ge\frac u4-\frac s3
>\frac16-\frac s5>\frac1{24}.
\tag{2}
\]

For a core--outer pair, write \(P=u r_O+v r_C\). Since
\(r_C<4/5\), the condition \(P\ge1\) implies
\(u r_O>1/5\), and thus \(u>2/15\). Consequently

\[
P'=u r'_O>\frac1{30}.
\tag{3}
\]

The axis width remains constant. Equations (2)--(3) and continuity show that
an initially valid selected separator never ceases to be valid. Indeed a
first return to its initial gap would contradict the strictly positive
derivative throughout the intervening region. This argument can be applied
to every selected edge simultaneously. Center rays, cyclic angular gaps,
their total \(2\pi\), and every absolute frame are unchanged.

**Monotonicity theorem.** Any adjacent-pair boundary cycle at radius-squared
\(q_1\in[5/2,4]\) expands to a boundary cycle of the same C/O word at any
\(q_2\in[q_1,4]\), by changing only outer radii. Every selected true SAT
separator remains valid. Every moved center travels at most
\((q_2-q_1)/3\).

The final travel bound follows directly by integrating (1). Core--core
edges, if any, are unchanged. No nonneighbor-disjointness claim is needed.

## 3. A fixed rational capture ceiling suffices for exact sharpness

Let the exact sharp root satisfy its already certified isolating interval

\[
|q_*-q_c|\le10^{-16},\qquad
q_c=3.91553413751747532652.
\]

Define two exact rationals

\[
q_-=q_c-2\cdot10^{-16},\qquad
Q_{\rm sharp}=q_c+10^{-16}.
\]

Then \(q_-<q_*\le Q_{\rm sharp}\) and
\(Q_{\rm sharp}-q_-=3\cdot10^{-16}\). Suppose hypothetically that an
eight-square packing lies in a disk with radius-squared \(q<q_*\). Set

\[
\bar q=\max(q,q_-).
\]

The same packing is contained in the \(\bar q\) disk, and
\(q_-\le\bar q<q_*\). Apply the proved radial-boundary reduction at this
radius \(\bar q\), preserving adjacent true SAT and total center angle.
Then expand outer centers to \(Q_{\rm sharp}\) by the monotonicity theorem.

A **complete** global capture at \(Q_{\rm sharp}\) now applies to that
expanded cycle. If its terminal pose has center error at most
\(\varepsilon-10^{-16}\) in a local sharpness theorem admitting error
\(\varepsilon\), shrink its outer radii back to \(\bar q\). Every center
changes by at most \(10^{-16}\); its absolute frames and all center-angle
gaps stay identical. The original \(\bar q\)-boundary cycle therefore
lies in the local theorem's tube. That theorem yields
\(\bar q\ge q_*\), contradicting \(\bar q<q_*\).

This argument needs neither a new rounded lower-bound gate nor a replay of
all nonterminal pair certificates with variable \(q\). It needs a small
explicit reserve in the terminal center tolerance; for a \(10^{-3}\) local
tube a target error of \(0.00099\) leaves far more reserve than required.
All frame-mismatch and common-tilt conditions are unchanged by the expansion
and shrink. The discrete labeling and chosen slider components must still
be included in the capture statement.

**Status.** The monotonicity and transfer argument are proved here. The
complete global capture into the local tube remains the separate gate that
the current role/anchor cover is intended to establish.
