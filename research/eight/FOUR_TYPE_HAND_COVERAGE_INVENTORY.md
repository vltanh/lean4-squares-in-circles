# Whole-domain coverage inventory for the four-type hand conversion

This file distinguishes complete pair entries, proved angle strips, and
remaining continuous domains. It is a scope ledger, not a proof of the
unproved entries. The computer-assisted PL certificate remains a separate,
completed artifact; none of its interval trees is silently treated as a
hand proof below.

## 1. One fixed proposed family

Put \(Q=9789/2500\), \(\beta=9/50\),
\(a_0=\sqrt{Q-1/4}-1/2\), and
\(c=\sqrt{Q/2}-1/2\). Use the following four geometric domains and
positive-half labels. Every decimal is an exact rational number.

| Type | Geometric domain, with \(t=b/a\ge0\) | Proposed \(\ell(a,b)\) |
|---|---|---|
| C, index 0 | whole core boundary, \(0\le t\le1\) | \(7.506931(7/12-a)+1.077372b\) |
| L, index 1 | outer boundary, \(0\le t\le1/4\) | \(.403875(a-a_0)+1.089065b\) |
| M, index 2 | outer boundary, \(1/4\le t\le3/7\) | \(-2.143075+1.489593a+1.580219b\) |
| H, index 3 | outer boundary, \(3/7\le t\le1\) | \(\pi/4-.569472(a-c)+.390886(b-c)\) |

For a signed state \(\alpha=\sigma\arctan(b/a)\), take the
lifted potential \(\psi=\alpha-\sigma\ell\). One representative
is chosen consistently for each physical vertex, including type-cut and
quarter-turn endpoints. `LIFTED_STATE_POTENTIAL_TELESCOPING.md` proves
that no equality of potential values on duplicate lifts is needed.

The cost is

\[
 C_{ij}=\delta-\beta h(\phi)+\psi_j-\psi_i
 =\phi-\beta h(\phi)+\sigma\ell_i-\tau\ell_j.
\]

The two source separators are

\[
 M_f=A\sin\phi-\tau B\cos\phi+\sigma b-W\ge0,
 \qquad
 M_e=a-A\cos\phi-\tau B\sin\phi-W\ge0,
\]

where \(W=1+h\). They are source axes 1 and 4. Reflected reversal
covers the two surviving target axes. The earlier cap and common-point
lemmas cover the discarded axes in the seven-state ring.

## 2. The actual finite whole-domain count

Before grouping any regimes there are exactly

\[
 4\cdot4\cdot2\cdot2\cdot2=128
\]

ordered source-axis branches: source type, target type, both signs, and
one of the two source axes. Relative-frame intervals must further be
split where a width formula, an arc support formula, or an explicitly
proved monotonicity changes. Counting a strip is not the same as
covering one of these whole branches.

An unordered diagonal type entry consists of eight such branches.
An unordered off-diagonal entry consists of sixteen. The present state is:

| Pair entry | Whole source-axis branches | Hand status |
|---|---:|---|
| C/C | 8 | **Complete**, all signs, axes and frame angles |
| C/L | 16 | **Complete**, independently reviewed |
| C/M | 16 | Complete restored manuscript and 213 fixed comparisons; fresh independent review pending |
| C/H | 16 | **Complete**, 143 fixed comparisons and independent polynomial/coverage review |
| L/L | 8 | **Complete**, independently reviewed |
| L/M | 16 | **Complete**, 305 fixed comparisons and independent reconstruction of all eight polynomial rows |
| L/H | 16 | **Complete**, 232 fixed comparisons and independent reconstruction of all 80 Bernstein bounds and 16 endpoint rows |
| M/M | 8 | **Complete**, 111 fixed comparisons and independent review of the whole contact deformation and both polynomial rows |
| M/H | 16 | **Complete at .8926**, 225 fixed comparisons and independent polynomial/coverage review |
| H/H | 8 | **Complete**, restored 108-comparison proof with fresh independent geometry, scalar and polynomial audit |

The reviewed complete entries now cover **112** of the 128 ordered
source-axis branches: C/C, C/L, C/H, L/L, L/M, L/H, M/M, M/H and H/H. The restored
C/M manuscript covers the final 16 branches and passes 213 fixed
comparisons; its fresh independent review is the final frame-table gate.

The [C/H audit](CORE_HIGH_INDEPENDENT_AUDIT.md) reconstructs its
degree-18 polynomial independently. The
[M/H audit](MID_HIGH_WHOLE_PAIR_INDEPENDENT_AUDIT.md) reconstructs all
five polynomials, including a direct conversion to degree 20 for the
elevated row. The prior low-entry audit remains
[LOW_FRAME_ENTRIES_INDEPENDENT_AUDIT.md](LOW_FRAME_ENTRIES_INDEPENDENT_AUDIT.md).

## 3. Exact scope of the proved strips

The interval endpoints in this table are included. Each target-axis
image under reflected reversal is also covered, but is not an extra
source-axis branch in the count above.

| Source, target | Signs | Source axis | Complete interval in this note | Proof file |
|---|---|---|---|---|
| C, C | all four choices | both | all admissible \(\phi\) | `CORE_CORE_WHOLE_PAIR_HAND_PROOF.md` |
| C, L and L, C | all four choices | both | all admissible \(\phi\) | `CORE_LOW_WHOLE_PAIR_HAND_PROOF.md` |
| L, L | all four choices | both | all admissible \(\phi\) | `LOW_LOW_WHOLE_PAIR_HAND_PROOF.md` |
| L, H | \((+,-)\) | \(+f\) | \([-1/50,1/50]\) | `LOW_HIGH_PARALLEL_STRIP_HAND_PROOF.md` |
| H, L | \((+,-)\) | \(+f\) | \([-1/50,1/50]\) | `LOW_HIGH_PARALLEL_STRIP_HAND_PROOF.md` |
| L, H | \((+,+)\) | \(+f\) | \([\pi/2-1/50,\pi/2+1/50]\) | `LOW_HIGH_QUARTER_STRIP_HAND_REDUCTION.md` |
| H, L | \((+,+)\) | \(+f\) | \([2/25,3/10]\) | `HIGH_LOW_NONALIGNED_SUPPORT_FORMULA.md` plus `HIGH_LOW_NONALIGNED_SHORT_HAND_PROOF.md` |
| M, C | \((-,-)\) | \(-e\) | \([1,29/25]\) | `CORE_MID_NONALIGNED_HAND_PROOF.md` |

`LOW_HIGH_ALIGNED_CONTACT_HAND_PROOF.md` proves the aligned endpoints
used inside the two strip deformations. Those endpoints are not counted
as additional branches or as an extension of the strips.

The longer `HIGH_LOW_NONALIGNED_HAND_CURVATURE.md` additionally proves
the stronger scalar value \(F>.8833599\) on its stated interval.
The aligned and deformation arguments retain values above .88335 as
well. None of those statements extends beyond the intervals in the table.

## 4. The proposed cost table and the frame-concentration interface

The earlier rounded target table was

\[
 \Gamma^{\rm old}=
 \begin{pmatrix}
 .92&.91&.9005&.8833\\
 .91&.91&.9005&.8833\\
 .9005&.9005&.8912&.8925\\
 .8833&.8833&.8925&.9099
 \end{pmatrix}.
\]

Its exact minimum length-seven closed-walk cost is
\(T=6.2094\). It suffices for the M5 width-floor contradiction, but
does **not** imply the present quarter table's required frame diameter
\(D<.7\). It gives only
\(U<(2\pi-6.2094)/.18\approx.409919\), whereas the concentration
lemma needs \(U<\sin(.7)+\cos(.7)-1\approx.40905987\).

The minimizing edge multisets consist of four C/H or L/H edges, two
M/H edges, and one M/M loop. An example type word is
\((C,H,C,H,M,M,H)\). Raising C/M alone therefore cannot repair
this budget.

Two alternative explicit repairs each give the exact budget
\(T=6.2096\):

1. Raise both C/H and L/H targets from .8833 to .88335.
2. Keep those targets and raise only M/H from .8925 to .8926.

The second version is the current proposed whole-domain target:

\[
 \boxed{\Gamma=
 \begin{pmatrix}
 .92&.91&.9005&.8833\\
 .91&.91&.9005&.8833\\
 .9005&.9005&.8912&.8926\\
 .8833&.8833&.8926&.9099
 \end{pmatrix}.}                                         \tag{1}
\]

Its C/C, C/L, C/H, L/L, L/M, L/H, M/M, M/H and H/H entries have complete independently
reviewed hand proofs. The M/H proof establishes the strengthened .8926
value required here. The
remaining obligations are recorded exactly in Section 2; the full matrix
is not yet claimed as a closed hand theorem.

## 5. The repaired finite graph budget has a short hand proof

Subtract \(a=.8833\) from every entry of (1). Every residual edge
cost is nonnegative. Each triangle has residual sum at least
\(p=.0265\); the four unordered triangle sums are

\[
 .0611,\quad .0267,\quad .0265,\quad .0265.
\]

Every loop other than M has residual cost at least \(p\).
The M loop has residual cost .0079, and every off-diagonal edge
incident to M has residual cost at least .0093. Thus a closed walk
containing that loop and any other vertex has residual cost at least

\[
 .0079+2(.0093)=.0265=p.
\]

The constant seven-step M walk has residual cost
\(7(.0079)>.0265\). Every other odd closed walk contains an odd
simple cycle. On four vertices this is a loop or triangle, already
covered. Nonnegative residual costs permit deleting the other edges.
Consequently every length-seven closed walk satisfies

\[
 \sum\Gamma_{i_j i_{j+1}}\ge7a+p
 =\frac{3881}{625}=6.2096.                                \tag{2}
\]

The example word above attains equality, so (2) is the exact minimum.
No exhaustive word enumeration is needed for this conclusion.

If all continuous pair inequalities for (1) are proved, telescoping
and \(\pi<355/113\) give

\[
 U<\frac{710/113-3881/625}{9/50}
 =\frac{10394}{25425}.                                   \tag{3}
\]

The lower sine/cosine Taylor polynomials through degrees 7 and 6 at
\(x=.7\) give

\[
 \sin(.7)+\cos(.7)-1>
 \frac{2945220061}{7200000000}>
 \frac{10394}{25425},
\]

with exact final difference

\[
 \frac{201866893}{813600000000}>0.
\]

Thus the repaired table would supply the precise \(D<.7\) interface.
The continuous pair entries in Section 2 remain the hand gate.

## 6. Other routes are logically separate

The common quarter-increment table uses two physical kinds, C/O, and
different markers. All three rows now have independent hand proofs, assembled in
`COMMON_QUARTER_TABLE_AND_FOUR_WORD_EXCLUSIONS.md`. Those proofs
are conditioned on \(D<.7\); they cannot themselves be substituted
for the missing frame-concentration premise without an additional
argument.

A discovery experiment with two angular graph types and only three
affine geometric labels (core, low outer, high outer) has not yet
reached the frame-concentration target. Its finite LP results are
discovery diagnostics only. They do not refute every possible two-type
marker or replace any continuous inequality above.
