# Complete same-radius entry from the original normal quarter owners

## 1. Necessary-cycle theorem and the order of the proof

Put
\[
 q_L=19577/5000,\qquad Q_1=1957767069/500000000,
 \qquad Q=9789/2500,\qquad h=7/10.
\tag{1}
\]
The exact stationary hard-chain minimum satisfies
qL<q*<Q1<Q. Work at one actual ceiling
\[
                              q_L\le q\le q_*.
\tag{2}
\]
Use an actual boundary-neighbor seven-cycle in the domain of
[the uniform-radius pair theorem](HAND_G5_UNIFORM_RADIUS_PRIMARY_PAIR_TRANSPORT.md):
sorted contained squares avoiding the open true core, one-winding
order, quarter word 0101011, real-frame spread below h, both
captured error variations below h, and every square on its true
core or its actual outer q circle. H,A are nonnegative outer
states and B,D nonpositive outer states. E is normalized
nonpositive; G,T may have either signed tangent.

After the established global owner restrictions, the actual
retained witnesses belong to exactly these sets:
\[
 HG,AB,TD\in\{0,2\},\qquad GA,EH\in\{0,1\},
 \qquad BT,DE\in\{2,3\}.
\tag{3}
\]
Retain the original zero-owner implications
\[
                    HG2\Longrightarrow y_G<0,
       \qquad       TD0\Longrightarrow y_T>0.
\tag{4}
\]
These are hypotheses when the necessary cycle is stated apart
from an original boundary reduction. All witnesses are weak;
no contact equality or sign of an individual error is assumed.

**Complete primary-owner entry theorem.** Such a cycle has
q=q*. Its proof reaches the hard GA0/BT2 necessary class at
the same q. More precisely, either the proof obtains a strict
contradiction at q<=q*, or it reaches that hard class by moving
only G and T, leaving the five original anchors H,A,B,D,E,
their coordinates, frames, circle values and E's sign identical.
Every originally chosen weak witness that is retained in the
construction remains an actual separating inequality.

The equality pullback must still use the original-center
argument, rather than identifying a comparison G or T with
its ancestor. Section 8 records exactly the unchanged data
and strictness information that argument needs.

The order matters. First perform only the independent G/T
pair reductions. While H,A,B,D remain outer at the original q,
exclude every terminal with a positive primary. Only then apply
the aligned negative-primary transports, whose hypotheses permit
the ensuing anchor changes. No positive-primary boundary theorem
is invoked after an anchor has lost its outer-circle equality.

## 2. Exhaust the G-side primary pair at the original q

If actual GA0 is already available, select it and stop on this
side, regardless of any additional primary witness. A GA1 error
equal to zero is such an actual tie.

Suppose GA1 is retained and GA0 is unavailable. There are exactly
two HG owners.

For HG0, Section 6 of
[the uniform-radius pair theorem](HAND_G5_UNIFORM_RADIUS_PRIMARY_PAIR_TRANSPORT.md)
gives a G-only actual descendant with GA0 or HG aligned. It
covers both G signs and radial kinds, every signed HG0/GA1
total, and both individual error signs. Its positive-total
contact arcs use the original outer q circle. Its nonpositive
clauses use the actual same-q flat-core constructions. At HG
alignment the transverse inequality and bH<.9 force
\[
                              y_G<-.1.
\tag{5}
\]
The two HG owners then have the same actual projection, so HG2
may be selected. The remaining GA error is positive, negative,
or zero, and the zero case is again an actual GA0 tie.

For HG2, (4) gives G's normal negative sign. If the GA1 error
is positive, retain this actual configuration. If it is negative
and GA0 is unavailable, the same-q contact-vector argument
(26a) of the uniform-radius note forces G onto its true flat
core. The
[canceling negative-primary companion](HAND_G5_CORE_NEGATIVE_GA1_WITH_CANCELING_HG.md),
together with its
[noncanceling companion](HAND_G5_CORE_NEGATIVE_GA1_WITH_NONCANCELING_HG.md),
then changes G alone to actual GA0 or HG alignment. Those
local constructions retain the original q and stay inside the
original frame interval. Their boundary-neighbor gap check is
also supplied in Section 6 of the uniform-radius note.

Thus the complete G-side list is
\[
\begin{array}{c|c|l}
 \text{type}&\text{quarter owner}&\text{other retained data}\\ \hline
 G_0&GA0&HG0\text{ or }HG2,\text{ arbitrary HG error}\\
 G_+&GA1\text{ at }x>0&HG2,\text{ arbitrary HG error}\\
 G_-&GA1\text{ at }x<0&HG\text{ aligned},\ y_G<0.
\end{array}
\tag{6}
\]
In G- we continue only while GA0 is actually unavailable;
otherwise reselect it and use G0. Every operation fixed all
five anchors and the other intermediate T.

## 3. The reflected local argument exhausts the T side

Use the exact local reflection and role reversal of H,G,A
to D,T,B. It transforms the projection formulas, physical
gaps and actual circles, and uses no E state or E witness.
Consequently it is valid without changing E's sign.

If BT2 is already actual, select it. BT3 at zero error is
the same actual BT2 projection. For BT3/TD2, the full
same-q pair theorem gives BT2 or TD alignment for either
T sign, either radial kind and every signed total. At TD
alignment the transverse inequality and bD<.9 force
\[
                              y_T>.1,
\tag{7}
\]
so the actual TD0 tie may be selected. For BT3/TD0, a
positive BT error is retained; a genuine negative one has
the reflected flat-core entry and reflected canceling/
noncanceling reduction, giving BT2 or TD alignment.

The complete T-side list is therefore
\[
\begin{array}{c|c|l}
 \text{type}&\text{quarter owner}&\text{other retained data}\\ \hline
 T_0&BT2&TD0\text{ or }TD2,\text{ arbitrary TD error}\\
 T_+&BT3\text{ at }z>0&TD0,\text{ arbitrary TD error}\\
 T_-&BT3\text{ at }z<0&TD\text{ aligned},\ y_T>0.
\end{array}
\tag{8}
\]
In T- reselect any already actual BT2 immediately. G-only
and T-only constructions can be composed in either order:
their changed vertices and changed edge pairs are disjoint.
They fix the original H,A,B,D,E coordinates and frames,
their actual circles and E's normalized sign. Frame spread
does not increase, and each variation is retained or decreases.

The implications (4) also persist. A new aligned HG2 has
(5), and a new aligned TD0 has (7). An endpoint retaining
an unaligned original owner retains its required original
sign; the wrong-sign pair constructions retain the other
zero owner. Thus no zero-owner sign hypothesis is silently
lost before the hard-owner theorem is used.

## 4. Every positive-GA terminal is excluded with either E sign

We need the following sign-free statement on the unchanged
outer-anchor domain: actual HG2 and GA1 at x>0 are impossible
at q<=q* for each of the four T rows
\[
\begin{array}{c|c|l}
 BT&TD&\text{condition}\\ \hline
 2&0&\text{arbitrary errors}\\
 2&2&\text{arbitrary errors}\\
 3&0&d_{BT}>0,\ d_{TD}\text{ arbitrary}\\
 3&0&d_{BT}<0,\ d_{TD}=0.
\end{array}
\tag{9}
\]
E may have either signed tangent, either radial kind, every
original DE/EH owner, and arbitrary E errors. This sign scope
is needed for Section 5, not merely for the initial normalized
cycle. We spell out its finite proof.

For core E all four rows are precisely the strict
[either-sign core-E theorem](HAND_G5_COUPLED_CORE_E_SIGN_SYMMETRIC_POSITIVE_ENTRY.md).
For outer E, first use
[signed nonpositive-primary reselection](HAND_G5_POSITIVE_GA_OUTER_E_SIGNED_NONPOSITIVE_PRIMARY_RESELECTION.md)
on the unchanged actual q states. Every retained nonpositive
E primary may be replaced by its actual secondary. All remaining
E primaries are therefore positive.

Both E secondaries are excluded in all four T rows by
[the E-independent all-secondary theorem](HAND_G5_POSITIVE_GA_OUTER_E_SECONDARY_E_ALL_T_OWNERS.md).
For sole EH1, both E signs are covered by the
[signed BT2/TD0 theorem](HAND_G5_SOLE_E_POSITIVE_GA_SIGNED_COORDINATE_EXTENSIONS.md),
the
[positive-T theorem](HAND_G5_POSITIVE_GA1_SOLE_E_PRIMARY_POSITIVE_T_EXCLUSION.md),
and the
[negative-T theorem](HAND_G5_POSITIVE_GA_SOLE_E_NEGATIVE_T_EXCLUSION.md).
Here a TD2 error is split into its nonnegative and negative
cases, and the last row of (9) retains its actual TD alignment.
At a zero T-primary error its secondary is an actual tie.

For sole DE3 with E nonpositive, the same positive/negative T
theorems and the
[BT2/TD0 sole-DE theorem](HAND_G5_POSITIVE_GA_OUTER_E_SOLE_DE_AND_SECONDARY_EXCLUSION.md)
apply. For sole DE3 with E positive, normalize E at its fixed
frame on the original outer q circle by Section 2 of
[the sign-free BT2/TD0 entry theorem](HAND_G5_COUPLED_OUTER_E_SIGN_FREE_BT2_TD0_ENTRY.md).
DE3 improves while EH0 is retained; all non-E data and every
actual error are unchanged. Its exact alternatives are E=0,
already covered, or the actual arbitrary-angle EH0 contact
\[
             a_H\cos\rho+b_H\sin\rho+y_E=W(\rho),
                         \qquad y_E>0.
\tag{10}
\]
The sharp obstructions at (10) are respectively

* Sections 3--5 of the sign-free BT2/TD0 entry theorem;
* [the positive-T arbitrary-contact extension](HAND_G5_COUPLED_OUTER_E_POSITIVE_T_UNALIGNED_CONTACT.md);
* [the negative-T arbitrary-contact extension](HAND_G5_EXCEPTIONAL_E_NEGATIVE_T_ARBITRARY_EH_CONTACT_EXTENSION.md).

They retain the EH0 angle in H's actual two-angle block.
They exclude x>0 at q<=q*, using strict outside-strip bounds
and the exact sharp hard-chain defect on the critical strip.
No sign-restricted sole-DE theorem is applied to a positive E.

Finally, if both E primaries are positive, the
[same-radius paired-E theorem](HAND_G5_COUPLED_POSITIVE_E_PAIR_SAME_RADIUS_ENDPOINTS.md)
changes E alone to DE alignment or EH alignment. Select the
actual secondary at that tie. The possibly changed E sign is
covered by the sole-E alternatives just proved. All six other
states and witnesses, the actual q, and both variations are
retained. This exhausts every outer-E alternative and proves
(9) with either E sign.

In particular G+ with any of T0,T+,T- is impossible. All weak
zero-angle ties in this proof are selected on actual states;
the sole nonstrict sharp endpoint has x=0 and is not G+.

## 5. Every positive-BT terminal is excluded by a checked full reflection

Suppose T+ remains. Reflect the physical cycle and reverse
its roles as
\[
 (H',G',A',B',T',D',E')=(D,T,B,A,G,H,E),
 \qquad \theta'=-\theta,\qquad y'=-y.
\tag{11}
\]
The common circle, true core, radial kinds, sorting, cyclic
gaps, real spread and both variations are preserved. Every
reversed-edge error equals its original error. The quarter
owner correspondence is 0<->2, 1<->3; the zero owners
exchange 0 and 2.

Thus original BT3 at z>0 with TD0 becomes positive GA1 with
HG2. The other side becomes exactly one of (9):
\[
\begin{array}{c|c|c}
 \text{original G type}&\text{reflected BT/TD}&\text{row of (9)}\\ \hline
 G_0\text{ with HG2}&BT2,TD0&1\\
 G_0\text{ with HG0}&BT2,TD2&2\\
 G_+&BT3\text{ positive},TD0&3\\
 G_-&BT3\text{ negative},TD\text{ aligned}&4.
\end{array}
\tag{12}
\]
The reflected E has nonnegative tangent. Section 4 explicitly
permits this sign on its original core or outer q circle, so
there is no E-sign gap in this invocation. It excludes every
row of (12). No E-normalizing relabeling or hidden E transport
is part of the reflection.

Consequently every terminal with G+ or T+ is impossible at
q<=q*. Only the four nonpositive terminal combinations remain.

## 6. The four remaining terminals reach the hard class

The complete terminal matrix is

| G type | T type | Same-radius conclusion |
|---|---|---|
| G0 | T0 | The actual hard GA0/BT2 theorem applies. |
| G- | T0 | Aligned negative-GA entry; a genuine primary gives strict H-anchor circle loss. |
| G0 | T- | Complete aligned negative-BT entry; a genuine primary gives strict D-anchor circle loss. |
| G- | T- | The two-negative span gives first-side entry; complete negative-BT entry retains the strict H loss and adds a strict D loss. |

### 6.1 G0/T0

E is still its original core or outer q representative. Hence
\[
             a_E\le7/12\quad\text{or}\quad
             a_E\ge c_q\ge\max\{b_H,b_D\}.
\tag{13}
\]
The original signs, owners, (4), true-core exclusion and real
frame bound are all retained. The
[arbitrary-sign hard-owner theorem](HAND_G5_ARBITRARY_SIGNS_AND_FRAMES_HARD_OWNERS_SHARP_REDUCTION.md)
therefore applies directly to the current necessary cycle and
gives q>=q*. Together with (2), this gives q=q*.

### 6.2 G-/T0

The
[complete aligned negative-GA theorem](HAND_G5_GLOBAL_PRIMARY_ENTRY_ALIGNED_NEGATIVE_ENDPOINT_COMPLETE.md)
has precisely these actual owners, both AB choices, arbitrary
TD owner/error, arbitrary T sign with its original implication
(4), and every E placement and mixed owner. G is normal by
HG alignment. Its D radial eligibility holds because D is
still outer at q; E is still core or outer at that q.

If GA0 is available, select it. Otherwise the theorem reaches
the hard class with strict H-circle loss at the same q. The
hard equality theorem forces H onto the stationary q* circle,
so this genuine case has q>q*, contradicting (2). No strict
loss at the free intermediate G is substituted for this H loss.

### 6.3 G0/T-

Apply the
[complete one-negative-BT theorem](HAND_G5_GLOBAL_PRIMARY_ENTRY_ONE_NEGATIVE_BT_COMPLETE.md).
It permits arbitrary G sign and all original HG/AB/mixed
errors, retains (4), and needs exactly E's core/outer q status
and nonpositive sign. All these data survived preprocessing.
It preserves H,G,A,B and produces the hard class with a strict
D-circle loss whenever BT2 was unavailable. Thus the genuine
case again forces q>q*, contradicting (2).

### 6.4 G-/T-

Reselect an already available hard owner first, reducing to
one of the preceding rows. Otherwise both aligned negative
primaries are genuine. The
[original two-negative span theorem](HAND_G5_GLOBAL_PRIMARY_ENTRY_BOTH_NEGATIVE_ALIGNED_SPAN.md)
and its
[stronger .21 version](HAND_G5_GLOBAL_PRIMARY_ENTRY_BOTH_NEGATIVE_ALIGNED_SHORT_SPAN.md)
give H-D<.21 on the unchanged actual states. Neither uses E.

Section 5 of the complete aligned negative-GA theorem explains
its exact local scope before BT2 is available: the H/G conversion
and E-only outside preparations still work with BT3 retained
once this separate H-D span is supplied. D is outer at q and
TD is aligned, so any required D-primary lift is eligible.
This reaches GA0 with strict H-circle loss, keeps B,T and their
frames unchanged, retains the actual negative BT3 and aligned
TD, and keeps E nonpositive on its true core or original q
circle. HG has its required normal G sign.

Now the complete one-negative-BT theorem from Section 6.3
applies to this descendant. It does not require H to remain
outer, and it preserves H,G,A,B exactly. In particular it
retains the strict H loss while converting the still-genuine
negative BT3, with a strict D loss as well. The resulting hard
input contradicts q<=q*. Alternatively the already established
[direct second-primary theorem](HAND_G5_GLOBAL_PRIMARY_ENTRY_BOTH_NEGATIVE_DIRECT_SECOND_TRANSPORT.md)
performs this same final conversion under its inherited
near-H bounds. The newer complete theorem avoids needing those
extra bounds in the present assembly.

This covers all four remaining terminal combinations. Every
genuine negative terminal is excluded by an actual anchor loss;
the only surviving route is the pair-only G0/T0 route of 6.1.

## 7. Radius, weak ties and actual geometric eligibility

All G/T preprocessing keeps the five original anchors on their
original circles. Every outer intermediate constructed in that
stage is outer at the same q. The positive-E normalizations and
pair endpoints also use that q and preserve their explicit
physical gaps and variations. Auxiliary Q-circle arguments are
used only to exclude a diagonal; no enlarged outer state is
substituted into a same-q transport.

The negative-entry theorems are necessary-system theorems.
They retain each required actual neighboring witness, true-core
avoidance and the real-frame bound, and use the same circle
ceiling. Their changed E retains (13). Their continuous
boundary paths preserve winding when that stronger geometric
domain is required. No theorem asserts preservation of omitted
nonneighbor inequalities.

Zero errors are always treated as actual primary/secondary ties.
Zero signed pair totals belong to the nonpositive local pair
constructions. The positive terminal exclusions require a
strictly positive remaining primary; their sharp exceptional
zero is therefore never discarded. The finite matrix contains
no unstated generic-position exception.

For an original packing below qL, run its original fixed-witness
radial-boundary reduction at the working ceiling qL before
applying this theorem. The resulting actual outer anchors then
lie at qL, and the conclusion contradicts qL<q*. Merely changing
the ceiling label of pre-existing outer representatives would
not supply these hypotheses.

## 8. Precise data retained for the original equality pullback

At q=q*, every route using a positive terminal is impossible,
and every genuine aligned negative terminal is impossible by
an actual H or D loss. The surviving route to hard owners uses
only G/T preprocessing, so the five original anchors and all
their frames remain identical to those of the hard descendant.

The
[retained-contact rigidity theorem](HAND_G5_HARD_EQUALITY_RETAINED_CONTACT_RIGIDITY.md)
then supplies the exact obstructions needed to examine the
source of each pair construction: invariant positive pair
totals, a G=A endpoint, or a retained strict actual HG/TD slack.
The independent opposite-intermediate preprocessing preserves
such a slack. A later genuine anchor-changing branch has already
been excluded separately and cannot erase this equality test.

These facts permit the original-owner equality argument to
reapply the hard theorem to the original untouched states once
the original hard owners are shown actual. They do not identify
the new free intermediate coordinates with the old coordinates,
and do not use an intermediate circle loss as an anchor loss.
The final original-packing pullback and the full weak
five-parameter converse remain the original equality-family
argument, invoked after this complete necessary-cycle entry.
