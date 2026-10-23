# Every outer-error sign is sharp in the ordered normal-sign hard-owner class

## 1. Original-candidate theorem

Put
\[
 Q_0=9789/2500,\qquad Q_1=1957767069/500000000,
 \qquad q_L=19577/5000,\qquad K=13/12.
\tag{1}
\]
Retain the original normal signed tangents
\[
 (y_H,y_G,y_A,y_B,y_T,y_D,y_E)
 =(b_H,-b_G,b_A,-b_B,b_T,-b_D,-b_E),\qquad b_i\ge0,
\tag{2}
\]
the sorted own-frame corner bounds and the true core condition:
\[
 a_i\ge b_i\ge0,\qquad
 (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q_0.
\tag{3}
\]
Assume real frames of spread at most 7/10, ordered by
\[
 \theta_D\le\theta_A,\theta_B\le\theta_H,
 \qquad\theta_D\le\theta_E\le\theta_H.
\tag{4}
\]
The retained original SAT witnesses are
\[
\begin{array}{c|rrrrrrr}
 \text{edge}&HG&GA&AB&BT&TD&DE&EH\\ \hline
 \text{axis}&0\text{ or }2&0&0\text{ or }2&2&0\text{ or }2&3&1.
\end{array}
\tag{5}
\]
There is **no sign restriction** on either original outer
difference \(\theta_G-\theta_H\) or \(\theta_D-\theta_T\),
or on the AB difference.

**Sharp ordered-class theorem.** Every candidate (2)--(5) has
\(q\ge q_*\). At equality its three original zero differences
vanish:
\[
 \theta_G=\theta_H,\qquad\theta_A=\theta_B,
 \qquad\theta_T=\theta_D.
\tag{6}
\]
Its original five anchors are the unique stationary anchors
at tilt t_*, with the canonical hard and E splits. For an
original packing, the unchanged remaining constraints give
the full weak five-parameter equality family and its converse.

This theorem includes the two mixed-sign possibilities as well
as the previously proved nonnegative and nonpositive classes.
The normal signs, frame order, true core and original owners
in (2)--(5) remain explicit entry hypotheses. No global capture
into those hypotheses is claimed here.

The stationary enclosure gives
\(q_L<q_*<Q_1<Q_0\). A q above Q_1 already proves the strict
lower bound. A q below q_L may first be enlarged to q_L without
moving its centers. It therefore suffices to work at
\[
                              q_L\le q\le Q_1.
\tag{7}
\]
All circle constructions use this working q. In an equality
argument q=q_*, so there is no enlargement.

## 2. Align AB before choosing an outer-error reduction

Apply `HAND_G5_AB_ALIGNMENT_WITH_ALL_ORDERED_OUTER_ERRORS.md`.
It covers both original outer owners, both signs of both outer
differences, and both original AB owners. It supplies a common
A/B frame rho between D and H and the exact tangent normalization
\[
                              b_A+b_B=1.
\tag{8}
\]
The actual H, D, E coordinates, their frames, and their two mixed
inequalities remain fixed. Any earlier strict A/B corner loss is
retained separately; a nonzero original AB difference supplies
such a strict loss.

The theorem first aligns every negative canceling HG2/TD0 side
at fixed endpoint coordinates. A negative noncanceling HG0/TD2
side is restored to a nonnegative hard-quarter tilt if necessary.
Its remaining exact-core composite, on the H side, is
\[
 (\sec e)b_H+a_A\cos t-b_A\sin t
 \ge W(t)+\tfrac12+\tfrac12\sec e+K\tan e,
 \qquad t,e\ge0,
\tag{9}
\]
where t+e is the H-to-common-frame span. The reflected D-side
formula has H,A replaced by D,B. The cap construction supplies
the true core intermediate needed for this composite; its
barrier comparisons can also be applied directly to (9).

A positive noncanceling side retains its exact same-intermediate-
circle cap. A positive canceling side retains its effective cap.
Its comparison G frame lies above H, or its T frame below D.
An already aligned side is retained as the aligned composite.
These are precisely the inputs of the existing positive and
negative scalar transport lemmas. No new packing property of
the comparison intermediates is assumed.

Choose one of A,B whose tangent is at least 1/2 and call it the
large side. The other tangent is at most 1/2 by (8). The tangent
values stay fixed during the next outer comparisons.

## 3. The large side either aligns or retains one negative error

There are four possibilities for the large side.

* If it is already aligned, keep it unchanged.
* For a positive canceling error, Section 6 of
  `HAND_G4_SIGNED_THREE_ZERO_REDUCTION_FOR_CANCELING_OUTER_OWNERS.md`
  aligns it at the same middle and outer coordinates. Its tangent
  is at least 1/2, hence above that lemma's threshold 1/5.
* For a positive noncanceling error, Section 5 of
  `HAND_G5_POSITIVE_HG_ZERO_OWNER_BOUNDARY_REDUCTION.md`
  gives alignment with strict pair slack. Its temporary primary
  lift and restoration of any inherited strict circle loss are
  exactly those proved in Section 4 of that note.
* A negative noncanceling error is retained in (9) if its middle
  tangent is greater than 1/2. If the tangent equals 1/2, the
  small-transverse negative transport instead aligns it at the
  same coordinates.

Negative canceling errors were already aligned in Section 2.
Every nonzero error actually aligned in this list has strict
pair slack. It is either the same-anchor slack of the canceling
transport, the negative small-transverse slack e/150, or the
positive noncanceling slack h/25 after its proved circle lift.

In every case, including a retained negative composite, this
large middle primary satisfies
\[
                              a_{\rm large}>1.1.
\tag{10}
\]
For an aligned side this follows from its composite and the
sorted outer bound b_outer<.9. For (9), its cap parameter is
\[
 D(e)=1+(1/2-b_{\rm outer})\sec e+K\tan e>3/5,
\]
and its nonnegative hard tilt gives a_large>=1/2+D(e)>1.1.
Its circle consequently gives b_large<.665, since
\(1.6^2+1.165^2>Q_0\). By (8), the other tangent satisfies
\[
                         .335<b_{\rm small}\le.5.
\tag{11}
\]
Thus the small side is in the domain of every needed positive
transport as well as of the small-transverse negative transport.

## 4. The small side aligns; both possible zero-transverse endpoints are excluded

If the small side is aligned, retain it. If its remaining error
is negative noncanceling, (11) permits the strict same-coordinate
transport in
`HAND_G4_NEGATIVE_NONCANCELING_ZERO_CORE_TRANSPORT.md`.
If it is positive canceling, (11) is above 1/5 and the positive
canceling transport applies. Negative canceling errors were
already removed.

It remains to consider a positive noncanceling small side. By
(11), Section 4 of
`HAND_G5_POSITIVE_HG_ZERO_OWNER_BOUNDARY_REDUCTION.md`
applies to its entire feasible positive-error interval. Keeping
its transverse coordinate and frame fixed, and preserving every
other anchor, it reduces to alignment or to its G/T transverse-zero
endpoint. If its tangent equals 1/2, direct alignment is already
available by Section 5 of that note. A remaining endpoint thus
has its middle tangent strictly between .335 and .5.

For the moment label that positive side H--G--A. This labeling
may reflect the original cycle; the E sign is not assumed to
survive that reflection. There are exactly two alternatives
for its opposite large side, by Section 3.

### 4.1 The opposite large side has aligned

The endpoint is exactly the one excluded by
`HAND_G5_G_ZERO_ENDPOINT_EXCLUSION.md` and its two affine
stress scalars. The proof allows signed E and therefore also
excludes the reflected T-zero endpoint. The containing radius
is at most Q_0 throughout.

### 4.2 The opposite large side retains a negative error

Write the fixed H-to-D span as x, the aligned common A/B frame
split as t+u+e=x, the positive HG error as h, and the negative
TD error magnitude as e. The positive boundary theorem gives
\[
\begin{gathered}
 .335<b_A<.5<b_B<.665,\qquad b_A+b_B=1,\\
 (a_A-\tfrac12)\cos(t+h)
       -(b_A+\tfrac12)\sin(t+h)=\tfrac12,\\
 b_H\ge\tfrac12+\tfrac12\cos h
               -(\sqrt{q-1/4}-1)\sin h,\qquad0\le t+h<.4,
\end{gathered}
\tag{12}
\]
with A on its actual q-circle. The opposite retained pair is
\[
 (\sec e)b_D+a_B\cos u-b_B\sin u
     \ge W(u)+\tfrac12+\tfrac12\sec e+K\tan e.
\tag{13}
\]
H,D,E and their two mixed constraints have not changed.
Their frame span remains x<=.7 and E lies between them.

Equations (12)--(13) are the exact hypotheses of
`HAND_G5_MIXED_G_ZERO_NEGATIVE_DOMAIN.md`. It proves
\[
                  h>.107,\qquad x+h<.311,
                    \qquad x<.204,\qquad u+e<.12.
\tag{14}
\]
In particular e<.12. The theorem does not require the enlarged
positive boundary frame to retain the original total G-to-D
spread. Only the fixed H-to-D span and the displayed endpoint
conditions are used.

Now apply
`HAND_G5_MIXED_G_ZERO_NEGATIVE_STRESS_EXTENSION.md`.
Its six inequalities are the two endpoint inequalities in
(12), the AB sum, (13), and the unchanged two E constraints.
The first endpoint inequality supplies the hard projection
with G transverse zero; the second supplies the H bound using
the weaker ceiling Q_0 if q<Q_0. Equation (14) supplies its
entire scalar domain. Its stress is strictly positive, so this
endpoint is impossible.

This new stress permits either signed transverse coordinate
of E. Accordingly the argument applies both when the positive
side is the original H side and when it is the original D side.
After the comparison, return to the original labels; the actual
original E data have stayed fixed. No nonnegative-E theorem is
being invoked on a reflected negative-E system.

Both endpoint alternatives are excluded. The small positive
noncanceling side therefore aligns. When its original positive
error was nonzero, strict convexity gives strict pair slack at
alignment. If it had already been the other endpoint, it would
have been excluded outright. The positive boundary theorem also
recreates any inherited strict circle loss after its primary lift.

## 5. The remaining necessary system is already sharply resolved

We have now aligned the small side and either aligned the large
side or retained a single negative noncanceling error there.
In the original labels, the output has exactly
\[
\begin{gathered}
 t,u,e_H,e_D\ge0,\qquad
 \alpha=t+u+e_H+e_D\le7/10,\qquad b_A+b_B=1,\\
 (\sec e_H)b_H+a_A\cos t-b_A\sin t
 \ge W(t)+\tfrac12+\tfrac12\sec e_H+K\tan e_H,\\
 (\sec e_D)b_D+a_B\cos u-b_B\sin u
 \ge W(u)+\tfrac12+\tfrac12\sec e_D+K\tan e_D,
\end{gathered}
\tag{15}
\]
together with the unchanged original E inequalities and its
nonnegative magnitude b_E. At most one of e_H,e_D is nonzero,
and such a side has its middle tangent greater than 1/2.

If both are zero, apply
`HAND_G5_ALIGNED_HARD_CLASS_SHARP_REDUCTION.md` directly.
If one remains, Sections 3--8 of
`HAND_G5_NONPOSITIVE_OUTER_OWNERS_SHARP_REDUCTION.md`
apply to exactly this displayed five-anchor system. Those
sections require only its two composites, sorted circles,
AB sum, original E sign and ordered E split. They do not
require that the comparison intermediates form an original
packing or satisfy an extra mismatch condition.

That proof bounds alpha<.27 and reduces E to its three actual
orientation/transverse boundaries. The E-zero boundary is
excluded by exact negative-error deletion. A large-A negative
side has no remaining E boundary. A large-B negative side
reaches the canonical boundary, where the continuous capture
gives total hard error below .015 and the exact local terminal
proves q>=q_*. Its equality conclusion forces its remaining
negative error to vanish.

Thus every output of Sections 2--4 satisfies q>=q_*. This
proves the sharp inequality for the original class, with
both mixed outer-error signs covered.

## 6. Recover original zeros and original centers at equality

The reductions preserve the strictness information needed to
return to the original candidate. The AB theorem preserves
earlier separate A/B corner losses and creates one whenever
the original AB difference is nonzero. A normalization of an
AB sum greater than one also lowers an actual middle circle.

A negative canceling original error supplies strict same-anchor
pair slack. A crossed noncanceling comparison frame supplies
the strict restoration slack from its barrier theorem. If AB
then moves, that movement independently supplies strict circle
loss; if AB was already aligned, the slack is retained directly.
Every nonzero outer error aligned in Sections 3--4 similarly
supplies strict pair slack. The positive noncanceling primary
lift preserves earlier losses by the strict endpoint argument
proved in its boundary theorem.

Once AB is aligned, strict pair slack can be converted into
a strict middle-circle loss by decreasing that middle primary
slightly. AB depends only on the two tangents. The only other
retained inequality involving this primary is its own outer
composite, whose primary coefficient is a positive cosine.
The bounds a_A,a_B>1.1 and b_A,b_B<.665, now valid on both
sides of (15), leave strict room for sorting and the true core.
Hence this decrease preserves every later necessary hypothesis.
The other outer path and H,D,E remain unchanged.

The aligned sharp theorem preserves those separate circle
ceilings through its split comparison. The nonpositive proof
retains the same A/B losses through E minimization and its
canonical terminal. Their final identities have positive
masses on all five anchor circles. Therefore every strict
A/B loss just listed is incompatible with q=q_*.

Suppose now q=q_*. The original AB difference and any strict
AB normalization must have been zero. There was no crossed
negative comparison restoration and no nonzero negative
canceling error. Every positive original outer error and
every negative small-transverse error must also have been zero,
since each was aligned with the strictness just recorded.

The only possible remaining nonzero outer error is the large
negative noncanceling one in (15). Its frame difference is now
the original frame difference: neither AB alignment nor a
crossed-frame restoration changed it, and the other side's
reductions do not touch it. The sharp nonpositive terminal
forces this error to be zero as well. This proves (6) for the
original candidate.

The original five anchors themselves consequently satisfy the
aligned hard-class hypotheses with their original E data.
Apply `HAND_G5_ALIGNED_HARD_CLASS_SHARP_REDUCTION.md` afresh
to these original anchors. It forces
\[
       \text{BT tilt}=\delta=0,
       \qquad\text{GA tilt}=\epsilon=t_*,
\tag{16}
\]
and the unique five stationary corner vectors. This last
application identifies original centers through their own
sharp inequalities, not through a radius-preserving descendant.

For an original packing, its actual remaining G/T and central
constraints are unchanged. The equality theorem and converse in
`HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md` therefore give
the full weak five-parameter equality family, up to the stated
isometries and relabelings.

Every original outer owner in (5), every outer-error sign, and
both AB owners have now been handled within (2)--(5). Other
original signs, other frame orders, and other hard-quarter or
mixed owners remain separate global-entry questions. No angle
mesh, sampled minimum, state-cover table, external acceptance
result, Lean compilation or CI is a premise.
