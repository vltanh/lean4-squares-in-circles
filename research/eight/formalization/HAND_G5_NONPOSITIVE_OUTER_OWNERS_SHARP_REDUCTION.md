# Both original outer zero owners are sharp on the nonpositive-error ordered class

## 1. Original-candidate statement

Put
\[
 Q_0=\frac{9789}{2500},\qquad
 Q_1=\frac{1957767069}{500000000},\qquad
 q_L=\frac{19577}{5000},\qquad K=\frac{13}{12}.
\tag{1}
\]
Retain the original normal signed tangents
\[
 (y_H,y_G,y_A,y_B,y_T,y_D,y_E)
 =(b_H,-b_G,b_A,-b_B,b_T,-b_D,-b_E),\qquad b_i\ge0,
\tag{2}
\]
the original sorted circle bounds and the true core condition:
\[
 a_i\ge b_i\ge0,\qquad
 (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q_0.
\tag{3}
\]
Assume real frames of spread at most `7/10`, with
\[
 \theta_D\le\theta_A,\theta_B\le\theta_H,
 \qquad \theta_D\le\theta_E\le\theta_H.
\tag{4}
\]
Both original outer differences are nonpositive:
\[
                 \theta_G-\theta_H\le0,
                 \qquad\theta_D-\theta_T\le0.
\tag{5}
\]
Retain any original SAT witnesses in the following sets:
\[
\begin{array}{c|rrrrrrr}
 \text{edge}&HG&GA&AB&BT&TD&DE&EH\\ \hline
 \text{axis}&0\text{ or }2&0&0\text{ or }2&2&0\text{ or }2&3&1.
\end{array}
\tag{6}
\]

**Sharp original-class theorem.** Every such candidate satisfies
`q>=q_*`. At equality all three original zero differences
\[
 \theta_G-\theta_H,\qquad\theta_B-\theta_A,
 \qquad\theta_D-\theta_T
\tag{7}
\]
vanish. Its original five anchors are the unique stationary
anchors at tilt `t_*`, with the canonical hard and E splits.
For an original packing, its actual remaining constraints give
the full weak five-parameter equality family and its converse.

The signs, order, true core and retained owners above are
hypotheses. In particular this theorem does not assume or claim
an unrestricted global capture into this class. It includes
either original outer owner and either original AB owner, but
does not include a positive outer difference.

The stationary enclosure gives `q_L<q_*<Q_1<Q_0`. Therefore
`q>Q_1` already proves the strict lower bound. If `q<q_L`,
enlarge the containing ceiling to `q_L` without moving the
original centers. It suffices below to work at
\[
                          q_L\le q\le Q_1.
\tag{8}
\]
All constructions use this working q in their circle formulas.
At an equality candidate `q=q_*`, no enlargement occurs.

## 2. Align AB and retain only nonpositive outer comparisons

Apply
`HAND_G5_AB_ALIGNMENT_WITH_ALL_ORDERED_OUTER_ERRORS.md`.
It first aligns every negative canceling HG2 or TD0 side by
the same-anchor transport in Section 3 of
`HAND_G4_SIGNED_THREE_ZERO_REDUCTION_FOR_CANCELING_OUTER_OWNERS.md`.
For a negative noncanceling HG0 or TD2 side whose intermediate
frame has crossed the adjacent middle frame, Section 4 of
`HAND_G4_NEGATIVE_NONCANCELING_ZERO_CORE_TRANSPORT.md` restores
that comparison frame, retaining H, A, B and D.

The AB theorem then supplies a common frame
`rho in [theta_D,theta_H]`, sorted middle coordinates at the
same q, and the exact normalization
\[
                              b_A+b_B=1.
\tag{9}
\]
H, D and E, their coordinates and frames, and both mixed
inequalities remain unchanged. The common frame is one of the
original A/B frames.

No positive outer error is introduced here. On a negative H
side the comparison G frame stays between the common frame
and H; if A passes the old G frame, the continuous cap sets G
at the new A frame. The reflected construction has the same
property for T between D and the common frame. An already
aligned composite stays aligned. Thus every remaining side is
either aligned or negative noncanceling.

Normalize the common A/B frame to zero. Write the H frame as
`Theta>=0` and the D frame as `-Upsilon<=0`. There are
nonnegative angles
\[
 t,u,e_H,e_D\ge0,\qquad
 t+e_H=\Theta,\quad u+e_D=\Upsilon,
 \quad\alpha=\Theta+\Upsilon\le7/10,
\tag{10}
\]
such that the two retained outer composites are
\[
\begin{aligned}
 (\sec e_H)b_H+a_A\cos t-b_A\sin t
 &\ge W(t)+\frac12+\frac12\sec e_H+K\tan e_H,\\
 (\sec e_D)b_D+a_B\cos u-b_B\sin u
 &\ge W(u)+\frac12+\frac12\sec e_D+K\tan e_D,
\end{aligned}
\tag{11}
\]
where `W(z)=(1+cos z+sin z)/2`. An aligned side has its e
equal to zero, so (11) is its usual aligned composite.

For a noncanceling side (11) is obtained from its same-G/T
pair using the true core primary bound `7/12`. The AB theorem
also supplies a concrete sorted core intermediate realizing
each cap when its comparison frame changes. Only the displayed
necessary system is retained; later steps require no new
packing or physical-gap assertion about these intermediates.

## 3. The common chain has a small total span and an E boundary

Section 5 of
`HAND_G4_NEGATIVE_NONCANCELING_ZERO_CORE_TRANSPORT.md`
applies to (9)--(11). In particular,
\[
\begin{gathered}
 a_A,a_B>1.1,\qquad .335<b_A,b_B<.665,\\
 b_H+a_A\ge2+\frac{167}{200}\sin\Theta,\qquad
 b_D+a_B\ge2+\frac{167}{200}\sin\Upsilon,\\
 a_H+a_D<1.9968-.718\sin\alpha<2,\qquad
                          0<\alpha<\frac{27}{100}.
\end{gathered}
\tag{12}
\]
The zero-span alternative is excluded by the mixed sum and
`a_H+a_D<2`.

The unchanged original E inequalities are
\[
\begin{gathered}
 \delta,\epsilon\ge0,\qquad\delta+\epsilon=\alpha,\\
 a_D+a_E\sin\delta+b_E\cos\delta\ge W(\delta),\\
 a_H+a_E\sin\epsilon-b_E\cos\epsilon\ge W(\epsilon).
\end{gathered}
\tag{13}
\]
At fixed H, A, B and D and their frames, that same section
proves that minimizing E's corner gives a descendant on one
of the three boundaries
\[
                    b_E=0,\qquad\delta=0,
                           \qquad\epsilon=0.
\tag{14}
\]
Its E corner is no larger than the input E corner. The other
four anchors and all their actual corner values stay fixed.
If the input E has `b_E>0`, `delta>0` and `epsilon>0`, its
corner is strictly larger than this minimum: the one-contact
directions and the strictly negative second orientation
derivative exclude every such interior minimum.

These statements use the complete shared-chain bounds (12),
without assuming either negative outer error is small.

## 4. A small middle tangent aligns its own negative side

Equation (9) implies that at least one of `b_A,b_B` is at most
`1/2`. If `b_A<=1/2` and `e_H>0`, the small-transverse
transport in
`HAND_G4_NEGATIVE_NONCANCELING_ZERO_CORE_TRANSPORT.md`
gives, at the same H and A coordinates,
\[
 b_H+a_A\cos(t+e_H)-b_A\sin(t+e_H)
 >1+W(t+e_H)+\frac{e_H}{150}.
\tag{15}
\]
Thus replace `t,e_H` by `t+e_H,0`. The true core realization
in the AB theorem justifies this use after an AB construction;
equivalently its barrier proof applies directly to (11).
The reflected statement replaces `u,e_D` by `u+e_D,0` when
`b_B<=1/2`.

The middle coordinates, AB sum, H, D, E, total span alpha and
mixed constraints are unchanged. Consequently both sides
align when both middle tangents equal `1/2`. More generally,
after these replacements either both sides are aligned, or
only a side with middle tangent greater than `1/2` can retain
a negative error.

If both sides are aligned, the five-anchor theorem
`HAND_G5_ALIGNED_HARD_CLASS_SHARP_REDUCTION.md`
already gives `q>=q_*`. Its proof preserves any strict A/B/E
corner loss. It remains to treat the two possible large-tangent
sides.

## 5. A remaining large-A negative side has no E endpoint

Suppose `b_A>=1/2`, the D side is aligned, and the H side is
represented by (11). Use the E minimizer (14).

The endpoint `b_E=0` is impossible by
`HAND_G5_NEGATIVE_OUTER_E_ZERO_ERROR_DELETION.md`.
That theorem covers either or both negative outer sides,
retains the actual A/B circles, and requires only the same
nonnegative angular split as (10), (13).

The endpoint `delta=0` is impossible by
`HAND_G5_NEGATIVE_HG_LARGE_TRANSVERSE_DE_ALIGNMENT_EXCLUSION.md`.
Its complete simplex theorem has exactly (9), (11),
`e_D=0`, `b_A>=1/2`, `alpha<=27/100` and the two mixed
constraints at `delta=0` as its inputs. It is proved at Q_1.

The last endpoint `epsilon=0` is also impossible, directly.
From (12) and `b_A>=1/2`,
\[
 a_A\le\sqrt{Q_0-1}-\frac12,\qquad
 b_H\ge\frac52-\sqrt{Q_0-1}.
\]
The H circle gives
\[
 a_H\le\sqrt{6\sqrt{Q_0-1}-8}-\frac12<1.
\tag{16}
\]
The final inequality follows by positive squaring from
`Q_0<2257/576`, or `sqrt(Q_0-1)<41/24`.
But `epsilon=0` in (13) would give `a_H>=1+b_E>=1`.
All three possible E minima are therefore excluded.

This argument retains the original nonnegative magnitude
`b_E` in (13). The inference from (16) is not used after a
reflection that changes that sign.

## 6. A remaining large-B negative side reaches the canonical boundary

Suppose now `b_B>=1/2`, the H side is aligned, and the D side
may retain a negative TD2 error. The E-zero endpoint remains
impossible by the same deletion theorem.

The endpoint `epsilon=0` is excluded by the signed-E version
of the large-transverse DE-alignment stress. To make the sign
change explicit, use the algebraic relabeling
\[
 (H',A',B',D')=(D,B,A,H),\qquad b_E'=-b_E,
\tag{17}
\]
and reverse frame order. The E circle is unchanged because
it uses `|b_E'|=b_E`. At `epsilon=0`, the original mixed
inequalities become precisely
\[
 a_{D'}+b_E'\ge1,\qquad
 a_{H'}+a_E\sin\alpha-b_E'\cos\alpha\ge W(\alpha).
\tag{18}
\]
The negative D composite becomes the theorem's negative H'
composite, with `b_{A'}=b_B>=1/2`; the opposite side is aligned.
Thus all its hypotheses hold. Its actual E support estimate
allows either sign of `b_E'`, so (18) is impossible.

The E minimizer must consequently have
\[
                         \delta=0,\qquad\epsilon=\alpha.
\tag{19}
\]
Moreover the same endpoint exclusions apply to every feasible
E before minimization with these fixed non-E data. Thus it has
`b_E>0` and `epsilon>0`. If its original delta was positive,
the E reduction produces a strict E-circle loss, while keeping
H, A, B and D fixed.

## 7. The canonical boundary satisfies the exact small-error capture

Rename the remaining angles so that t is the nonnegative
BT tilt, e the magnitude of the negative TD2 error, and u the
aligned H-side tilt. Equations (9), (11), (13), (19) become
\[
\begin{gathered}
 t,u,e\ge0,\qquad\alpha=t+u+e<27/100,\\
 b_H+a_A\cos u-b_A\sin u\ge1+W(u),\\
 b_A+b_B=1,\qquad b_B\ge\frac12,\\
 (\sec e)b_D+a_B\cos t-b_B\sin t
 \ge W(t)+\frac12+\frac12\sec e+K\tan e,\\
 a_D+b_E\ge1,\qquad
 a_H+a_E\sin\alpha-b_E\cos\alpha\ge W(\alpha).
\end{gathered}
\tag{20}
\]
All five actual anchor circles are retained.

Apply the relabeling `(H',A',B',D')=(D,B,A,H)` again, now
with the nonnegative transverse magnitude `c_E=b_E`.
The last two lines become
\[
 a_{D'}+a_E\sin\alpha-c_E\cos\alpha\ge W(\alpha),
 \qquad a_{H'}+c_E\ge1.
\tag{21}
\]
Together with the unchanged sorted circles, the first three
contacts in (20) are exactly the hypotheses of
`HAND_G5_NEGATIVE_CANONICAL_SMALL_ERROR_CAPTURE.md`.
That theorem proves on this whole necessary system
\[
                               t+e<\frac3{200}.
\tag{22}
\]
It uses one common stress on each fixed-alpha simplex and
four intrinsic vertices of its truncation `t+e>=3/200`.
Its explicit continuous weight formulas and whole-polynomial
inequalities require no original mismatch or physical-gap input.

Undo the relabeling. Equations (20), (22) now satisfy every
assumption of
`HAND_G5_CANONICAL_NEGATIVE_BOUNDARY_SMALL_ERROR_TERMINAL.md`.
That direct five-anchor theorem gives `q>=q_*`. At equality it
forces
\[
                        t=e=0,\qquad u=\alpha=t_*,
\tag{23}
\]
and the five stationary anchors.

The terminal reconstructs core intermediates only to evaluate
its exact force-and-circle identity. It proves all required
coordinate and tangent bounds for them and invokes the tail
and stationary estimates through that identity. Therefore no
G1, physical-gap, or omitted nonneighbor condition is being
inferred for the constructed five-anchor system.

Sections 4--7 exhaust the lower-bound alternatives. They prove
the theorem's inequality for every original candidate (2)--(6).

## 8. Strict losses survive every reduction

For original-center equality, record the following sources of
strictness before invoking either sharp five-anchor theorem.

* Every nonzero original AB difference produces strict room
  in the common-frame cap comparison. A sufficiently small
  primary decrease makes one new A/B circle strictly smaller
  than q. The AB theorem preserves earlier strict A/B losses
  separately: a retained anchor keeps its loss, and a changed
  anchor recreates its loss through the strict cap comparison.
* Every negative canceling original outer difference has
  same-anchor composite slack greater than `3e/20`, by the
  signed three-zero transport. If AB was already aligned this
  slack is retained; if AB moves, the preceding item already
  supplies a strict middle-circle loss.
* Restoring a crossed noncanceling G frame with
  `theta_G-theta_A=t_0<0` leaves pair slack greater than
  `-t_0/4`. The reflected T restoration has the same property.
  This slack is again retained when AB is already aligned;
  a nonzero AB move independently gives strict circle loss.
  Thus restoration cannot erase equality information even
  when its new outer error becomes zero.
* Every nonzero remaining negative error on a small-tangent side has
  the slack `e/150` in (15), at unchanged anchor coordinates.
  Normalizing an AB sum strictly greater than one also lowers
  an actual middle circle strictly.
* An interior E with positive delta on the surviving large-B
  branch yields the strict E-circle loss in Section 6.
  The fully aligned theorem retains the identical strictness
  for its own E-boundary reduction.

Here is why the pair slacks really give circle losses in this
necessary system. Once AB is aligned, its inequality involves
only `b_A+b_B`. Decrease the corresponding middle primary by
a sufficiently small positive amount. Its only retained
noncircle inequality is its own cap in (11), or its aligned
version; the coefficient of that primary is a positive cosine.
The strict pair slack therefore absorbs the decrease. The
other outer path, AB and both mixed constraints stay fixed.
The bounds `a_A,a_B>1.1` and `b_A,b_B<.665` in (12) leave
strict room for sorting and the true core. Thus the primary
decrease gives an actual strict corner loss and preserves all
the hypotheses used subsequently.

The small-tangent transports do not lift either middle anchor.
The E minimization leaves their actual corner values unchanged.
The fully aligned sharp theorem preserves separate A/B
circle ceilings through its split comparison. The canonical
negative terminal retains all five actual circle inequalities
directly. Both sharp identities have five positive circle
masses. Consequently any strict A/B or E loss described above
is incompatible with `q=q_*`.

## 9. Recover the original zeros and the original stationary anchors

Suppose `q=q_*`. Section 8 first forces the original AB
difference to vanish. It also excludes any nonzero negative
canceling outer difference, any crossed noncanceling frame
restoration, and every nonzero negative error aligned by the
small-tangent transport. The common AB frame and the remaining
uncanceled intermediate frames therefore agree with their
original values; no AB sum normalization can have been strict.

If both outer sides have aligned, all three original zero
differences already vanish. Otherwise the only surviving side
is the large-B negative TD2 side: the large-A alternative was
excluded in Section 5. Its remaining e in (20) is now exactly
the magnitude of its original outer difference. None of the
preceding surviving steps changes that frame difference.
Equation (23) forces e to be zero as well. Thus (7) vanishes
in every equality case.

The original five anchors themselves now satisfy the aligned
hard-class inequalities, with their original mixed split and
original own-frame coordinates. Apply
`HAND_G5_ALIGNED_HARD_CLASS_SHARP_REDUCTION.md` afresh to
these original anchors. It forces
\[
 \text{BT tilt}=\delta=0,
 \qquad\text{GA tilt}=\epsilon=t_*,
\tag{24}
\]
and fixes all five original corner vectors to the unique
stationary ones. This final invocation does not identify an
original center with a moved descendant merely because their
containing radii coincide.

For an original packing, the actual remaining G/T sliders and
central square obey its unchanged remaining packing
constraints. The full equality theorem and converse in
`HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md` therefore
apply to that original packing, up to the stated isometries
and relabelings.

This closes the lower bound and original-center equality on
the entire ordered nonpositive-outer-error class (2)--(6).
Mixed outer-error signs, other frame orders, other original
signs and other original quarter or mixed owners remain
separate entry questions. No state table, angle mesh, sampled
minimum, external acceptance result, Lean compilation or CI
is a premise of this proof.
