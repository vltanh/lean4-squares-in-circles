# Core E: positive-primary exclusion with either E sign

## 1. Statement and the reason for retaining the E sign

Put
\[
 q_L=19577/5000,\qquad Q=9789/2500,\qquad
 h=7/10,\qquad K=13/12.
\tag{1}
\]
Use the actual same-radius boundary-neighbor domain and all the
H,A,B,D hypotheses in Section 1 of
[the core-E positive-GA theorem](HAND_G5_POSITIVE_GA_HG2_CORE_E_COMPLETE_EXCLUSION.md).
In particular H,A are positive sorted outer states, B,D are
negative sorted outer states at one actual ceiling
\(q_L\le q\le Q\), the real frames have spread at most h,
and both actual error variations are at most h. E is on its
true-core boundary. G and T may have either tangent sign and
either radial kind.

The sole change to that theorem's hypotheses is
\[
             -a_E\le y_E\le a_E\le7/12:
             \quad y_E\text{ has either sign}.
\tag{2}
\]
Retain actual HG2 and GA1 with \(d_{GA}\ge0\), either AB
owner, and DE2/3 and EH0/1. Then the same four T regimes
are strictly impossible:
\[
\begin{array}{c|c|l}
 BT&TD&\text{condition}\\ \hline
 2&0&\text{arbitrary errors}\\
 2&2&\text{arbitrary errors}\\
 3&0&d_{BT}\ge0,\quad d_{TD}\text{ arbitrary}\\
 3&0&d_{BT}<0,\quad d_{TD}=0.
\end{array}
\tag{3}
\]

All original weak ties are included. The contradiction is strict
at Q; thus these cases contribute no sharp equality. This is a
sign extension of an actual necessary-system theorem, not a
reflection that silently changes its hypotheses. Sections 2--4
check every use of E's sign. No new scalar inequality or stronger
coefficient claim is needed: the seven existing certificates are
unchanged.

## 2. A nonnegative E-primary total has the same charge

Write \(a=a_E\), \(z=-y_E\), and \(b=|z|\). The two actual
primary projections at errors d and r are
\[
 P_{DE3}=a_D+a\sin d+z\cos d,\qquad
 P_{EH1}=a_H+a\sin r-z\cos r.
\tag{4}
\]
Their actual secondary counterparts are
\[
 P_{DE2}=a_D\cos d+b_D\sin d+z,\qquad
 P_{EH0}=a_H\cos r+b_H\sin r-z.
\tag{5}
\]
These formulas retain the signed z; no state is replaced when
they are added. If both primaries are retained and their sum is
\(e=d+r\ge0\), the E deficit is
\[
 L_z=W(d)+W(r)-2-a(\sin d+\sin r)
                              -z(\cos d-\cos r).
\tag{6}
\]
It obeys exactly the old lower bound
\[
 L_z\ge J(e):=-\frac1{12}\sin e-K(1-\cos e).
\tag{7}
\]

For clarity, this also follows directly from the proof of
equations (34)--(39) of the cited core-E theorem. Interchanging
d and r changes z to -z and leaves e and both angle variations
unchanged. The proof minimizes over both possible individual
signs and over both endpoint splits. Thus its worst transverse
coefficient is b, independent of the sign of z. With two
nonnegative errors, the smaller intrinsic endpoint has value
\[
 (1/2-a)\sin e-(1/2+b)(1-\cos e)\ge J(e).
\tag{8}
\]
With opposite individual signs, its half-angle expression is
the same expression (38) there, with b in place of the formerly
nonnegative z. Its two coefficients are positive and ordered
because \(0\le b\le a\le7/12\). The same concavity and
near-versus-far endpoint comparison therefore apply. This
proves (7) on the whole signed domain, including e=0.

For one retained primary and one retained secondary, summing
(4)--(5) instead gives one of
\[
 (1/2-a)\sin e-(1/2+z)(1-\cos e),\qquad
 (1/2-a)\sin e-(1/2-z)(1-\cos e).
\tag{9}
\]
Each is bounded below by (8). With two secondaries the E force
cancels and its charge is zero. Hence (7) treats every
nonnegative selected E-primary total, with exactly the same
ordinary H/D angles and the same enlargement of the variation
domain as the original proof.

## 3. A negative E-primary total has the same actual flat-core reduction

For z nonnegative, Section 6 of the core-E theorem already
provides the reduction. We verify the missing case z negative
without reflecting the other five roles.

There is an exact local involution of the D,E,H triple:
\[
 (\bar D,\bar E,\bar H)=(H,E,D),\qquad
 \bar\theta_i=-\theta_i,\qquad \bar y_i=-y_i.
\tag{10}
\]
Thus \(\bar d=r\), \(\bar r=d\), and
\(\bar z=-\bar y_E=-z>0\). Direct substitution in (4)--(5)
gives the complete witness correspondence
\[
\begin{array}{c|cccc}
 \text{barred witness}&DE3&EH1&DE2&EH0\\ \hline
 \text{original witness}&EH1&DE3&EH0&DE2.
\end{array}
\tag{11}
\]
The width W of each error is identical. The barred D and H
are respectively negative and positive sorted outer states
at the same q. The true-core E has nonpositive barred tangent.
Every hypothesis of the local E reductions is therefore
present after (10).

This invocation is only local. Apply the constructions in
Sections 2--5 of
[the mixed-negative E reduction](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md)
to this triple, then undo (10). They change E alone; original
H and D, all five other states, and every other actual witness
stay fixed. The frame motion stays between the same original
E and endpoint frames, and each error variation decreases by
the same amount. The E sign is preserved on its original side
of zero. The endpoint is on the actual core, with original
weak contacts retained or an actual secondary selected as
specified by (11).

Here is the same-radius check, rather than a substitution of
the Q circle for the actual q circle. The contact and core
formulas of that local proof do not involve Q. Its sole lower
outer-radius step is the tangent-zero endpoint (19), where
the comparison corner has square less than 541/144. Since
\[
                          541/144<q_L\le q,
\tag{12}
\]
the actual outer barred H, which is original D, supplies the
strict secondary witness. The other coordinate bounds use
only \(q\le Q\). Flat comparison E states are below q_L.
The actual continuous neighboring inequalities and the
boundary-neighbor bridge preserve cyclic order and winding
after undoing (10). No nonneighbor separation is asserted.

The two flat-entry facts likewise exchange exactly:

- For z<0, a genuine negative DE3 with DE2 unavailable is
  the barred genuine negative EH1. It forces
  \(a_E=7/12\) and \(|z|<39/250\).
- A retained DE2 gives
  \(|z|\le\sqrt{a_D^2+b_D^2}-1<a_0-1<.415\), so a true-core
  E is flat. This is the barred EH0 flat-entry inequality.

If both E primaries are negative, either an actual secondary
can be selected, or the adverse signed primary supplies that
flat entry. If their signs are opposite and their sum negative,
the local constructions just verified reach a negative flat
primary with a secondary. If selecting an actual secondary
instead leaves a nonnegative selected total, Section 2 applies.
These are precisely the finite alternatives of the original
Section 6, with H and D exchanged where required.

## 4. The secant and ordinary-angle bounds are independent of E's sign

On a flat E, give a negative primary of magnitude s the
weight \(\sec s\), and a secondary weight one. If both E
primaries are negative, use their respective secant weights.
In either case the two coefficients of the *signed* z in
(4)--(5) cancel exactly. The resulting radial gain is the
same \(F_n(s)\) on H or \(F_c(s)\) on D used in Section 6
of the core-E theorem:
\[
 F_a(s)=\sec s+K\tan s
       -\sqrt Q\sqrt{\sec^2s+a^2}
       -1+\sqrt Q\sqrt{1+a^2}.
\tag{13}
\]
The force left at a given outer anchor depends on which actual
E edge was primary, not on the canceled sign of z. In both
coefficient families every unmodified opposite coefficient is
at least k=.863. Thus the same lower secant gains, including
\(F_a(s)>1.03s\) for a at least k, hold without change.

The ordinary H and D one-angle estimates in Section 6 of
[the angular envelope](HAND_G5_POSITIVE_GA_CORE_E_ANGULAR_ENVELOPE.md)
already permit either modified anchor. Their ranges
\(1\le\sec s<1.308\) and \(.7\le c_{\rm rot}\le1.4\)
are unchanged. If negative TD2 and negative DE3 both modify D,
the same nonpositive mixed derivative of the full-circle norm
proves the additive gain. No new simultaneous modification is
introduced by changing z's sign.

All other forces, the varying-B comparison, the four T
reductions, and the positive G/T split are independent of z.
Sections 7--9 of the original theorem now leave precisely its
old charges (43). The seven whole-interval inequalities in
[the scalar companion](HAND_G5_POSITIVE_GA_CORE_E_SCALAR_CERTIFICATES.md)
therefore give the same strict contradiction. This proves
(3) with either E sign on the full continuous domains.

## 5. The reflected positive-BT theorem, with the sign change checked

Now return to the original normalized E sign \(y_E\le0\).
Suppose actual BT3 has nonnegative error and actual TD0 is
retained. Physically reflect the entire actual boundary cycle
and reverse the roles by
\[
 (H',G',A',B',T',D',E')=(D,T,B,A,G,H,E),
 \qquad \theta'=-\theta,\qquad y'=-y.
\tag{14}
\]
The boundary-neighbor reflection calculation gives the same
quarter word, the same radius, core distances, radial kinds,
frame spread and both variations. Each reversed error equals
the old error. On a quarter edge the owner map is
\(0\leftrightarrow2\), \(1\leftrightarrow3\); on a zero
edge it is \(0\leftrightarrow2\). Thus original BT3/TD0
becomes GA1/HG2 with the same nonnegative primary error.
The reflected E has nonnegative tangent, which is now covered
by the theorem just proved.

Translating (3) back gives the following **strictly excluded
positive-BT/core-E domains**:
\[
\begin{array}{c|c|l}
 GA&HG&\text{condition}\\ \hline
 0&2&\text{arbitrary errors}\\
 0&0&\text{arbitrary errors}\\
 1&2&d_{GA}\ge0,\quad d_{HG}\text{ arbitrary}\\
 1&2&d_{GA}<0,\quad d_{HG}=0.
\end{array}
\tag{15}
\]
AB, DE and EH retain their full original owner alternatives
and signed errors. The original E remains the original
nonpositive core state; reflection was only used to apply an
explicitly sign-symmetric theorem. In particular (15) closes
the formerly missing coupled orientation
\[
   \text{genuine negative GA1 with HG aligned}
   \quad+\quad
   \text{positive BT3 with arbitrary TD0}
\tag{16}
\]
for core E. It also closes sole positive BT3/TD0 with actual
GA0 and either original HG owner. The opposite mixed orientation
was already included in (3).

## 6. What this closes in the finite coupled join

The [uniform-radius pair theorem](HAND_G5_UNIFORM_RADIUS_PRIMARY_PAIR_TRANSPORT.md)
and the two genuine-negative local companions change only G
or only T. Thus their endpoint choices can be composed while
all five anchors and E's radial kind stay fixed. After selecting
an already available hard witness and normalizing any primary
pair, each unresolved side has one of two terminal types:

| Side | Positive terminal | Genuine negative terminal |
| --- | --- | --- |
| H/G/A | GA1 at positive error, actual HG2 (alignment permitted) | GA1 at negative error, HG aligned, GA0 unavailable |
| B/T/D | BT3 at positive error, actual TD0 (alignment permitted) | BT3 at negative error, TD aligned, BT2 unavailable |

For negative GA1 with either HG owner, the canceling and
noncanceling local companions reach GA0 or HG alignment. Their
reflected three-state statements reach BT2 or TD alignment for
negative BT3. These local uses involve no E sign hypothesis.
Their flat comparison state is canonical at the actual q.
The direct gap check in (27) of the uniform-radius pair note
applies to either retained HG owner: the changed HG gap lies
above -h, and the changed GA gap is positive or lies above -h;
an allegedly nonpositive gap would contradict the actual
two-square angular band. Their sum is unchanged. Clamping G
to an endpoint of the H/A frame interval preserves each
variation when G originally lies between those frames and
decreases both variations otherwise. Thus both local companions
have the boundary eligibility needed here, not merely local
algebraic feasibility. The reflected check applies to T.
For the two retained primary pairs HG0/GA1 and BT3/TD2, the
same-radius theorem treats every signed total and intermediate
sign. A zero quarter error supplies the actual hard witness as
a weak tie. Hence the table has no omitted zero-error case.

When both sides remain unresolved and E is core, their four
terminal sign combinations have the exhaustive join

| GA1 sign | BT3 sign | Completed theorem |
| --- | --- | --- |
| positive | positive | (3), third row |
| positive | negative | (3), fourth row |
| negative | positive | (15), fourth row |
| negative | negative | [Both-negative same-q conversion](HAND_G5_GLOBAL_PRIMARY_ENTRY_BOTH_NEGATIVE_DIRECT_SECOND_TRANSPORT.md), Section 7 |

The first three rows are impossible throughout the working
band. The fourth reaches the actual hard class and has strict
H/D anchor losses if both hard owners were unavailable. It
therefore has \(q>q_*\). This completes the **coupled
core-E terminal sign join**, with both original intermediate
signs and all weak witness ties admitted before normalization.

Rows where normalization already supplies GA0 or BT2 must
still invoke the corresponding one-primary theorem. In
particular, this note does not infer sole negative BT3 entry
from the two-negative theorem. It also does not cover outer E.
These are separate rows of the unrestricted global-entry join.

All statements above are hand-proof consequences of actual
contact identities and previously proved whole-domain scalar
bounds. No new angle mesh, optimizer certificate, Lean
compilation, or CI result is used.
