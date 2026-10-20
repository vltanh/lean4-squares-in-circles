# Positive paired E primaries reduce at the actual radius

## 1. Domain, conclusion and the retained E sign

Put
\[
 q_L=19577/5000,\quad Q_1=1957767069/500000000,
 \quad Q=9789/2500,\quad h=7/10.
\tag{1}
\]
Fix one actual ceiling \(q_L\le q\le Q_1\). Work with a
boundary-neighbor cycle at q in role order H,G,A,B,T,D,E,
quarter word 0101011, actual weak neighboring witnesses,
frame spread below h, and both captured variations below h.
H is a positive sorted outer q state and D is a negative
sorted outer q state. E may have either sign or radial kind.
All other states and owners are arbitrary within that domain.

Retain actual DE3 and EH1 at errors
\[
 d=\theta_E-\theta_D\ge0,\qquad
 e=\theta_H-\theta_E\ge0,\qquad t=d+e<h.
\tag{2}
\]
Write \(y_E\) for E's physical signed tangent and put
\[
 c_q=\sqrt{q/2}-1/2,\qquad
 a_q=\sqrt{q-1/4}-1/2,
 \qquad a(y)=\sqrt{q-(|y|+1/2)^2}-1/2.
\tag{3}
\]
The actual inequalities are
\[
 a_D+a_E\sin d-y_E\cos d\ge W(d),\qquad
 a_H+a_E\sin e+y_E\cos e\ge W(e),
\tag{4}
\]
where \(W(s)=(1+\cos s+|\sin s|)/2\).

**Same-radius endpoint theorem.** Replacing only E produces
an actual boundary-neighbor cycle at the same q with one of
\[
 \begin{array}{c|cc}
 &DE&EH\\ \hline
 d'=0&2&1\text{ at }t\\
 e'=0&3\text{ at }t&0.
 \end{array}
\tag{5}
\]
The six other actual states, their coordinates and frames,
and every other retained witness are unchanged. The new E
is sorted outer at q. Its frame stays between the original
D and H frames, and the two nonnegative errors keep their
sum t. Thus frame spread cannot increase, and both captured
variations are unchanged.

The conclusion deliberately permits either sign of the
new E tangent. In particular, an initially nonpositive E
need not remain nonpositive. Section 6 identifies the exact
remaining sign interface when (5) is used with positive GA1.
Section 7 closes that interface at the sharp ceiling without
using a symmetry exclusion.

If t=0, both errors already vanish, and the corresponding
secondary witnesses are actual ties. If one of d,e is zero,
that edge can already be reselected; the construction is
only needed when both are positive.

## 2. The larger endpoint scalar and the two contact arcs

Choose the larger of \(a_H,a_D\) as the first scalar B;
let C denote the other scalar. The following two local
coordinate choices give exactly the same algebra:
\[
 \begin{array}{c|ccccc}
 \text{choice}&B&C&u&v&y\\ \hline
 a_H\ge a_D&a_H&a_D&e&d&-y_E\\
 a_D\ge a_H&a_D&a_H&d&e&y_E.
 \end{array}
\tag{6}
\]
At equality either choice works. In both cases
\[
 c_q\le C\le B\le a_q,\qquad u,v\ge0,\quad u+v=t,
\]
and (4) becomes
\[
 B+a_E\sin u-y\cos u\ge W(u),\qquad
 C+a_E\sin v+y\cos v\ge W(v).
\tag{7}
\]
Raising \(a_E\) at fixed y and frame to a(y) improves both
inequalities, preserves sorting and containment at q, and
cannot decrease distance from the open true core. The
local two-square band preserves cyclic order during this
radial entry, exactly as in the
[same-radius primary-pair note](HAND_G5_UNIFORM_RADIUS_PRIMARY_PAIR_TRANSPORT.md).
Only its final outer state is used in the boundary arguments.

On the outer circle set
\[
 F_1(u,y)=B+a(y)\sin u-y\cos u-W(u),
\]
\[
 F_2(v,y)=C+a(y)\sin v+y\cos v-W(v).
\tag{8}
\]
Since \(|a'(y)|\le1\) and \(u,v<h<\pi/4\),
\[
                      (F_1)_y<0,\qquad(F_2)_y>0.
\tag{9}
\]
The inequalities hold on both circle arcs and across y=0
by continuity. Increase y to the largest value allowed by
F1. This preserves the second witness and gives its unique
first contact, unless the upper diagonal y=cq is reached.
The lower diagonal never gives the first contact:
\[
 F_1(u,-c_q)=B-1/2+(c_q-1/2)(\sin u+\cos u)>0.
\tag{10}
\]
The contact root increases strictly with u, because
\[
 (F_1)_u=(a(y)-1/2)\cos u+(y+1/2)\sin u>0.
\tag{11}
\]
For y below −1/2, sorting and \(\cos u>\sin u\) prove
(11); otherwise both terms are nonnegative and the first
is positive. At u=0 the contact root is
\[
                             y=B-1\in(-c_q,c_q).
\tag{12}
\]
Thus there are at most two contact arcs, separated by one
zero-tangent contact, followed possibly by an upper-diagonal
arc. This intrinsic decomposition is independent of C.

## 3. Strict contact concavity and the finite candidate set

Put \(P=B-1/2\), \(S=\sin t\), \(K=\cos t\).
At a positive-y contact, the exact required value of C is
\[
 \mathcal C_+(u)=1/2-PK+(S+K)\cos u+S\sin u
                     -S\sqrt{q-(\sin u-P)^2}.
\tag{13}
\]
At a negative-y contact it is
\[
 \mathcal C_-(u)=1/2-PK+(S+K)\cos u
                     -S\sqrt{q-(\sin u+\cos u-P)^2}.
\tag{14}
\]
These identities follow by resolving the shifted circle
coordinates along the contact axis; they are the exact
identities (14) in the same-radius primary-pair note.
Neither identity uses an upper bound on C.

Here \(3/8<P<183/200\). The uniform rational reserves in
that note give respectively
\[
 \sqrt{q-(\sin u-P)^2}>7/4,
 \qquad\sqrt{q-(\sin u+\cos u-P)^2}>5/3.
\tag{15}
\]
Their exact differentiated formulas therefore give
\[
 \mathcal C_+''< -\frac{301577}{6860000}<0,
 \qquad
 \mathcal C_-''< -\frac{471}{2500}<0.
\tag{16}
\]
All lower-radius comparisons use qL; all upper-radius
comparisons use \(q<Q<4\). The circle equations themselves
retain the original q. On the upper diagonal the demand is
\[
 \mathcal C_{\rm diag}(u)
        =1/2-(c_q-1/2)\{\sin(t-u)+\cos(t-u)\},
\tag{17}
\]
which increases strictly with u.

Concavity on each contact arc and monotonicity on (17)
show that some feasible maximal state yields at least one
feasible candidate of these four types:

1. the first alignment u=0;
2. the second alignment v=0;
3. the unique interior contact y=0;
4. the first upper-diagonal contact y=cq.

The formulas (13)--(14) agree in value at y=0. No global
concavity across that join, or connected feasible path from
the original contact to a selected candidate, is assumed.

## 4. Direct endpoint eligibility and the diagonal exclusion

The physical gap verification differs from the T-pair
proof: both E edges are quarter edges, so no upper bound
C<1 is needed. Let
\[
 \alpha=\arctan(y/a(y)),\qquad
 \beta_H=\arctan(b_H/a_H),\quad
 \beta_D=\arctan(b_D/a_D).
\]
For the first row of (6), the physical DE and EH gaps are
\[
 \pi/2+v+\alpha-\beta_D,
 \qquad \pi/2+u-\alpha-\beta_H.
\tag{18}
\]
For the second row the same formulas hold after exchanging
H,D and the two edges. A strictly sorted E has
\(-\pi/4<\alpha<\pi/4\), whereas \(\beta_H,\beta_D\le\pi/4\),
so both gaps are positive. At the only possible diagonal
candidate \(y=c_q\), its first contact has u>0 by (12).
The second expression in (18) is then at least u>0;
the other is at least \(\pi/2+v>0\).

The other five gaps are unchanged, and the sum of the two
in (18) is unchanged. Thus the gaps are positive and sum
to \(2\pi\). Actual containment, core avoidance, neighboring
SAT witnesses and canonical boundary states have already
been checked. The boundary-domain bridge therefore applies
to every selected candidate itself, without a connectedness
assumption. Its local two-square band gives each gap greater
than 19/25.

The nearest-axis tie theorem excludes an E diagonal for
either sign. At the original q this follows by the auxiliary
Q argument in Section 2 of the same-radius note: fixed-axis
radial expansion to the core/Q boundaries preserves all
rays, actual weak witnesses and the diagonal, contradicting
the Q-boundary nearest-axis theorem. This is only an auxiliary
contradiction; none of the actual comparison states is taken
from that enlarged circle. The nearest-axis theorem has no
E-sign hypothesis. Thus candidate 4 is impossible.

## 5. The zero-tangent candidate is dominated by an alignment

Suppose candidate 3 has u,v>0 and y=0. Put
\[
 A_q=a_q+1/2,\quad d_q=a_q-1/2=A_q-1,
 \qquad f_q(s)=1/2+\tfrac12\cos s-d_q\sin s.
\tag{19}
\]
Its contact and opposite feasibility give
\[
                              B=f_q(u),\qquad C\ge f_q(v).
\tag{20}
\]
The choice B≥C in (6), not an inequality C≤cq, is what
is needed here. Since fq decreases, (20) gives u≤v and
\(t\ge2u\). Also B≥cq implies u<1/8 by the same exact
Taylor comparison as in the T-pair theorem.

Set
\[
 \delta=1-B=d_q\sin u+(1-\cos u)/2>0,
 \quad\epsilon=A_q-\sqrt{A_q^2-\delta-\delta^2}.
\tag{21}
\]
At the first alignment u'=0 use the actual outer state
\[
                      y'=-\delta=B-1,\qquad a'=a_q-\epsilon.
\tag{22}
\]
It is strictly sorted, since \(\delta\le1-c_q<c_q\), and
its first primary and secondary projections both equal 1.
Its second-primary slack, using C≥fq(v), is at least
\[
 M=\sin t\{d_q(1-\cos u)+\tfrac12\sin u-\epsilon\}
                               -(1-\cos u)\cos t.
\tag{23}
\]
The half-angle calculation in Section 5 of
[the positive T-pair theorem](HAND_G3_POSITIVE_PAIRED_T_PRIMARY_ENDPOINT_REDUCTION.md)
applies without change. For completeness, with
\(z=\tan(u/2)<1/15\), it uses
\[
 L=d_q(1-\cos u)+\tfrac12\sin u-(1-\cos u)\cot(2u),
\]
\[
 L>z/2+2d_qz^2,\quad L<2z/3,\quad
 \delta<2d_qz+z^2<2z,
\]
and the uniform bounds \(1.9<A_q<2\), \(.9<d_q<.915\)
to give
\[
 2A_qL-L^2-\delta-\delta^2
                 >(2-A_q)z+\frac{314}{225}z^2>0.
\tag{24}
\]
Both sides of the resulting radical comparison are positive,
so (24) proves \(\epsilon<L\). As \(2u\le t<\pi/2\), (23)
then gives
\[
 M>(1-\cos u)\{\sin t\cot(2u)-\cos t\}\ge0.
\tag{25}
\]
Thus (22) is a feasible first alignment with strict opposite
slack. Section 4 verifies its actual positive gaps.
The only remaining candidates are the two alignments in (5).
Their tied secondary witnesses are the identical projections
of the respective primary at zero error. This proves the
same-radius endpoint theorem, including all original ties.

## 6. The precise positive-GA interface

Now additionally retain positive GA1 with HG2, either AB
owner, BT2 and arbitrary TD0; keep the usual H,A positive
and B,D negative outer anchors. The G sign is arbitrary.
The other six states and all their errors are fixed by the
construction, so the sole-E endpoint theorems apply whenever
their E-sign hypothesis holds.

At the DE-aligned endpoint in (5), EH1 is the only remaining
E primary. The
[signed EH1 extension](HAND_G5_SOLE_E_POSITIVE_GA_SIGNED_COORDINATE_EXTENSIONS.md)
excludes it for either E sign. At the EH-aligned endpoint,
write y for E's physical signed tangent. Its actual EH0
projection gives
\[
                              a_H+y\ge1.
\tag{26}
\]
Move E on its same outer q circle, at the same aligned frame,
down to
\[
                              y_*=1-a_H.
\tag{27}
\]
This is strictly sorted: \(-.415<y_*<.101<c_q\). Throughout
this motion EH0 stays feasible, and DE3 improves because
\[
 \frac{d}{dy}\{a_D+a(y)\sin t-y\cos t\}
                      \le\sin t-\cos t<0.
\tag{28}
\]
At the new endpoint put
\(\alpha_*=\arctan(y_*/a(y_*))\). Since E is strictly
sorted, \(-\pi/4<\alpha_*<\pi/4\). Its two actual gaps are
\[
 \pi/2+t-\beta_D-\alpha_*>0,\qquad
 \pi/2+\alpha_*-\beta_H>0.
\]
Their sum is unchanged. The five other gaps and all other
states are unchanged, so winding one holds directly.
The endpoint is on its original outer q circle and avoids
the true core; (26)--(28) retain the two actual weak
witnesses. Thus it is an eligible boundary-neighbor cycle
at q. All frames and variations are unchanged. At the new
endpoint EH0 is exact.
If \(a_H\ge1\), then \(y_*\le0\), and the
[DE3/EH0 theorem](HAND_G5_POSITIVE_GA_OUTER_E_SOLE_DE_AND_SECONDARY_EXCLUSION.md),
with its signed-G extension, excludes it as well.

Consequently the only endpoint not excluded by these two
sole-E theorems has the explicit data
\[
 \begin{gathered}
 d_{EH}=0,\qquad d_{DE}=t>0,\qquad
 c_q\le a_H<1,\\
 y_E=1-a_H\in(0,1-c_q)\subset(0,.101),\qquad
 a_H+y_E=1,
 \end{gathered}
\tag{29}
\]
with H and E both on the same outer q circle. No comparison
between aH and aD is asserted in (29). The exceptional sign
is real; the paired-E construction must not silently discard
it or invoke an E-nonpositive theorem there.

For a useful equivalent normalized interface, reflect the
whole physical cycle and reverse its roles as
\[
 (H',G',A',B',T',D',E')=(D,T,B,A,G,H,E).
\tag{30}
\]
Signed tangents and real frames negate; reversed-edge errors
are unchanged. The quarter-owner map is 0↔2, 1↔3. The
zero-edge owners likewise exchange 0 and 2. Thus (29) maps
to the actual owner pattern
\[
 HG2,\quad GA0,\quad AB0\text{ or }AB2,\quad
 BT3\text{ at }x\ge0,\quad TD0,
 \quad DE2\text{ at }0,\quad EH1\text{ at }t>0.
\tag{31}
\]
Here HG,GA,AB,TD have their original arbitrary signed errors,
and
\[
 y_{E'}<0,\qquad b_{E'}=1-a_{D'}\in(0,.101),
 \qquad a_{D'}+b_{E'}=1,
\tag{32}
\]
with D',E' outer at the original q. Both G' and T' may have
either sign or radial kind. Equations (31)--(32) precisely
identify the complementary positive-BT endpoint needed to
close this finite join. This section proves the reduction to that interface. The new
sharp comparison in Section 7 closes it at q<=q*.

All comparisons are exact circle identities, whole-interval
derivative bounds, positive-side squarings and direct physical
gap checks. No sampled minimum, state mesh or optimizer value
is a proof premise. No equality inference is drawn from a
modified intermediate square.


## 7. The sharp positive-GA join is now closed

Assume the additional positive-GA scope of Section 6 with
actual GA error x>0 and q<=q*. At the exceptional endpoint
(29), let e denote the sole remaining DE3 error and put
tau=x+e. The transport preserved the E-primary sum and
the positive variation, so 0<tau<h. The signed G and
arbitrary TD0 data are unchanged.

The [outside-strip theorem](HAND_G5_POSITIVE_GA_EXCEPTIONAL_E_ALIGNED_OUTSIDE_CRITICAL_STRIP.md)
strictly excludes this exact EH contact at Q1 whenever
tau is in [0,.1] or [.16,h]. On the remaining closed strip
[.1,.16], the [critical hard-chain dual](HAND_G5_POSITIVE_GA_EXCEPTIONAL_E_ALIGNED_SHARP_CRITICAL_STRIP.md)
forces x=0 at q<=q*, which contradicts x>0. Thus all
positive-paired-E endpoints are excluded in this positive-GA
scope. The finite all-owner/radial-kind join appears in
[the complete BT2/TD0 entry theorem](HAND_G5_POSITIVE_GA_HG2_BT2_TD0_COMPLETE_EXCLUSION.md).

The radius restriction matters: the critical theorem uses
the exact hard minimum and permits its zero when x=0.
This section asserts neither a strict Q1 exclusion of that
zero nor a positive-GA theorem for an additional T primary.
