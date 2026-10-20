# The entire aligned hard-quarter class has the sharp lower bound

## 1. A five-anchor statement with no mismatch hypothesis

Put

\[
 Q=9789/2500,\qquad Q_1=1957767069/500000000.
\]

Let the five anchors A, B, D, E and H have nonnegative sorted
own-frame coordinates satisfying

\[
 a_i\ge b_i\ge0,\qquad
 (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q.
\tag{1}
\]

Take angles

\[
 t,u,\delta,\epsilon\ge0,\qquad
 t+u=\delta+\epsilon=\alpha\le7/10,
\tag{2}
\]

and write `W(z)=(1+cos z+sin z)/2` on this interval.
Assume the five actual inequalities

\[
\begin{aligned}
 b_H+a_A\cos t-b_A\sin t&\ge1+W(t),\\
 b_A+b_B&\ge1,\\
 a_B\cos u-b_B\sin u+b_D&\ge1+W(u),\\
 a_D+a_E\sin\delta+b_E\cos\delta&\ge W(\delta),\\
 a_H+a_E\sin\epsilon-b_E\cos\epsilon&\ge W(\epsilon).
\end{aligned}
\tag{3}
\]

These are precisely the necessary five-anchor inequalities obtained
from the aligned HG, AB and TD edges and the original GA0, BT2,
DE3 and EH1 witnesses. The shared G and T coordinates have already
canceled in the first and third lines. They need not be supplied as
additional centers for this theorem.

Let `(q_*,u_*,t_*)` be the unique stationary zero constructed in
`HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md`. In particular

\[
                  3.9154<q_*<Q_1<Q.
\tag{4}
\]

**Sharp branch theorem.** Every system (1)--(3) satisfies

\[
                              q\ge q_*.
\tag{5}
\]

At `q=q_*`, it has `u=delta=0`, `t=epsilon=t_*`, and exactly
the five stationary anchor coordinates. No bound on `u+delta`,
or on an earlier mismatch, is an input. The sign convention for E
in (3) is the normalized nonpositive signed tangent.

This is a complete continuous theorem for the explicitly stated
hard-quarter class. It is not a claim that every unrestricted
candidate has its signs, owners, frame order or aligned zero edges.

## 2. Domain bounds and reductions retain the same anchors

The A/B cap argument in Sections 2--3 of
`HAND_G4_E_INTERIOR_BOUNDARY_REDUCTION.md` uses only the first
three lines of (3) and the five circle bounds. Thus it gives

\[
 0<\alpha<11/50,\qquad .335<b_A,b_B<.665,
 \qquad a_H+a_D<1.9968-.718\sin\alpha<2.
\tag{6}
\]

The zero-span endpoint is excluded by the last two lines of (3),
which would imply `a_H+a_D>=2` there.

The E-zero theorem
`HAND_G5_E_ZERO_HARD_QUARTER_SPLIT_EXCLUSION.md` also applies to
(3) directly. Its proof first cancels G and T and thereafter uses
only the five inequalities printed here. In particular

\[
                              b_E>0.
\tag{7}
\]

Similarly `HAND_G5_ALIGNED_HARD_EPSILON_ZERO_EXCLUSION.md`
excludes the entire `epsilon=0` branch of this five-anchor system,
so

\[
                              \epsilon>0.
\tag{8}
\]

Both exclusions are proved already at Q and therefore hold at
every q in (1). They use neither a later tilt window nor a radius
lower bound.

## 3. Move only E to an orientation endpoint

Fix A, B, D and H and all four angles determining their frames.
Among the auxiliary E states with `a>=b>=0`,
`delta+epsilon=alpha`, and the last two inequalities of (3),
minimize the E corner value. The original E state is feasible,
so the minimum is at most its original value and in particular
at most q.

The boundary-reduction theorem in
`HAND_G4_E_INTERIOR_BOUNDARY_REDUCTION.md` proves that such a
minimum has

\[
                 b_E=0,\qquad\delta=0,
                              \text{or}\quad\epsilon=0.
\]

The unchanged first three inequalities of (3) exclude the first
and third alternatives by (7)--(8). Therefore there is a
five-anchor descendant, still satisfying (1)--(3) at the same q,
with

\[
                           \delta=0,\qquad\epsilon=\alpha.
\tag{9}
\]

A, B, D and H are unchanged. If the original delta was positive,
then (7)--(8) put the original E strictly inside the orientation
and sign interval. The proof of the E-boundary theorem rules out
every interior minimum. The minimum E corner value is therefore
**strictly smaller** than the original E corner value in this case.

No bad-mismatch condition is imposed during this reduction. The
retained quantities are q, the four other anchors, their frames,
the total span alpha, and the five inequalities (3).

## 4. Move the A/B common frame to a split endpoint

Now keep H, D and the selected E fixed, including (9). The
full-feasible-cap theorem in
`HAND_G5_HARD_SPLIT_CONVEXITY_FULL_FEASIBLE_CAP_RANGE.md`
applies separately to the two composite paths in (3), with

\[
                  D_A=3/2-b_H,\qquad D_B=3/2-b_D.
\tag{10}
\]

Both parameters exceed `3/5`, since the sorted circles give
`b_H,b_D<.9`. The first and third inequalities of (3) give
`a_A>=2-b_H` and `a_B>=2-b_D`. Thus their actual corner values
`q_A,q_B`, respectively, satisfy

\[
 q_A\ge(D_A+1)^2+1/4,
 \qquad q_B\ge(D_B+1)^2+1/4.
\tag{11}
\]

Use these separate radii in the two cap functions

\[
 L_i(z)=\cos z\sqrt{q_i-(D_i+\cos z)^2}
                      -\sin z(D_i+\cos z).
\tag{12}
\]

The scalar theorem gives strict convexity on the full interval
for each cap. The actual AB constraint yields

\[
 2\le L_A(t)+L_B(u)
 \le\max\{L_A(0)+L_B(\alpha),\ L_A(\alpha)+L_B(0)\}.
\tag{13}
\]

The maximizing endpoint constructs new A and B at respective
corner values no larger than `q_A,q_B`. Their sorted coordinates,
the first three inequalities of (3), and the common circle ceiling
q remain valid. H, D and E are unchanged. In particular any
strict circle slack already present at A, B or E is preserved.

If `t,u>0`, strict convexity makes the last comparison in (13)
strict. Continuity then permits decreasing both A/B corner
ceilings a little while retaining the two hard contacts and AB.
Consequently both new A/B corner values can be made strictly
smaller than their respective original values.

The endpoint `t=0,u=alpha`, together with (9), is excluded by
`HAND_G5_ALIGNED_GA_DE_ENDPOINT_EXCLUSION.md`. Its statement
explicitly includes the five-anchor system with G/T omitted.
Therefore every surviving descendant satisfies

\[
                  u=\delta=0,\qquad t=\epsilon=\alpha.
\tag{14}
\]

## 5. The zero-error sharp stress needs only these five anchors

We record the precise downstream statement to avoid importing
unnecessary geometric hypotheses about omitted sliders. In the
case (14), (3) reads

\[
\begin{gathered}
 c a_A-s b_A+b_H\ge1+W,\qquad b_A+b_B\ge1,\\
 a_B+b_D\ge2,\qquad a_D+b_E\ge1,\\
 a_H+s a_E-c b_E\ge W,
\end{gathered}
\tag{15}
\]

where `s=sin(alpha)`, `c=cos(alpha)`.

Suppose first that `q<=Q1`; this includes every potential
counterexample to (5) and its equality case. The explicit
five-circle nominal stress in `HAND_POSITIVE_TILT_NOMINAL_GAP.md`
applies to (15) directly. Its collection of the G/T-free forces
is exactly the collection of these five inequalities. The
whole-interval bounds proved there and used in
`HAND_OWNER_GAUGE_POSITIVE_TILT_AT_THREE_TWO_HUNDREDTHS.md`
are

\[
 g(q,s)>0\quad\text{if}\quad
 0\le s\le1/10\quad\text{or}\quad79/500\le s\le3/10.
\tag{16}
\]

But (15) and the five circle bounds imply `g(q,s)<=0`.
Equation (6) puts `s<.22<.3`, so (16) forces

\[
                            1/10<\alpha<4/25.
\tag{17}
\]

The conversion follows from `sin(alpha)<=alpha` and
`sin(.16)>=.16-.16^3/6>.158`. At zero the E force and mass
vanish and its circle is simply omitted, as specified in the
nominal stress proof. No core, tangent, physical-gap or slider
bound is needed for this nominal implication.

## 6. Complete the five actual circles

At radius `q_*` and tilt `alpha` in (17), use the unique
stationary position `v_0=u(q_*,alpha)` from
`HAND_STATIONARY_POSITION_AND_SLIDER_BOUNDS.md`. To distinguish
this position from the frame split u, write

\[
\begin{gathered}
 r=\sqrt{q_*-v_0^2},\quad l=2-v_0,
 \quad U_0=\sqrt{q_*-l^2},\quad V=3-U_0,\\
 Y=\sqrt{q_*-V^2},\quad v=2-Y,
 \quad w=\sqrt{q_*-v^2},\\
 k_1=2-c(r-1)+s v_0,\qquad
 k_2=1+c v-s(w-1).
\end{gathered}
\tag{18}
\]

Define the comparison corner vectors in the five own frames by

\[
 C_A^*=(r,v_0),\quad C_B^*=(U_0,l),\quad
 C_D^*=(Y,V),\quad C_E^*=(w,v),\quad C_H^*=(k_2,k_1).
\tag{19}
\]

The first four have squared norm `q_*`; H has squared norm
`q_*+M(q_*,alpha)`. The stationary theorem gives

\[
 M(q_*,\alpha)\ge0,
 \qquad M(q_*,\alpha)=0\ \Longleftrightarrow\ \alpha=t_*.
\tag{20}
\]

Here are the exact equilibrium weights used by the earlier sharp
terminal, now applied directly to (15). Put

\[
 a_0=s+c v_0/r,\qquad b_0=a_0U_0/l,\qquad e_0=k_2/k_1,
\]

\[
 A_0=c/(2r),\quad B_0=a_0/(2l),\quad
 D_0=b_0/(2V),\quad E_0=s e_0/(2w),\quad H_0=1/(2k_1),
\]

\[
 \omega=(A_0+B_0+D_0+E_0+H_0)^{-1},
 \qquad (\mu_A,\mu_B,\mu_D,\mu_E,\mu_H)
       =\omega(A_0,B_0,D_0,E_0,H_0).
\tag{21}
\]

All masses are positive and sum to one. Give the five inequalities
in (15) the respective positive weights

\[
              \omega,\quad\omega a_0,\quad
              \omega b_0,\quad\omega b_0Y/V,\quad\omega e_0.
\tag{22}
\]

Their collected forces on `(a_i,b_i)` are exactly `2mu_i C_i^*`.
For E, the needed identity is the actual position stationarity
equation

\[
                  b_0Y/V=e_0(c+s v/w).
\]

The other four identities follow directly from (18)--(22).
The comparison centers `C_i^*-(1/2,1/2)` make every inequality
in (15) an equality. Hence, writing
`C_i=(a_i+1/2,b_i+1/2)` for the unchanged descendant corners,
the nonnegative weighted separation gaps give

\[
                 \sum_i2\mu_i C_i^*\cdot(C_i-C_i^*)\ge0.
\tag{23}
\]

Expanding five squared distances and using (1), (19)--(23) now
gives the full nominal sharp bound

\[
\begin{split}
 q&\ge\sum_i\mu_i|C_i|^2\\
  &\ge q_*+\mu_H M(q_*,\alpha)
                   +\sum_i\mu_i|C_i-C_i^*|^2
  \ge q_*.
\end{split}
\tag{24}
\]

This derivation includes every premise used by the zero-error
terminal. It requires only (15) and the five circle bounds.
In particular a constructed G or T, nonneighbor disjointness,
core geometry and an original small-mismatch bound have not
been smuggled into the reduction.

## 7. Finish the lower bound and recover original-anchor equality

If `q<q_*`, then `q<Q1`. Sections 3--4 produce a descendant
at the same circle ceiling q satisfying (14)--(15). Equation
(24) contradicts `q<q_*`, proving (5).

Suppose instead `q=q_*`. For every descendant in (24), equality
forces `alpha=t_*`, all five differences `C_i-C_i^*` to vanish,
and every one of its five actual corner values to equal q_*.

If the original delta were positive, Section 3 would produce a
strictly smaller E corner. Section 4 keeps that E fixed, so
(24) would be impossible. Thus the original `delta=0`.
The original `epsilon=0` and E-zero cases were already excluded.

If the original t and u were both positive, the separate-ceiling
split in Section 4 would strictly lower both A/B corners, again
contradicting (24). The original `t=0,delta=0` endpoint is
excluded by its whole-arc stress. Therefore the original `u=0`.

The original five anchors now themselves satisfy (14)--(15).
Reapply (24) to those original anchors. This fixes their own
corner vectors to (19) at the unique tilt `t_*`, without
identifying original centers with moved descendants.

The converse for these five anchors follows directly from the
stationary construction. When they belong to an original packing,
the unchanged G/T sliders and central square are subject to the
actual remaining packing inequalities; the complete weak
five-parameter equality-family theorem then applies.

## 8. Original ordered candidates with the canceling outer owners

Combine this theorem with
`HAND_G4_SIGNED_THREE_ZERO_REDUCTION_FOR_CANCELING_OUTER_OWNERS.md`.
Every original candidate with that note's six transverse signs,
normalized E sign, real-frame order and retained original axes has
`q>=q_*`, without any mismatch hypothesis and without assuming its
three zero edges were aligned originally.

Indeed, if necessary first enlarge a ceiling below `q_L=19577/5000`
to q_L, without moving any square. Since `q_L<q_*`, a lower-bound
counterexample would still be a counterexample at this ceiling.
The three-zero theorem then supplies precisely (1)--(3), preserving
H, D and E and using the actual ceiling for the new A/B corners.
The sharp branch theorem excludes every ceiling below q_*.

At `q=q_*`, any nonzero original HG, AB or TD frame difference
would leave a strict A or B corner loss after the three-zero
reduction. Sections 3--4 preserve that loss, including through
the separate A/B circle ceilings. It contradicts (24). Hence all
three original zero differences vanish. The original five anchors
themselves now satisfy (1)--(3), so the equality conclusion of
Section 7 applies to them: `u=delta=0`, `t=epsilon=t_*`, and all
five anchors have the stationary coordinates. When these are
original packing centers, the full weak five-parameter equality
classification and its converse apply as above.

Thus the entire stated ordered, canceling-owner class is closed
for both the lower bound and equality. Its original sign, owner
and order assumptions remain explicit; no deformation is asserted
to preserve omitted packing conditions.

## 9. Integration boundary

This proof replaces a mismatch estimate by two explicit
radius-preserving reductions on the full aligned hard-quarter
class. Every noncanonical orientation lost at equality leaves
strict slack in a particular anchor circle, and that slack is
preserved until the nominal sharp identity is applied.

The original-center sign, owner and frame-order capture needed
to reach (1)--(3) is still a separate problem. The signed
three-zero reduction in
`HAND_G4_SIGNED_THREE_ZERO_REDUCTION_FOR_CANCELING_OUTER_OWNERS.md`
supplies the complete original-candidate corollary in Section 8. Its
HG2/TD0 owner and ordering hypotheses must be supplied before
it can be used for an unrestricted candidate. This note does
not label that missing global reduction as proved.

No state table, mesh, sampled minimum, external acceptance result,
Lean compilation, or CI result is part of this argument.
