# The entire zero-individual-weight boundary of the one-radial all-side C6 is impossible

Date: October 26, 2026.

**Status: accepted complete hand proof and explicit scalar-scope extension
after root and separate independent full-source and physical-scope reviews.**
See REVIEW_C6_ONE_RADIAL_ZERO_WEIGHT_ROOT_2026_10_26.md and
REVIEW_C6_ONE_RADIAL_ZERO_CORNER_WEIGHT_CERTIFICATE_REDUCTION_2026_10_26.md.
For the current nine-square route, every constant-bit row in Section 6
now uses SIX_CYCLE_RADIAL_ZERO_WEIGHT_CONSTANT_ALL_MEANS_EXTENSION.md,
with its fresh complete review
REVIEW_C6_RADIAL_ZERO_WEIGHT_CONSTANT_ALL_MEANS_ROOT_2026_10_26.md.
It derives R<2 from the unchanged physical zero-weight scalar identities
and contradicts R>2 for the same nine squares. The old six-matrix
one-share and six-matrix two-share arguments below remain historical
stronger isolated-core alternatives; they are no longer required by
the current nine-square route, and the same twelve checks are not
counted as a second retirement.
The theorem keeps the original physical two-circle-corner mask. It
does not replace that mask by a physically unique corner or change
either of its two original weights. The extra premise is that one
of those weights already equals zero in the common selected
certificate. Both choices of the zero weight are covered.

Retain the entire original alternating C6 component, its three true
unloaded degree-two side-normal transmitters, all positive pair
forces, every actual application mean, the full physical intersection
types, every transmitter slider, all nine physical unit squares, and

\[
 K_0:=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
 \qquad d=\sqrt{R^2-\frac14}-1.
\tag{1}
\]

Exactly one of its three positively loaded squares, S, has two
physical circle corners. The other two, B and C, have exactly one
physical circle corner each. The original total circle weight of
each loaded square is positive.

**Theorem.** If either original individual circle weight of S is
zero, this physical core is impossible in (1). Consequently every
surviving strictly obtuse one-radial configuration has both of its
original radial corner weights strictly positive.

The proof imports scalar inequalities from the completed all-unique
contact analyses only after deriving every input of those inequalities
for the present physical mask. It does not apply an all-unique
physical theorem to S or invoke a limiting packing. No new finite
coefficient calculation or computational certificate is added.

## 1. The supported actual corner fixes one short incident angle

Reflect the entire original configuration if necessary so that the
corner with positive weight is the upper one in S's radial frame:

\[
 S=[d,d+1]\times[-1/2,1/2],
 \qquad z_S=(d+1,1/2).
\tag{2}
\]

The other physical circle corner remains present and has its original
zero weight. The complete radial support cover in
`RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md`, Section 1, and the
distinct-port torque argument in
`SIX_CYCLE_ZERO_DIAGONAL_TWO_RADIAL_EXCLUSION.md`, Section 1,
give the original two ports and directions from S:

\[
 P_+=(d,1/2),\quad g_+=(-\cos\alpha,\sin\alpha),
\]
\[
 P_-=(d,-1/2),\quad g_-=(-\cos\beta,-\sin\beta),
 \qquad 0<\alpha,\beta<\pi/2.
\tag{3}
\]

Both are strict vertex features of S, so neither of S's two
loaded/transmitter interfaces is genuinely shared. The two actual
ports are the endpoints of S's complete inner side and have distance
one. These assertions are independent of the two weight values.

Let \(a=\tan\alpha\), \(b=\tan\beta\), and \(T=a+b>0\).
Intersecting the two unchanged normal lines gives their actual
concurrence

\[
 q_S=\left(d+\frac1T,\frac{b-a}{2T}\right).
\tag{4}
\]

The actual circle resultant is a positive multiple of the original
corner \(z_S\), since its other original coefficient is zero.
The full force and torque equations therefore put \(q_S\) on the
positive ray through \(z_S\). This is the concurrence conclusion
of `SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md`; no containment of
\(q_S\) is assumed in using it. Substituting (2)--(4) gives

\[
 (d+1)(b-a)=d(a+b)+1,
                 \qquad b-(2d+1)a=1.
\tag{5}
\]

In particular \(b>1\), so \(\beta>\pi/4\), and

\[
 T=1+2(d+1)a>1,
 \qquad d<(q_S)_x<d+1,
 \qquad 0<(q_S)_y<1/2.
\tag{6}
\]

Thus this particular physical mask boundary does have concurrence
strictly inside S. This conclusion follows from its actual zero
weight; it is not asserted for an arbitrary radial weight split.

The two physically unique loads satisfy the full local upper-turn
theorem in Section 1 of
`SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md`:
\(\theta_B,\theta_C\le3\pi/4\). Its proof has no diagonal
premise. The true turn sum is \(2\pi\), so the actual radial
turn obeys

\[
 \theta_S=\pi-\alpha-\beta\ge\pi/2,
                    \qquad \alpha+\beta\le\pi/2.
\tag{7}
\]

Consequently \(ab\le1\). The exact window bound \(d>9/10\)
and (5) give

\[
                    1\ge ab=a+(2d+1)a^2
                              >a+\frac{14}{5}a^2.
\tag{8}
\]

If \(\alpha\ge12/25\), then \(a=\tan\alpha\ge\alpha
\ge12/25\), and the increasing polynomial on the right of (8)
is at least

\[
 \frac{12}{25}+\frac{14}{5}\left(\frac{12}{25}\right)^2
                         =\frac{3516}{3125}>1,
\tag{9}
\]

a contradiction. We have therefore proved the following intrinsic
feature, including both choices of the originally zero corner:

**Short supported-corner port.** At the inner vertex of S adjacent
to its original positive-weight circle corner, the incident channel
makes an angle strictly smaller than \(12/25\) with the inward
radial direction.

The frame in (2) merely expresses this unchanged supported corner
as the upper one. It does not select a different corner after the
certificate is fixed.

## 2. Every actual turn is strict and every loaded chord is on one side

Since \(\beta>\pi/4\), equations (3) and (7) also give
\(\theta_S<3\pi/4\). The turn sum and the two unique upper
bounds consequently imply

\[
                       \theta_B,\theta_C>\pi/2.
\tag{10}
\]

If \(\theta_S=\pi/2\), the complete actual endpoint
classification in
`SIX_CYCLE_ONE_RADIAL_RIGHT_TURN_CLASSIFICATION.md`, Sections
1--4, forces \(\alpha=\beta=\pi/4\), independently of the
radial weights. Equation (5) would then read \(-2d=1\),
contrary to \(d>0\). Thus this mask boundary cannot have the
right-turn endpoint even as a six-body core. We obtain

\[
 \pi/2<\theta_i\le3\pi/4\quad(i=S,B,C),
                        \sum_i\theta_i=2\pi.
\tag{11}
\]

The full unique-loaded feature cover, applied locally at B and C
using (10), places their two distinct original applications on one
inner side, with at least one a vertex and at most one genuine share
at each. The strict-turn distinctness argument in
`SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md`,
Section 5, includes every shared-side endpoint and keeps the two
actual transmitters. At S the corresponding statement is already
the explicit strict-inner-vertex statement (3). No all-unique global
turn theorem has been used for S.

## 3. The exact selected-corner scalar model remains valid

Use the true counterclockwise loaded order. Write the actual channel
forces and circle resultants as

\[
 f_i=\mu_i n_i,\qquad \mu_i>0,\quad |n_i|=1,
 \qquad F_i=f_{i-1}-f_i,\qquad D_i=|F_i|>0.
\tag{12}
\]

At B,C choose their actual unique circle corners. At S use exactly
the original positive-weight corner fixed above. For all three
these real corners now satisfy

\[
                             z_i=R F_i/D_i.
\tag{13}
\]

This is an identity of the original circle forces. The second
physical corner of S, its zero weight, and its occupied square
have not been removed.

Write each directed actual inner side as
\(b_i+[0,1]u_i\), with inward normal \(v_i=-Ju_i\). Then

\[
 z_i=b_i+\chi_i u_i+v_i,\qquad \chi_i\in\{0,1\},
\]
\[
 p_i^-=b_i+t_i^-u_i,\qquad
 p_i^+=b_i+t_i^+u_i,\qquad
 0\le t_i^-<t_i^+\le1,
 \quad\ell_i=t_i^+-t_i^-.
\tag{14}
\]

At a nonshared unit the two actual ports are vertices, so
\((t_i^-,t_i^+)=(0,1)\). This holds in particular at S.
At B or C every actual shared mean has the original torque formula
of `SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md`, Section 3:

| Genuine share | Corner bit and direction | Exact chord and mean endpoints |
| --- | --- | --- |
| Outgoing | \(\chi_i=1,\ u_i=-Jn_i\) | \(\ell_i=1-(\mu_{i-1}/\mu_i)(\sin\theta_i+\cos\theta_i)\), \((t_i^-,t_i^+)=(0,\ell_i)\) |
| Incoming | \(\chi_i=0,\ u_i=Jn_{i-1}\) | \(\ell_i=1-(\mu_i/\mu_{i-1})(\sin\theta_i+\cos\theta_i)\), \((t_i^-,t_i^+)=(1-\ell_i,1)\) |

Every genuine endpoint mean \(\ell_i=1\) remains included. No
such formula is imposed on a physically radial shared interface:
S has no shared interface by (3).

Define, exactly as in the support-functional derivation,

\[
 K_i=(\chi_i-t_i^-)f_{i-1}+(t_i^+-\chi_i)f_i,
 \qquad g_i=K_i+JF_i,
 \qquad E_i=|g_i|.
\tag{15}
\]

The true torque about the chosen corner gives \(u_i\parallel
g_i\). Its sign is positive: the identity from actual supports is

\[
 u_i\cdot g_i
   =H_i(f_{i-1})+H_i(f_i)+H_i(F_i)>0,
\tag{16}
\]

where \(H_i\) is the centered support halfwidth of the original
square. To justify the last summand also at S, its selected corner
maximizes \(F_i\), because \(F_i\) is a positive multiple of
that far circle corner. Each own-axis corner coordinate is at least
one half and hence positive. The second physical circle corner does
not affect that support identity. Thus \(u_i=g_i/E_i\), and
\(E_i>0\).

The three actual transmitter equations and summation by parts give
the same exact closure and radius identities:

\[
 p_{i+1}^- -p_i^+=n_i,\qquad
             \sum_i(n_i+\ell_i u_i)=0,
\]
\[
                   R\sum_iD_i=\sum_i\mu_i+\sum_iE_i.
\tag{17}
\]

In the second line use (13) before summation by parts. It would
not be valid in this form for a general positive split between S's
two corners; its validity here comes from the given zero coefficient.
Equations (11)--(17), with their actual means, are precisely the
inputs of the scalar arguments used below.

## 4. The only additional corner input has a strict weak-mask replacement

Containment of the two vertices adjacent to every selected \(z_i\)
gives

\[
              z_i\cdot v_i\ge1/2,
       \qquad(2\chi_i-1)z_i\cdot u_i\ge1/2.
\tag{18}
\]

These inequalities are strict at B and C, but only weak is claimed
at S. In particular one actual equality at S has not been suppressed.

The constant-one-share proof and one mixed-two-share force branch
need the uniform nonshared force ratio below. It remains **strict**
under (18). For a nonshared unit write

\[
 a=\mu_{i-1}>0,\quad b=\mu_i>0,
 \quad s=\sin\theta_i>0,\quad c=\cos\theta_i<0,
 \quad h=s-c,
\]
\[
 D^2=a^2+b^2-2ab c.
\]

When \(\chi_i=1\), the exact nonshared norm and dot product in
(15) give

\[
 E^2=2a^2+b^2+2ab h,
 \qquad F_i\cdot u_i=\frac{a(a-bc)}E.
\tag{19}
\]

The weak second inequality in (18) yields
\(ED\le2Ra(a-bc)\). But

\[
                    E^2-D^2=a^2+2ab s>0,
\tag{20}
\]

so \(ED>D^2\). Put \(x=b/a\) and \(k=-c\). The
combined inequalities are therefore still strict:

\[
                       x^2<(2R-2)kx+2R-1.
\tag{21}
\]

For \(\chi_i=0\), interchange a,b: the same proof uses
\(E^2-D^2=b^2+2ab s>0\), with \(x=a/b\).
Using \(R<133/64\) and \(k\le1/\sqrt2<99/140\),
equation (21) implies

\[
                  x^2-\frac{6831}{4480}x-\frac{101}{32}<0.
\tag{22}
\]

The polynomial is strictly increasing for \(x\ge27/10\) and
its value at that endpoint is \(151/8960>0\). Thus for every
actual nonshared unit, including S,

\[
 \chi_i=1\Longrightarrow\frac{\mu_i}{\mu_{i-1}}<\frac{27}{10},
 \qquad
 \chi_i=0\Longrightarrow\frac{\mu_{i-1}}{\mu_i}<\frac{27}{10}.
\tag{23}
\]

This proves the necessary replacement directly; it is not a continuity
argument from physically unique masks. The scalar proofs below use
no other strict corner inequality at a nonshared unit. Every shared
unit is one of B,C and remains physically unique throughout.

## 5. Complete contact count and the doubly shared channel

At B,C there is at most one genuine share each, and there is none
at S. Consequently there are zero, one, or two genuine shared
interfaces. Three-share and higher-share possibilities are already
impossible by the actual support and strict-turn features. No
three-share scalar theorem is needed for this mask boundary.

If a transmitter were shared at both ends, its two endpoints would
have to be B and C. The geometric Sections 1--2 of
`SIX_CYCLE_DOUBLE_SHARED_CHANNEL_EXCLUSION.md` apply to these two
physically unique endpoints and to the already established actual
same-side ports and turns at the third square S. They do not yet
use the third square's circle-corner coordinates or its circle mask.
Here is the particular contradiction they give.

Normalize that actual shared channel horizontally with reserve one.
Its far-circle horizontal coordinates satisfy \(a+c=3\).
The other original directions from B,C toward S have angles
\(\eta_B,\eta_C\in[\pi/4,\pi/2)\), with
\(\pi/2<\eta_B+\eta_C\le3\pi/4\). Their two true
applications P,Q on S have positive horizontal difference

\[
          0<\Delta_x=1-\cos\eta_B-\cos\eta_C
                                      <1-1/\sqrt2.
\tag{24}
\]

Their directed side angle \(\phi\) satisfies
\(|\phi|\le\pi/4\), by the two actual support inequalities.
Therefore their actual chord satisfies

\[
                      |Q-P|=\frac{\Delta_x}{\cos\phi}
                                   <\sqrt2-1<1.
\tag{25}
\]

The complete angle proof of the strict upper bound in (24) is the
sum-to-product estimate in that source, Section 2, including the
\(\pi/4\) endpoints. But the two original radial ports (3) have
distance exactly one. This is an immediate contradiction. In
particular no third-share conclusion at an artificially unique S
is needed, and neither historical coefficient packet of the
double-shared analysis is imported.

Thus two genuine shares, when present, form a matching. The cyclic
relabeling and reflection-plus-cycle-reversal operations preserve all
physical squares and the original supported corner. In the directed
side chart they act by

\[
                              \chi'_i=1-\chi_{-i}.
\tag{26}
\]

The mean-preserving proof of (26) in
`SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md` uses
only (14). It applies here without changing which original S
corner has positive weight. Consequently the same finite covers
give the two constant/mixed zero-share types, the four one-share
orbits, and the three matching two-share orbits.

## 6. Original scalar cover and historical stronger dependency table

The current nine-square proof replaces all constant-bit rows of the
table by SIX_CYCLE_RADIAL_ZERO_WEIGHT_CONSTANT_ALL_MEANS_EXTENSION.md.
Its inputs (11)--(17) are proved above for this actual physical radial
endpoint; stationarity of the common convex functional gives R<2,
contrary to the global R>2 theorem for the same nine squares. The
mixed-bit rows and the finite contact cover are unchanged. The table
records the older stronger isolated-core scalar alternatives in full.

The following table states the scalar input used in each row and
locates the physically radial square in every possible canonical
placement. The all-unique geometric hypotheses in the original
titles are not being asserted here: equations (11)--(17) and, where
needed, the replacement (23) supply the scalar premises directly.

| Contact count and canonical type | Possible radial positions | Actual scalar contradiction reused | Strict physical corner input used in that scalar argument |
| --- | --- | --- | --- |
| Zero shares, mixed bits | Any of the three nonshared units | `SIX_CYCLE_ALTERNATING_UNIQUE_SINGLETON_EXCLUSION.md`, Section 4: strict vertical closure projection | None after the strict-turn, unit-chord and torque equations; supplied by (11)--(17) |
| Zero shares, constant bits | Any of the three nonshared units | Same source, Sections 5 and the cited complete triangle-square-corner Fermat inequality | None after the actual norm model, closure and radius identity; supplied by (11)--(17) |
| One share, constant 111, share 0 | Unit 1 or 2 | `SIX_CYCLE_CONSTANT_CHI_ONE_SHARE_EXCLUSION.md`, Sections 2--6 | Only the nonshared unit-1 bound \(\mu_1/\mu_0<27/10\); equation (23) supplies it even if unit 1 is radial |
| One share, mixed 110, share 1 | Unit 0 or 2 | `SIX_CYCLE_MIXED_ONE_SHARE_MIDDLE_EXCLUSION.md`, or the shorter `SIX_CYCLE_MIXED_ONE_SHARE_1_CLOSURE_EXCLUSION.md`: strict vertical closure projection | None after the original share formula and strict turns |
| One share, mixed 110, share 2 | Unit 0 or 1 | `SIX_CYCLE_MIXED_ONE_SHARE_2_CLOSURE_EXCLUSION.md`: strict diagonal closure projection | None after the original share formula and strict turns |
| Two shares, constant 111, shares 0/1 | Unit 2 | `SIX_CYCLE_CONSTANT_CHI_TWO_SHARE_EXCLUSION.md`: one closure restriction and its full force-gap inequality | No corner inequality after the norm, mean, closure and radius formulas |
| Two shares, mixed 110, shares 0/1 | Unit 2 | `SIX_CYCLE_MIXED_01_COMPLETE_EXCLUSION.md` and its complete closure, Cauchy, monotonicity and endpoint join | No corner inequality; the force lower bound and angle restrictions are derived from actual closure |
| Two shares, mixed 110, shares 0/2, \(q\ge p\) | Unit 1 | `SIX_CYCLE_MIXED_02_SMALL_FORCE_BRANCH_ANALYTIC.md`: full closure and radius-gap proof | No corner inequality after the norm, mean, closure and radius formulas |
| Two shares, mixed 110, shares 0/2, \(q<p\) | Unit 1 | `SIX_CYCLE_MIXED_02_LARGE_FORCE_BRANCH_ANALYTIC.md`: full closure contradiction | Only the nonshared unit-1 bound \(p<27/10\), supplied by (23) for the actual radial unit |

Each scalar radius contradiction is strict and holds for the complete
displayed positive force and angle domain. The zero-share mixed
projection also includes its strict endpoint argument from positive
forces. The constant zero-share Fermat bound applies to the actual
force triangle because all its turns are in (11), putting the origin
inside that triangle; its derived-corner formulas are exactly (15)
with the constant bit.

For the historical one-share constant row, the same \(p<27/10\) replacement
also supplies the strict lower estimate on the middle side direction
used to derive that source's single angle triangle. Its six existing
rational control matrices are unchanged. The constant two-share row
uses its own six existing matrices, again unchanged. All other rows
are the already completed analytic scalar inequalities. There is no
new matrix, new angle subdivision, force-ratio mesh, or coefficient
certificate in that historical extension. The present current
nine-square route uses neither set of six matrices: its explicit
all-means extension above replaces both at once, keeping the global
five-charge certificate as one shared dependency.

No row uses the strict shared-unit force-ratio bound
\(\sqrt{1041}/8\) at S: S is never a shared unit. No hidden
weak-to-strict replacement of \(z_S\cdot u\ge1/2\) or
\(z_S\cdot v\ge1/2\) is made; (19)--(23) give the only
strict consequence that is needed. The original shared means,
including \(\ell_i=1\), enter every row through their exact
formulas in Section 3.

The complete zero-, one- and two-share cover therefore leaves only
the canonical mixed one-share type

\[
 \chi=(1,1,0),\qquad S_0W_0\text{ the sole genuine share}.
\tag{27}
\]

This is exactly the finite contact residue identified in
`SIX_CYCLE_ONE_SHARE_FULL_ORBIT_COVER_AND_RESIDUE.md`.
Its further numerical or completion restrictions are not used here.

## 7. Both possible radial placements in the residue contradict the short-port lemma

The actual radial square cannot be unit 0 in (27), because that
unit has a genuine shared interface. Thus it is unit 1 or unit 2.
Both are nonshared and have the original full side chord one.

If S is unit 1, its selected corner has bit \(\chi_1=1\).
Equation (14) gives

\[
 z_S=p_1^++v_1,
 \qquad z_2=p_2^-+v_2.
\tag{28}
\]

Thus the outgoing channel \(S_1-W_1-S_2\) starts at the
actual inner vertex of S adjacent to its original positive-weight
circle corner, and ends at an actual vertex of the physically unique
unit 2 adjacent to that unit's actual circle corner. Both distances
in (28) equal one.

If S is unit 2, its selected corner has bit \(\chi_2=0\).
The same two identities (28), with unit 1 now physically unique and
unit 2 radial, show that the incoming channel \(S_1-W_1-S_2\)
has exactly the same intrinsic property: at S it uses the vertex
adjacent to the original supported corner, and at the other unit
it uses the vertex adjacent to its actual unique circle corner.

Use the actual global reflection permitted in the local radial
channel lemma to express this particular supported-corner port as
the upper port in (3). Its angle is therefore the \(\alpha\)
of Section 1 and satisfies \(\alpha<12/25\). But its other
actual application Q and circle corner z satisfy \(|z-Q|=1\).
The complete local theorem in
`SIX_CYCLE_RADIAL_INCIDENT_NEAR_CORNER_ANGLE_BOUND.md`,
Sections 1--2, applies to this unchanged channel and gives
\(\alpha>12/25\). Its proof uses physical circle contact,
not positive weight at every physical corner, and does not assume
an interior radial concurrence.

This contradiction excludes both possible radial placements in
(27), including all their mean-preserving symmetry images. No
corner was freshly chosen: (28) refers throughout to the unique
original supported circle corner of S and its carried image under
(26).

## 8. Full scope of the concluded exclusion

The actual support cover, the zero/right-turn checks, the no-share
property at S, the at-most-one-share statements at B,C, and the
double-shared-channel contradiction exhaust the original contact
features. Section 6 covers every remaining scalar orbit, except the
single residue excluded in Section 7. Both original individual
zero-weight endpoints of the radial mask are consequently impossible
throughout (1), without a condition on any transmitter slider or
extra-square placement.

All nine actual squares and all genuine mean endpoints remain. The
core contradiction removes this entire boundary of the physical
one-radial weight domain. It leaves the radial mask with two
strictly positive individual weights as a separate full obligation;
neither the whole one-radial gate nor the global sharp inequality,
equality classification or prior prerequisite-chain audit is declared
closed. No original roadmap count is increased by this subfamily
statement. No Lean compilation, CI, physical perturbation, sampled
configuration, or new computational certificate is used.
