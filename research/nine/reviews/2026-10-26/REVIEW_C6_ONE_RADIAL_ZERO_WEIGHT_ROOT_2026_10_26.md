# Root review: complete one-radial zero-individual-weight boundary exclusion

Date: October 26, 2026.

**Result: PASS for both original zero-individual-weight endpoints of
the physical one-radial all-side C6, with its two-corner mask retained.**
This does not close the full one-radial gate.

I independently read SIX_CYCLE_ONE_RADIAL_ZERO_CORNER_WEIGHT_EXCLUSION.md,
checked its local radial and unique-turn prerequisites, reread the
geometric double-shared-channel argument and the singleton scalar
entry points, and checked each row against the previously reviewed
constant/mixed shared scalar sources. The new scope extension is
explicit; an all-unique physical theorem is never simply assigned
to the radial square.

## 1. The originally supported radial corner is fixed throughout

When one original radial corner coefficient is zero and the total
load is positive, the other original coefficient is positive. A
global reflection places that actual supported corner at (d+1,1/2)
without changing either weight or the occupied square. The strict
radial support cover and torque signs retain exactly the two inner
vertex applications, with distinct normals and no genuine share at S.

The intersection of their actual normal lines is

\[
 q_S=(d+1/(a+b),(b-a)/(2(a+b))),
 \quad a=\tan\alpha,\ b=\tan\beta.
\]

The unchanged force and torque make it collinear with the supported
corner. The positive horizontal coordinate selects the positive ray.
This gives b-(2d+1)a=1 exactly. In particular b>1 and
a+b=1+2(d+1)a>1; the concurrence is proved strictly inside S.
No such assertion is made for an arbitrary two-positive-weight split.

The full local unique upper-turn theorem bounds the other two turns
by 135 degrees. The exact turn sum then gives alpha+beta<=pi/2,
so ab<=1. With d>9/10, the actual zero-weight equation would give
ab>3516/3125 if alpha>=12/25. Thus the original port adjacent to
the supported corner has alpha<12/25 on the entire endpoint domain.

## 2. The required strict-turn normal form is established directly

Since beta>pi/4, the radial turn is below 135 degrees, forcing
both unique turns above 90 degrees. The possible radial right
turn is eliminated by the accepted complete actual right-turn
classification: its alpha=beta=pi/4 contradicts the unchanged
zero-weight equation. Thus all three turns lie in (90,135].

At B,C the complete local feature cover now gives their distinct
same-inner-side applications and at most one genuine share. At S
the chord is the full unit inner side. Every original mean endpoint
is included. The selected circle corner at S is the original
supported one, while its second physical circle corner remains.

## 3. The scalar model has the same actual equations

At the supported radial corner, just as at B,C, the actual circle
force gives z_i=RF_i/|F_i|. It also maximizes its force direction
on the original square: its inward own-axis coordinates are positive,
including the one equal to 1/2. Therefore the centered-support
identity makes u_i dot(K_i+JF_i)>0, and the original torque gives
u_i=(K_i+JF_i)/E_i with the positive sign.

The actual side channels yield unchanged closure and virial. The
same genuine shared formulas apply only at B or C, which really
remain physically unique. No formula for a unique physical mask is
assigned to an S shared interface, because there is no such interface.

The weak physical corner bounds at S give ED<=2Ra(a-b cos(theta)).
The exact nonshared identity E^2-D^2=a^2+2ab sin(theta)>0
then supplies strict ED>D^2. Hence the resulting force-ratio bound
is still strict. I checked the bit-zero interchange, the rational
quadratic x^2-(6831/4480)x-101/32 and its positive value151/8960
at27/10. Thus the needed directed ratio<27/10 is valid even at
the actual weak corner inequality. No continuity argument is used.

## 4. The contact cover and every imported scalar input are complete

There are at most two genuine shares, since S has none and B,C each
have at most one. If one transmitter were shared at both ends, its
endpoints must be B,C. The first two geometric sections of the
double-shared source use only these unique endpoints and the actual
same-side chord at the third square. Their support inequalities and
sum-to-product estimate give that chord length<sqrt(2)-1. This
contradicts S's actual chord one before any third-mask circle formula
or scalar certificate is used.

All remaining shares form a matching. The reflection/reversal of
bits follows from the actual directed side chart, so it carries the
original supported corner and its mean endpoints rather than choosing
a new one. The stated zero-, one- and two-share orbit covers follow.

For zero shares, the mixed vertical projection requires only the
actual norm/closure model and turns; the constant Fermat argument
requires that same positive-support model, zero closure gradient,
virial and the proper force triangle. All are present here.
For the two constant shared cases, the previously reviewed matrices
and angle restrictions require no new mask input except the
nonshared27/10 bound in the one-share case. For the mixed cases,
the closure, Cauchy, derivative and endpoint arguments are scalar
consequences of these same exact equations. The sole extra force
bound in the large-force mixed02 branch is again the proved27/10
bound at its nonshared unit1. The shared-unit strict corner bound
is never needed at S. Every radial canonical placement in the
dependency table is therefore covered.

No new matrix or coefficient packet is required. The existing
constant proofs retain their openly displayed finite matrix work.

## 5. The single remaining scalar orbit is geometrically impossible

After those exhaustive scalar contradictions, the only possible
chart is mixed110 with sole outgoing share0. S cannot occupy unit0,
since its original interfaces are not shared. At either other
placement the same actual channel1 has both applications adjacent
to their selected real circle corners:

\[
 z_1=p_1^++v_1,\qquad z_2=p_2^-+v_2.
\]

At S this is precisely the port adjacent to its original supported
corner, which was proved to have angle<12/25. At the other unit,
the actual unique circle corner has distance exactly one from the
application. The separately reviewed full near-corner lemma therefore
forces the same actual angle>12/25. Both placements are impossible.

This is a direct core contradiction throughout the original radius
window. It covers either zero-weight choice by a global physical
reflection and never discards the second circle corner. All positive
pair forces, true degrees, genuine means and their endpoints, actual
sliders and all nine physical squares remain. The full surviving
one-radial domain must have both individual weights positive; that
interior domain and the original parent gate stay open. No checklist
count, Lean compilation, CI or global equality conclusion changes.
