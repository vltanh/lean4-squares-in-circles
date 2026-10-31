# Root audit: the physical orientation of a boundary-contact moment

Date: October 28, 2026. Reviewer: root, separately from author hexagon.

**Root decision: ACCEPT the complete force-free local sign theorem.**
Separate full independent review remains required before checkpoint
acceptance. This is a local interface, not a whole original-family exit.

## 1. Frozen full source and exact imports

I read the complete `BOUNDARY_CONTACT_ORIGIN_MOMENT_ORIENTATION.md`,
SHA-256 `851417d7fcd12ccb93a6f7f09ba7d7b2bf9bccc61c82fee3457b5ee4cee47e9a`.
I also reread the full physical center-gap and touching-neighbor proof
and the complete one-square corner/resultant angle argument used here.
The current bytes match both literal input pins in the source. The
one-square angle lemma has no balanced-four-body-path premise.

The actual premises are two interior-disjoint contained unit squares
which both physically touch the circle, and any point and any directed
unit normal in their real common support face. The complete declared
radius window is retained. Degrees, positive force assignments, side
ownership and shared-side means are unrestricted. Optional resultant
weights are merely nonnegative and not all zero on each square.

## 2. The entire physical sign proof

With O as coordinate origin and n=East, write the unchanged application
as (h,y). Both squares have normal width at least one, so
1-R<=h<=R-1. If y=0, choose the circle corner of the square on the
origin-facing side of the support line. Its squared distance from
the application is at least R^2-h^2>=2R-1>2, contradicting the
unit diameter. Thus the contact moment -y is nonzero without using
any force equation or proper-concurrence theorem.

For y>0,h>=0 the same full diameter calculation forces every circle
corner of the left square to have positive y. Choose its angle in
(0,pi), and a right-square corner angle in [-pi/2,pi/2]. Their support
ordering gives theta_A>=|theta_B| and hence L=theta_A-theta_B>=0.
Equality would be a shared physical circle point, which is impossible:
the short inward radial segment lies in the open interior of either
contained square at such a corner. Therefore L>0.

The actual contact-to-corner distance also gives z_A.x>=h-sqrt(2).
The strict lower radius bound makes theta_A<5pi/6, so L<4pi/3.
If L>=pi, its minor gap is 2pi-L>2pi/3. The center contact gap and
the two individual corner deviations bound that same minor corner
gap by 17pi/30, a contradiction. Thus 0<L<pi, and indeed L<17pi/30.
This resolves the possible angular wrap rather than assuming a lift.

Lifting the center directions within pi/12 of those two chosen
corners gives their difference in (-pi/6,11pi/15). A nonpositive
difference would have absolute value below pi/6, violating the
strict center separation pi/5. The directed difference is therefore
positive and below pi. Hence both the center determinant and the
actual contact moment are negative in this whole sign row.

For h<0 with y>0, horizontal reflection followed by exchange of the
two physical bodies preserves both determinants: each operation
reverses the center orientation, and their combination preserves it.
The transformed directed normal is again East and the application
height is unchanged. For y<0, vertical reflection reverses both
determinants and reduces to the proved positive-height case. These
operations cover every h and every nonzero y, including h=0 and
all physical normal-cone and common-side endpoints.

## 3. Full resultant version and verification

The touching centers have directed minor gap of absolute value
strictly between pi/5 and 2pi/5. Each full nonzero nonnegative
circle resultant deviates by less than pi/12 from its center.
Their directed gap consequently has the same sign and absolute
value between pi/30 and 17pi/30, strictly inside (0,pi). Its
determinant has exactly the proved physical contact-moment sign.
The argument includes either individual zero weight in a physical
two-corner mask and does not replace a higher-degree force star.

The exact check record
`/tmp/pr11_root_boundary_contact_moment_checks.json`, SHA-256
`fe8c770c08125b73c5cf3808e731054c962d547870e691207edbef7b2fc783e4`,
verifies both input pins and six strict rational radius/angle reserves.
The proof above is analytic over the whole physical domain. There
are no sampled configurations or computed force assumptions.

The theorem determines a sign only. It does not establish proper
concurrence, place the circle center, supply equilibrium, fix an
application mean, or close any original family. No Lean compilation,
CI, workflow, remote mutation or shared metadata edit was used.
