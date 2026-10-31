# Independent review of side ownership at a triangle S-root's near-origin interface

Date: October 26, 2026.

Reviewer: independent c6_five agent.

**Verdict: PASS, unchanged, for the complete local theorem and its stated
whole-interface application.** The exact frozen source is
S_ROOT_TRIANGLE_NEAR_ORIGIN_CONTACT_SIDE_OWNERSHIP.md, SHA256
`51dc1e532e3663d7637c3d22a7053d5b2e8e024d076706f5bbd793f8cc3e42be`.

I read all six sections and independently rederived the physical chart,
proper-port identity, full angle estimate, and all shared displacements.
No positive radial-concurrence sign, neighbor degree reduction, or
additional point-normal selection is needed. No repair was requested.

## 1. Exact scope and frozen dependencies

B is the true degree-three root of a genuine S leaf. Its other actual
neighbors are H,K. H meets the closed epsilon disk, K physically
touches the containing circle, and H,K physically touch one another.
Their actual degrees, circle weights, and additional forces are
arbitrary. In particular K need not be loaded. Every original packing
unit remains present.

The theorem excludes every strict free singleton HB contact, whether
BK is a singleton or a positive-length shared side. Shared HB contacts
retain their actual means and normals. It does not make the converse
claim about a free BK when HB is shared.

The singleton/singleton input is the independently reviewed
S_LEAF_ROOT_FIXED_NONLEAF_CONTACT_SELECTION.md at
`499e6d42632a811bcb7bef6596b8585c11fbb5f59f36551d02fd05c080387a43`.
I previously audited its complete finite selection and physical
domain; its neighbor-degree-free statement applies here exactly.

I reread the exact physical proper-port lemma in Section 2 of
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md at
`20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf`.
That section is genuinely geometric, despite the stronger loaded-tip
context of the file's main theorem. Its full axis, adjacent-vertex,
coincident-vertex, and impossible-opposite-vertex cover applies to
the actual two nonparallel supports of B in any physical H-B-K
triangle. It imposes no equilibrium or load hypothesis at H or K.

## 2. The small support bound and the complete free/shared chart

The real radial S application de and unit inward segment prove that
the root meets D_epsilon. The source's explicit own-coordinate
verification is also correct, including tilted roots and aligned
mean endpoints: with d<sqrt(2), at most one closest-point coordinate
can exceed its unit interval, and that excess is at most epsilon.

At the actual B-to-H support line, a point of B in the small disk
gives h>=-epsilon, and a point of H gives h<=epsilon. Both concern
the same original separator. No contact point is moved into the
small disk to obtain this bound.

When BK is shared, its unique normal is a root side axis. Normalize
it upward. The radius-free physical triangle theorem gives a
nonnegative upward component to the actual HB normal. Since HB is
free, strict vertex exposure makes both components nonzero; after
horizontal reflection it is n=(-u,v), u,v>0. The complete true B3
force equation then puts its genuine leaf direction strictly right
and down. Its radial application is the actual lower-right root
corner p=(A,-b), with A,b>0 and A^2+b^2=d^2.

Thus B=[A-1,A] x [-b,1-b] and the actual free HB point is
P=(A-1,1-b). The original positive equations give mu*u=lambda*A
and b*u-A*v>0. Both inequalities are strict consequences of the
retained third force. They yield the full interval
0<v/u<b/A without a choice of a sampled normal.

## 3. Properness supplies exactly A<=b, with no radial sign premise

The two nonleaf lines are nonparallel because u>0. The true torque
equation makes their concurrence q a real multiple of (A,-b).
The geometric triangle lemma gives P=q+ell*n, ell>=0, for the
actual free point and the actual shared force line.

Multiplying the first coordinate of q=P-ell*n by b and the second
by A, then adding, gives precisely

`A-b+ell*(b*u-A*v)=0`.

Since the parenthesized term is strictly positive, A<=b. This proof
allows ell=0 and any sign of the scalar in q=t(A,-b). It neither
asserts that q is inside B nor imports positive radial concurrence
from an isolated cycle. The possible shared-mean coincidence at P
is retained in this identity and the following contradiction.

## 4. The angle bound is uniform on the whole original interval

The actual support is h=u*(1-A)+v*(1-b). From A<=b and the fixed
norm, A<=d/sqrt(2)<1037/1440<1. On the complete closed comparison
interval 0<=theta<=arctan(b/A), the function
(1-A)cos(theta)+(1-b)sin(theta) attains its minimum at an endpoint.
For b<=1 it is positive and concave. For b>1 its derivative is
strictly negative. These two alternatives include b=1 and do not
assume the coefficient 1-b is positive throughout.

The endpoint values are exactly 1-A and (A+b-d^2)/d. Under A>=1/10,
the first is above 403/1440. For the second, s=A/d lies strictly
above 6/61 and at most 1/sqrt(2); the function s+sqrt(1-s^2)
increases on that entire interval. The displayed radical bracket
sqrt(3685)>60 therefore gives a lower bound above 239/3660, itself
above 1/60 by 89/1830. Both contradict the original support bound.

Hence 0<A<1/10 and b>sqrt(4/5)>8/9. I recomputed the displayed
rational identities and positive reserves, including the 4/405
squared reserve for the last comparison. All radius endpoints and
the equality A=b are covered by these strict estimates.

## 5. Every original shared-return displacement is excluded

The common-frame K chart is
[A-1+s,A+s] x [1-b,2-b], with the complete shared-length interval
-1<s<1. Its actual shared force mean is unrestricted throughout.

For s<0, P lies in the relative interior of K's bottom side. K's
upper half-plane and B's lower-right quadrant leave only the exact
lower-left quadrant for a third unit H at P. Its inward axes include
-e_y, but n.(-e_y)=-v<0 contradicts P being a minimum-n support of H.
This is a local physical obstruction to the unchanged strict normal.

For s=0, K and B fill the upper-right and lower-right quadrants.
H's entire inward tangent cone lies in the left half-plane. Its
whole unit therefore has x<=A-1<-9/10, incompatible with its real
point in D_epsilon. This treats the exact displacement wall directly.

For s>0, every actual K point has |x|<11/10 and |y|<10/9. The
second bound retains the negative lower height 1-b>-1/60. Thus all
K corners have squared norm below 19801/8100, strictly less than
(79/40)^2 by 37741/25920. I recomputed both identities exactly.
K is consequently physically circle-clear, contradicting the real
boundary premise, independently of its chosen circle coefficient.

These three signs exhaust all allowed shared displacements. No
endpoint mean is dropped, and no mean is replaced by a geometric
endpoint to obtain the bounds.

## 6. Full interface join and precise remaining scope

If BK is a singleton, the frozen fixed-nonleaf selector already
excludes free HB in the same compatible certificate. If BK is shared,
the new force and geometry argument excludes its full continuous
domain. The new source therefore needs no added finite avoidance
condition and proves the complete local HB side-owner conclusion.

For the S/S hub-tip diamond, the actual S-leaf tip root B has true
degree three, its genuine S-leaf hub neighbor H meets D_epsilon,
the actual K is boundary, and HK is physically present. Every premise
is supplied while H4 and K3 remain unchanged. Thus the whole free HB
interface is removed from M6.B4L2.DIAMOND.HUB_TIP.LKC.SS. This is
not a closure of the remaining side-owner or free-BK/shared-HB
families and introduces no new original gate tick.

The result is reusable at arbitrary H,K degrees under its stated
physical triangle and genuine-root hypotheses. All masks, individual
zero weights, actual side means, displacement walls, and completion
units remain. No force deletion, radial-sign assumption, post-extraction
normal change, orientation sample, computational exclusion certificate,
Lean invocation, CI, ledger edit, or remote mutation was used.
