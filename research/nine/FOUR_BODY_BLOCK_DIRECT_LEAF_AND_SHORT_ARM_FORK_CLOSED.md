# A four-body block cannot carry a fork with a direct leaf and a short arm

Date: October 27, 2026.

**Status: complete hand whole-attachment theorem, resubmitted for full
root and separate independent review after correction of its negative-
bridge dependency.** Sections 1--4 are unchanged. Section 5 now uses
the correct full circle-force sign and the dependency's mask-specific
forbidden rays and two-triangle winding correction. No shared metadata
or coarse count is changed.

Keep all nine original physical units and the common compatible
selected radius/Phi-minimizer and minimum-positive-original-scalar-
atom certificate, with

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,       9/10<d<61/60,
    r=R-sqrt(2),       1/2<r<2/3,
    epsilon=max(d-1,0)<1/60.

The positive component consists of an actual four-body cyclic block
and the exact original four-edge outside tree

    H--U,       U--L,       U--V,       V--M,

where H belongs to the cyclic block, U,V,L,M are four distinct
outside bodies, U has true positive degree three, V true degree
two, and L,M are genuine positive leaves. The ninth physical
square remains arbitrary and present. All actual forces, full
root circle loads, physical masks, individual zero weights,
selected normals and actual shared-side means are retained.

**Theorem.** This entire C1.4.b4 attachment is impossible for every
four-body block profile, root orbit, leaf type and radius. It does
not close every other four-bridge forest or the whole coarse cell.

## 1. The genuine fork contains O and its short arm is S/side

All three original U edges are bridges. Deleting U gives three
positive branches, so the exact bound k+ell<=3 in
GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md, Section 5, forces
U's circle load to vanish. Thus U is a true unloaded all-bridge
body of degree three. If it avoided O, the full minimal-support
theorem GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md would
make its true degree two. Consequently

    O belongs to closed U.                            (1)

The three branch resultants at U cannot all be collinear. Indeed
their force and normalization vectors would then lie in a space
of dimension at most two; the exact branch-reweighting proof
would remove one whole positive branch while preserving every
remaining original mean and all physical bodies, contradicting
the same atom-level minimality. This is the unchanged three-
branch noncollinearity used in ONE_CYCLIC_BLOCK_FIVE_BRIDGES_EXCLUDED.md.

V is the actual root of genuine leaf M and is physically clear.
Its true positive degree is two, so its original force and torque
equations give a real normal transmitter of width w in {1,sqrt(2)}.
If e is M's genuine radial direction, its actual U--V application
is

    p_UV=(r_M-w)e,
    r_M=r for D,       r_M=d for S.                    (2)

The actual support of U in direction e is r_M-w. By (1) it is
nonnegative. Since r<1 and d<sqrt(2), the entire actual arm-type
cover therefore reduces to

    M is S,       w=1,       d>=1,
    p_UV=(d-1)e=epsilon e.                             (3)

In particular every strict-low-radius case d<1 is excluded already.
No U or H force was removed to obtain (3).

## 2. The original parent bridge is radial

Cut the actual H--U bridge and sum the full origin moments on the
original U-side subtree U,L,V,M. Every actual circle force has zero
origin moment, and internal pair forces cancel at their unchanged
common applications. Hence the H--U force also has zero origin
moment. With n its unit normal from H into U and beta>0 its
magnitude, the actual application is

    P=rho n.

Equivalently, if m=-n is the true outward parent normal from U,
then P=lambda m with lambda=-rho. Because O belongs to U,

    lambda>=0.

The sharp contained-neighbor support bound from
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1, also gives

    lambda<=d.                                         (4)

We prove the strict inequality lambda>0 in every remaining case.
It will be the exact strict negative-bridge hypothesis at H.

## 3. At high radius the genuine fork is origin-interior

Assume d>1. If L is D, its actual root U contains O openly, so
every outward unit support of U is positive and lambda>0.

Suppose L is S with genuine direction g. If g were an own side
axis of U, that root's longitudinal interval would be [d-1,d],
which excludes O. This contradicts (1). Thus d g strictly exposes
a U vertex. In the two inward own directions, the coordinates of
O from that vertex are

    d a, d b,       a,b>0,       a^2+b^2=1.

They both belong to (0,1] by (1). If O were not interior, one
coordinate would equal one. Both cannot equal one, since d<sqrt(2).
The other would equal

    t=sqrt(d^2-1)=sqrt(2epsilon+epsilon^2).

After choosing signs and exchanging the own axes, the whole
actual unit would consequently be

    U=[0,1] times [-t,1-t].                             (5)

Here the elementary strict comparisons are

    t>epsilon,
    1-t>epsilon,

because t^2-epsilon^2=2epsilon>0 and
(1-epsilon)^2-t^2=1-4epsilon>0. In particular every vertex of (5)
has norm greater than epsilon. Its four outward own-side support
heights are exactly 0,1,t,1-t, none equal to epsilon.

But (3) supplies an actual outward radial support point epsilon e.
If e is not an own side axis, that point must be a vertex of norm
epsilon, which (5) excludes. If e is an own axis, its support height
would be epsilon, also excluded. This is the complete side/vertex
cover, including actual side endpoint means. Therefore O must
belong to int(U), proving lambda>0 for every high-radius type.

## 4. The entire critical endpoint also has lambda>0

Now d=1 and R^2=17/4. Equation (3) gives the actual U--V point O,
so O cannot be interior to U. The direct leaf L cannot be D,
because a D root is origin-interior. Thus L is S.

If O lay in a relative side interior of U, its only outward radial
support point of norm one would be the foot on the opposite side.
For example, in U=[0,1]u+[h-1,h]v with 0<h<1, the other side
heights are strictly below one, the near-side vertices have norm
below one, and the far-side vertices have norm above one. Hence
L's real direction is u and the arm's actual outward normal at O
is -u. The third force is then also parallel to u, contradicting
the full original three-branch noncollinearity from Section 1.

Consequently O is a U vertex. Choose the actual own axes so that

    U=[0,1]u+[0,1]v,       L=S(u).

At an origin-vertex unit the only outward radial support points
of norm one are its two adjacent vertices; this justifies the
exhaustive choice of L's direction. Write e for the actual arm
normal from (3), m for the actual parent normal, and retain all
three positive magnitudes:

    alpha u+gamma e+beta m=0,
    alpha,gamma,beta>0,
    e.u<=0,       e.v<=0.                              (6)

If e.v=0, every vector in (6) is parallel to u, again forbidden.
Thus e.v<0 and m.v>0.

If m.u<0, the actual parent support is the unique vertex v. Its
radiality P=lambda m is incompatible with m.u<0. If m.u>0, the
parent support is the unique vertex u+v; radiality gives
lambda=sqrt(2), contradicting the sharp bound (4) with d=1.
The remaining case is exactly

    m=v,       P=v,       lambda=1.                    (7)

This preserves a possible shared-side endpoint mean; it does not
call the original H--U contact a singleton. Its actual H may be
a physical boundary unit at this critical endpoint, so its full
circle force must be retained in the next step.

## 5. The complete original block is excluded with its root load intact

Sections 3--4 prove lambda>0 in every remaining type. With the
unchanged normal from H to U this is

    P=rho n,       rho=-lambda<0,
    O belongs to closed U.

H--U is the only original edge from the four-body cyclic block
to the outside forest. Each private block body has exactly its
actual block degree. Every hypothesis of
FOUR_BODY_BLOCK_NEGATIVE_BRIDGE_WITH_FULL_ROOT_LOAD_EXCLUSION.md
therefore holds.

That theorem forms the private block resultant using the complete
root equation

    M=-G_H-beta n,

with the entire actual G_H retained. Its forbidden-ray premise is
proved separately for every actual load mask: by genuine root
clearance, or by the full boundary-force acuteness at a loaded
opposite-mask root. Its two-triangle root correction needs no
positive-M point. Its zero/single/double/triple private-load cover
excludes every C4 mask; the complete hub/tip diamond and selected
K4 cover excludes the remaining profiles. No leaf or transmitter
equation is assigned to H and no original private force is dropped.

This closes the whole original direct-leaf-plus-short-arm fork,
including critical boundary-root cases, all D/S choices for L,
all original masks and means, and the ninth arbitrary physical
unit. The proof uses no numerical sampling, post-extraction normal
change, Lean compilation or CI.
