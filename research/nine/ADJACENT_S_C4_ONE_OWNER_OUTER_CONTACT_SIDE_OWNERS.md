# Both outer contacts have a side owner in the one-owner adjacent-S C4

Date: October 27, 2026.

**Status: complete hand compatible-selection export, submitted for
full root and separate independent review.** It strengthens the
necessary contact cover, without claiming a whole residual layout
or gate excluded.

Retain all nine actual units and the original positive component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,

in the full strict-high adjacent-S domain. The original AB normal
is owned by A and not B. Use the complete all-physical-mask leaf
reduction
ADJACENT_S_LEAF_C4_ONE_OWNER_ALL_MASK_LEAF_REDUCTION.md,
independently accepted in
REVIEW_ADJACENT_S_ONE_OWNER_ALL_MASK_REDUCTION_ROOTED_BLOCKS_2026_10_27.md.

The exact selected normal is East, its unchanged application is
P=(h,-k), and its positive origin moment gives

    |h|<=epsilon<1/60,       k>0.

P is a fixed actual B vertex and lies in the relative interior
of A's actual side. The remaining genuine A leaf is its strict
outer lower vertex or its owned West side. The remaining genuine
B leaf is the strict lower adjacent vertex or its owned far-j
side in the actual frame

    f=(c,s),       j=(s,-c),
    c,s>0,       c^2+s^2=1.

**Theorem.** In the same compatible necessary certificate,
each of the actual outer edges AD and BC has a side-axis owner
at one of its endpoints. More precisely, a strict upper-vertex
AD feature is owned by D, and a strict upper-vertex BC feature
is owned by C. Actual root-owned North means remain arbitrary.
For the West A leaf its already forced AD East mean also remains
arbitrary.

## 1. Exact singleton selection and why it applies here

The general original preselection is Section 4 of
ADJACENT_C4_SINGLE_LOAD_S_LEAVES_EXCLUSION.md. At a true
three-force radial-leaf root, let q,p be its two distinct actual
singleton applications, with original outward normals n,m and
radial leaf direction e. The full force and zero origin-moment
equations imply

    det(e,n)*det(p,m)-det(e,m)*det(q,n)=0.             (1)

If n is a free vertex/vertex normal, m is fixed and not parallel
to e, and q is not collinear with e, then (1) reads

    det(W,n)=0,
    W=det(p,m)*e-det(e,m)*q !=0.                      (2)

It excludes only finitely many directions in the original strict
free-normal interval. The finite pose prelist contains every
possible actual leaf assignment and every such pair of singleton
features before multiplier extraction. These finite open dense
conditions are compatible with the original matched-junction,
nonradial and uncrossing conditions. Since p!=q, a matched pair
at q does not couple this variation to the fixed axis at p.

No side mean is selected by this rule. In the present application,
the other contact AB is a singleton because B has its actual
unique supporting vertex P; at A it is the same fixed physical
point P supplied by that neighboring vertex. Its selected normal
is the fixed A axis. Thus it is a legitimate fixed singleton at
either root, even though A owns a side there.

If a strict upper contact were not owned by its other endpoint,
it would be a free point-only vertex/vertex contact. The original
strict-point convention excludes a nonowned axis endpoint.
Uncrossing retains surviving point normals and only adds actual
shared-side endpoint atoms; it does not introduce an axis at
the present point-only tilted AB contact. Conic thinning only
deletes original atoms.

This rule uses the declared true A3 or B3 equation, not a
three-force surrogate obtained by deleting an extra attachment.
It uses no circle mask or degree at the other endpoint.

## 2. The complete outer AD cover and noncollinearity

If A's real leaf is owned West, the accepted all-mask reduction
already gives AD East, with its entire actual mean
(-epsilon,y), y>4/5. A owns that normal, so there is no further
selection to apply.

Otherwise write the actual strict outer-lower genuine point as

    d*e_L=(-X,-v),       X=1-h,
    X^2+v^2=d^2,       0<k<v<13/50,
    X>59/60.

The full A3 vertical component makes its outward AD force
strictly upward. The complete support cover is its North own
side or one of the two strict upper vertices. North is already
owned by A, and its full original application interval is kept.

At the strict upper-left and upper-right vertices, respectively,

    q_-=(-X,1-v),       q_+=(h,1-v),

the exact determinants are

    det(d*e_L,q_-)=-X !=0,
    det(d*e_L,q_+)=v-X !=0.                             (3)

The latter is strictly negative by v<13/50 and X>59/60.
The two points are distinct from P, since P is a relative
A-side-interior point with negative height. The other selected
normal m on AB is East and is not parallel to e_L because v>0.

Therefore (1)--(2) exclude a free AD normal at either strict
upper vertex. D owns the actual normal. No AD or AB mean
was substituted in this conclusion.

## 3. The complete outer BC cover

Use the actual positively oriented (j,f) frame. The original
B-to-A normal is (-s,-c). The two actual genuine-leaf charts
are as follows.

For the strict lower adjacent leaf,

    B=[xi,xi+1] times [-w,1-w],
    d*e_M=(U,-w),       U=1+xi,
    -epsilon<xi<epsilon,       0<w<13/50.

The accepted force-free shallow-S screen and the full B3
f component leave precisely North, strict Northwest or
strict Northeast. The full component is

    (F_BC)_f=mu*c+beta*w/d>0.

At the strict vertices q_-=(xi,1-w), q_+=(U,1-w),

    det(d*e_M,q_-)=U-w>59/60-13/50>0,
    det(d*e_M,q_+)=U>0.                                (4)

For the owned far-j leaf,

    B=[epsilon,d] times [-w,T],       T=1-w,
    d*e_M=(d,0),       0<=w<=1.

Its full f component is (F_BC)_f=mu*c>0, so the
same three upper support features exhaust all possibilities.

In this type T is in fact strictly positive. If w=1, the
actual root support bound h=epsilon*s-c>=-epsilon gives

    c<=epsilon*(1+s)<1/30,       s>29/30>c.

At North, its actual mean (epsilon+ell,0), 0<=ell<=1,
obeys c*ell=s, impossible. At strict Northwest the full
moment gives nu*T*a=mu*w*s>0, impossible for T=0.
At strict Northeast the full moment gives
nu*T*a=mu*(c-w*s)<0, again impossible. These are the
unchanged true B3 equations, so no endpoint was silently
discarded. Hence T>0.

At either strict upper vertex in this owned-leaf type,

    det(d*e_M,q)=d*T>0.                                (5)

For both genuine-leaf types, the other normal on AB is
(-s,-c). In the strict-leaf type,

    det((U,-w),(-s,-c))=-U*c-w*s<0,

and in the owned-leaf type it is -d*c<0. Thus it is not
parallel to e_M. The upper q points in (4)--(5) are distinct
from the fixed lower-left vertex P.

The singleton rule (1)--(2) now excludes a free BC at every
strict upper vertex, so C owns the actual normal. The
North-side feature remains B-owned with its full original
mean. This proof retains w=0 in the owned-leaf type.

## 4. Exact all-mask consequence and remaining scope

The full original one-owner cover now has precisely these
outer-edge alternatives:

| Genuine root leaf | Actual outer contact cover |
| --- | --- |
| A strict outer lower | A-owned North, or D-owned normal at an actual strict upper A vertex |
| A owned West | A-owned East with the complete original mean |
| B strict lower adjacent | B-owned North, or C-owned normal at an actual strict upper B vertex |
| B owned far-j | B-owned North, or C-owned normal at an actual strict upper B vertex |

This holds for every physical C/D circle mask. It is stronger
than the unique/unique all-cycle determinant at this particular
one-owner scope, because its fixed AB point is supplied by the
actual tilted B vertex. No corresponding conclusion for a
variable shared AB side mean is asserted.

In a C-two-corner mask the radial-boundary theorem already
forces B-owned North; the table supplies the complete actual
AD cover. In a D-two-corner mask only A's outer-lower leaf
remains and AD is A-owned North; the table supplies the
complete actual BC cover. Both-two-corner is separately
excluded in the accepted whole-mask source.

Every remaining North/East side mean, the original CD
contact, all true degrees and positive magnitudes, both
real leaves and all completion squares remain. This is
a compatible necessary-domain theorem, not a new claim
that any remaining contact layout or complete cell is
impossible.
