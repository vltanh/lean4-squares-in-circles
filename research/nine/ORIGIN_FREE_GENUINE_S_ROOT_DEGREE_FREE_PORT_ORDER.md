# Strict moment-port order at an origin-free genuine S root, with arbitrary true degree

Date: October 28, 2026. Author: two_blocks.

**Status: complete proposed uniform physical theorem, frozen for full
root and separate independent review. No original gate is changed.**

Keep all nine original interior-disjoint closed unit squares, their
unchanged containing circle and compatible selected positive certificate,
with

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1 <61/60,
    epsilon=max(d-1,0)<1/60.

Let X have a genuine positive leaf L and suppose O is not in the
closed X. The radial-leaf theorem forces L to be S and d>1. Its
actual contact is d e and its actual center is (d+1/2)e. X meets
closed D_epsilon. Its true degree and all its other forces remain
arbitrary; in particular no two-force or three-force equation at X
is a premise of either local theorem below.

**Port theorem.** Let p_-,n_- and p_+,n_+ be two actual contacts
of X with units different from its real leaf L, retaining their
actual outward unit normals and applications. If

    det(p_-,n_-)<0<det(p_+,n_+),

then the counterclockwise angular change from p_- to p_+ on the
unique angular branch of the origin-free convex X is strictly
positive. The neighbors have no degree, load, force or disk-avoidance
premise.

**Radial theorem.** No actual unit T different from L and avoiding
O can have a radial contact with X. Here a radial contact means
an actual common application p and separating normal n with
det(p,n)=0. It need not be a bridge or carry positive force.

## 1. The exact occupied-leaf cap

Every actual contained unit center c satisfies

    |c|<=d+1/2<M, M=91/60.

Every contained unit on the outer side n.x>=h of an actual unit
support satisfies h<=d and c.n>=h+1/2. These follow from the
farthest-corner center inequality and the minimum half-width 1/2,
as in Section 1 of the pinned degree-free moment-port source.

Put C=3501/2440. The open cap defined by

    c.x>C, |c|<M

lies in a rectangle of squared diameter

    (M-C)^2+4(M^2-C^2)=52124381/53582400<1.

Two distinct actual centers cannot both lie there, since their
disjoint open radius-1/2 incircles require center distance at least
one. This is an actual occupied-center argument, with no force
equation at either unit.

The following estimate will place every forbidden neighbor in that
cap. If its actual supporting normal n=(u,v) satisfies

    u>60/61, |v|<11/61, h>1,

then its center has c.n>3/2 and

    |c.Jn|<sqrt(181)/60<27/120.

Resolving the first coordinate gives

    c.x>(3/2)(60/61)-(27/120)(11/61)=3501/2440=C.

All inequalities use the entire actual contained unit, not a
surrogate center or a leaf equation assigned to that neighbor.

## 2. The aligned S root

If e is an own side axis of X, rotate it east. The exact geometry is

    X=[epsilon,d] x [b,b+1], -1<=b<=0,
    L=[d,d+1] x [-1/2,1/2], epsilon=d-1>0.

A nonleaf neighbor with outward X normal east would lie in x>=d.
Its center then has c.x>=d+1/2 while |c|<=d+1/2. Both inequalities
must be equalities: c=(d+1/2,0), and its east half-width is 1/2.
A unit square has this half-width only when its own axes are east
and north. The actual neighbor is therefore exactly L. Hence no
nonleaf contact uses the east side-axis normal, at any side mean.

At the upper-right vertex p=(d,b+1), an outward normal is
n=(u,v) with u,v>=0. A negative moment would give

    d v<(b+1)u.

For u,v>0 its support then satisfies

    h=d u+(b+1)v>d(u+v^2/u)=d/u>=d,

contrary to actual neighbor containment. The v=0 endpoint is the
already excluded east axis; the u=0 endpoint has positive moment.
Thus there is no negative nonleaf port at this upper-right vertex.
Reflection gives no positive port at the lower-right vertex.

The complete remaining feature cones are as follows. The top side
and upper-left vertex have nonnegative moment, strictly positive
when the moment is nonzero. The bottom side and lower-left vertex
have nonpositive moment, strictly negative when nonzero. On the
left side the moment equals the actual y coordinate. Consequently
every negative port has y<=0 and every positive port has y>=0.
All points of X have strictly positive x coordinate.

Their angular change is strictly positive. Equality would require
both y coordinates to be zero. If zero lies strictly between the
two horizontal sides, the only remaining such feature is the left
side and its moment is zero. If the upper side is y=0, only positive
nonzero moments can occur there; if the lower side is y=0, only
negative nonzero moments can occur there. The distinct sides cannot
both be y=0. Thus the required two strict signs cannot have equal
angular coordinate. This includes every aligned endpoint b=-1 or 0
and every original side application.

## 3. The strictly tilted S root

Reflect and exchange own axes, also interchanging the positive and
negative labels under a reflection, to put

    X=[U-1,U] x [V-1,V],
    e=(U,V)/d, U>=V>0, U^2+V^2=d^2.

These operations preserve the claimed oriented order. Since
V<=d/sqrt(2)<1 and X avoids O, necessarily U>1. Therefore

    a=U-1 satisfies 0<a<epsilon,
    0<V<sqrt(d^2-1)<11/60.

The second own interval strictly straddles zero. The actual leaf
port is P=(U,V). The actual leaf center satisfies

    (c_L).x=U(1+1/(2d))>1+1/(2d)>91/61>C.

Thus the real L already occupies the cap in Section 1.

### 3.1. The leaf corner and far side remain physically occupied

No other actual unit can touch X at P. Every outward X normal
n there has nonnegative own components and e.n>0. For a neighbor
across such a normal, the actual inward support segment contains
P+t n for all sufficiently small t>0. Since P is the midpoint
of the inward side of the actual S leaf and e.n>0, those points
belong to int L. This forces interior overlap, even if such a
point were initially on the boundary of the neighboring unit.

No nonleaf neighbor can use the far-side normal east. Its center
would have x coordinate at least U+1/2>3/2>C and norm less than M.
It would occupy the same cap as the distinct real leaf, contrary
to the cap diameter bound.

### 3.2. Every wrong-sign far-lower vertex is excluded

At the remaining far-lower vertex W=(U,V-1), an outward normal is
n=(u,-v), u,v>=0. Suppose its moment were nonnegative:

    (1-V)u-Uv>=0.

Then u>0. If v>0, its actual support satisfies

    h=Uu+(1-V)v>=U(u+v^2/u)=U/u>1/u.

The same final inequality holds for v=0, when h=U>1. Containment
gives h<=d, hence u>1/d>60/61 and v<11/61. Section 1 puts this
neighbor's center in the already occupied cap. It cannot be the
actual leaf L, whose unique minimum-e side touches X only at P:
the strictly tilted X has e.x<d at W. This contradicts the cap
bound. Thus every nonleaf contact at W has strictly negative
moment; all axis endpoints and the zero-moment boundary are covered.

### 3.3. Full tilted port order

The upper-right leaf corner and east side are excluded. The top
side and upper-left cone have strictly positive moment, and their
points have y=V>0. The bottom side and lower-left cone have strictly
negative moment, and their points have y=V-1<0. Section 3.2 gives
the same negative sign at the far-lower vertex. On the left side
the moment equals its actual y coordinate.

It follows that every negative nonleaf port has y<0 and every
positive nonleaf port has y>0. Since x>=a>0 on X, this proves
strict negative-to-positive angular advance. Every own feature,
normal-cone endpoint, shared-side mean and physical neighbor frame
is included. No force or moment equation at X was used.

Sections 2--3 prove the port theorem at every allowed S-root frame.

## 4. Complete radial nonleaf exclusion without a degree premise

We reconstruct the degree-free radial argument to make its scope
explicit. For any actual radial contact p!=O, choose its inner
unit U_0 and outer unit V_0 so that

    p=t n, t>0,
    n.x<=t on U_0, n.x>=t on V_0.

The contained-neighbor bound gives t<=d, and p is the unique
nearest point of V_0 to O. If U_0 avoids O, reflect one missing
own interval to [a,a+1], a>0. Radial outward support forces the
corresponding coordinate of p to be a+1>1, so t>1.

Every origin-free actual unit U_0 has at most one outward radial
contained neighbor. To prove this, fix that same missing own axis
u for all such contacts. Each radial direction satisfies

    n.u=(a+1)/t>1/d>60/61, |n.Ju|<11/61.

The actual neighbor center has c.n>=t+1/2>3/2 and norm<M.
The calculation in Section 1 puts its u coordinate above C.
The exact rectangle cap then prevents two distinct such neighbors.
This holds for all radial contact features and actual means.

Now let T!=L avoid O and have a radial contact with X. A contact
at O is impossible because X avoids O. If X were its outer unit,
the origin-free inner T would force t>1, whereas the same radial
geometry gives

    t=dist(O,X)<=epsilon<1/60

from the genuine S-root inward unit segment. If X were its inner
unit, both T and the distinct actual L would be outward radial
contained neighbors of X, contradicting the preceding cap.
Both alternatives are impossible. This proves the radial theorem.

## 5. Exact inputs, comparison and retained scope

| Source | SHA256 | Operative scope |
| --- | --- | --- |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Exact genuine S/D forms, actual leaf midpoint and full inward unit segment. |
| GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md | 8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49 | Section 1 actual center and support bounds; these do not assume force equations or degree. |

The occupied-leaf cap is reconstructed in full from the physical
calculation already used in Section 1 of
`ROOTED_C3_334_PRIVATE_OPPOSITE_LEAF_C4_EXCLUSION.md`. The radial
argument is reconstructed from Sections 1--3 of
`ROOTED_ORIGIN_FREE_RADIAL_CONTACT_EXCLUSIONS.md`. Their later
triangle, concurrence and true degree-three arguments are not
operative here.

In particular this source does not apply a true X3 concurrence to
a higher-degree root. It neither selects two forces as a complete
star nor resets either application. The real leaf is used as an
occupied physical square. All additional positive X forces, actual
contacts and completion units remain unchanged. No numerical pose,
finite orientation table, Lean build, compilation, CI, remote write
or original ledger change is used.
