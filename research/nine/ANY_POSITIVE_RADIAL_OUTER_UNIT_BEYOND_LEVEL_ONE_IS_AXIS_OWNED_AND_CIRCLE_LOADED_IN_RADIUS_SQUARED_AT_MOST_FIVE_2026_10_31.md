# Every radial outer unit beyond level one is axis-owned and circle-loaded

Date: October 31, 2026 UTC.
Constructor: root.
Status: complete HAND theorem frozen for clean independent review.

This is a whole-star theorem for arbitrary actual neighbor sets. It does
not assume a leaf, two forces, a small graph, a root contact or a chosen
circle mask. All physical squares and all original pair and circle terms
remain. The geometric assertions need no equilibrium or certificate
selection; the final load conclusion uses the entire original star.

## 1. Exact theorem, including its larger radius window

Let a finite collection of actual closed unit squares have pairwise
disjoint open interiors and lie in the same closed disk D_R centered at
O=0, with R^2<=5. Let X,Y be distinct actual units with an original
positive pair at the unchanged common application

    p=t e, |e|=1, t>1,
    X subset {z:e.z<=t}, Y subset {z:e.z>=t}.

The direction e is the ORIGINAL X-to-Y pair normal, not a later radial
support substituted for it. Its positive pair magnitude is mu_XY.
At a shared side, p is the actual original mean, including endpoints.

**Theorem A, complete geometric outer frame.** e is an own side axis of
Y. In the orthonormal frame (e,f), f perpendicular to e, the SAME Y is

    Y=[t,t+1] x [-b,1-b], 0<b<1.

Its original p=(t,0) is in the relative interior of its inner side.
Every actual neighboring unit Z and EVERY geometric support normal n
from Y toward Z at their physical contact satisfy n.e<=0. This includes
original free normals, all owners, full shared-side means and endpoints.

**Theorem B, complete original-star load.** If these actual data have
an original equilibrium certificate with nonnegative circle coefficients,
then Y has positive total circle load. In particular Y is physically
boundary. With the original convention

    F_Y=2 sum_(physical circle corners z of Y) lambda_z z,
    sum_Z mu_YZ n_YZ + F_Y=0,

one has the quantitative whole-star bound

    F_Y.e >= mu_XY >0.

Every original positive neighbor Z is retained in this sum. Individual
zero circle coefficients and other physical contacts are retained too.

**Exact sharper frame in the nine-square window.** If additionally
R^2<=1105/256, then

    7/16<b<9/16,
    1<t<=sqrt(R^2-1/4)-1.

No assertion here applies at t=1 or with R^2>5. The closed endpoint
R^2=5 and, in the sharper consequence, R^2=1105/256 are included.
This theorem alone does not exclude the radial pair, a whole D family,
an original case label, or the global nine-square packing problem.

## 2. Whole actual normal segments, with no owner or mean restriction

At any actual minimum-n support point q of a unit square Z, where |n|=1,

    q+[0,1]n subset Z.                                      (1)

At a vertex let u,v be its inward orthonormal own axes. The components
of n along them are nonnegative and at most one. Each point q+s n,
0<=s<=1, therefore stays in the two closed unit coordinate intervals.
If n is an own inward normal and q lies in the relative interior of a
side, that segment preserves q's unchanged tangential coordinate. The
same proof includes both side endpoints. There is no choice of a new
contact point or mean in (1).

Consequently every actual Y-to-Z support at q has the necessary bound

    |q+n|^2=|q|^2+1+2 q.n <= R^2.                          (2)

This is a geometric statement about the actual contained neighbor Z.
It needs neither a positive force on that physical contact nor a load
or degree premise on Z. The elementary normal-segment argument already
appears in the earlier far-body and radial-inner sources; it is fully
reprinted here and is not claimed as a new method.

## 3. A strict minimum vertex would exceed the entire radius window

The actual p=t e minimizes e on Y. Suppose it were a strictly exposed
Y vertex. Let u,v be its two inward orthonormal own axes. Then

    e.u>0, e.v>0, (e.u)^2+(e.v)^2=1,
    e.u+e.v>=1.

The opposite actual Y vertex is p+u+v. Its squared norm is

    |p+u+v|^2=t^2+2t(e.u+e.v)+2
              >=t^2+2t+2>5>=R^2.                         (3)

The strict inequality follows from t>1. It is a whole normal-cone
argument, with no pose or angle evaluation. Thus p is not strictly
exposed. A unit square's remaining support directions are exactly its
own side axes, so e is such an axis.

Normalize the orthonormal chart to (e,f), keeping the same origin.
The complete actual side interval is now

    Y=[t,t+1] x [-b,1-b], b in [0,1],                      (4)

because the original point p has transverse coordinate zero. Containment
of BOTH opposite-side corners gives

    (t+1)^2+b^2<=R^2,
    (t+1)^2+(1-b)^2<=R^2.                                (5)

Since (t+1)^2>4 and R^2<=5, both b and 1-b are strictly below one.
This excludes b=0 and b=1 and proves 0<b<1. Therefore even an axis-owned
support at a vertex cannot survive; p is an actual relative-side-interior
point. This does not reset the original mean to the side midpoint.

## 4. Every entire physical neighbor lies behind a nonpositive-axis normal

Consider ANY actual neighbor Z of Y and an actual support normal
n=(n_x,n_y) from Y into Z. Suppose n_x>0. All such normals fall in the
following complete feature cover of (4).

If n_y=0, n=e and the original Y support point q lies on its far side
x=t+1. Equation (1) places q+e in Z, with first coordinate t+2>3.
Its squared norm exceeds9, contrary to R^2<=5. This includes every
possible far-side mean and both endpoints.

If n_y>0, the unique maximum-n Y point is the far upper corner
q=(t+1,1-b). Its coordinates are both strictly positive, so q.n>0.
Also |q|^2>(t+1)^2>4. Hence (2) would give

    R^2>=|q+n|^2=|q|^2+1+2q.n>5,                         (6)

a contradiction. If n_y<0, the maximum-n point is the far lower corner
q=(t+1,-b). Again both component products in q.n are positive, and
the identical strict bound (6) applies. These are all n_x>0 normals.

Thus every possible actual neighboring support satisfies n.e=n_x<=0.
No normal with n_x=0 has been excluded by an invalid strict argument;
all such tangential normals are allowed in the conclusion. The complete
inner side and its two cones likewise remain. All cases were proved
from the same actual Y and Z, and no force equation was changed.

## 5. Full-star equilibrium forces an actual positive circle coefficient

Return to the unchanged original positive star of Y. By Section 4,
each term has n_YZ.e<=0. The distinguished positive X pair has

    n_YX=-e, mu_YX=mu_XY>0.

Therefore

    sum_Z mu_YZ n_YZ.e <= -mu_XY <0.                      (7)

The COMPLETE original force equation now gives

    F_Y.e=-sum_Z mu_YZ n_YZ.e >= mu_XY>0.                 (8)

If every physical circle coefficient were zero, F_Y would be zero,
contrary to (8). Nonnegativity then means the total circle load is
strictly positive. At least one actual circle corner exists, so Y is
physically boundary. If it has two such corners, either or both may
carry positive weight; (8) discards neither physical corner and imposes
no equal-weight requirement.

The proof used every positive pair in the actual Y star. It did not
call Y a leaf, remove tangential pairs, infer its true degree, or merge
different neighbors into one physical unit. Any number of other actual
squares, their forces and their zero-weight physical contacts remain.

## 6. Sharp-window bounds and exact future application boundary

From (5), when R^2<=1105/256,

    b^2<1105/256-4=81/256,
    (1-b)^2<81/256.

Since b,1-b>0, this gives 7/16<b<9/16 over the whole stated window.
Also max(b^2,(1-b)^2)>=1/4, so (5) gives

    (t+1)^2+1/4<=R^2,
    t<=sqrt(R^2-1/4)-1.

These inequalities keep the original closed radius endpoints and every
allowed original side mean. They are necessary consequences, not choices
of a replacement pose.

In the continuing D-root proof this lemma is intended for an actual
non-H radial pair whose inner unit is the unique origin-free near X.
Its t>1 premise must be proved from the already accepted original
geometry before application. The separately accepted common-boundary
obstruction may then prohibit an H contact of this loaded outer Y, but
THAT composition and any moment-DAG conclusion are not proved or used
here. No independent result about H, X or a cyclic block is a premise
of the present generic theorem.

## 7. Complete proof and preservation boundary

This source is mathematically self-contained: there are ZERO operative
source dependencies. Its proofs of the normal segment, square support
cover, containment bounds and full-star projection are all printed above.
The original equilibrium convention is explicitly part of Theorem B's
hypotheses. It applies to any certificate satisfying those actual full
equations, not only to a selected generic one. Previous uses of the
normal-segment method retain their credit.

Root supplied the new whole outer-frame/contact-cone/load construction.
No prospective reviewer received its evolving mathematics before this
source was frozen. A clean noncontributor must read this entire source
and its complete companion base and reconstruct all cases by hand.

No mathematical script, symbolic check, numerical sample, pose grid,
optimizer, computational certificate, Lean/Lake, build, test or CI was
used. Any preservation program checks whole-file bytes, LF, hashes and
exact copies only. No original parent/count/global/equality flag or
GitHub file is changed. The nine-square project remains OPEN.
