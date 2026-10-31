# Radial contacts and a genuine leaf triangle outside an origin-interior unit

Date: October 27, 2026.

**Status: accepted complete hand theorem or reduction after full root and separate independent reviews.**
Reviewed mathematical SHA-256: `29a952efee6802ad0664b2ed55ffd82af8fcd9dc04d07b008e2124688c456906`. Root review: REVIEW_C3_334_B1_TRIANGLE_AND_DIAMOND_ROOT_2026_10_27.md. Separate review: REVIEW_ORIGIN_FREE_RADIAL_CONTACTS_GLOBAL_2026_10_27.md. No shared ledger
or original fine label is changed.

Keep every actual unit square, selected normal, original contact mean
and positive force in

    79/40<=R<=sqrt(1105)/16,
    91/100<d=sqrt(R^2-1/4)-1<61/60,
    epsilon=max(d-1,0)<1/60,
    r=R-sqrt(2)>14/25.

Every contained unit center has norm less than M=91/60. A contained
unit beyond support height h requires h<=d. These are the full
center and halfwidth bounds in END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md
Section 1. Distinct interior-disjoint units have center distance
at least one, by their disjoint open radius-1/2 incircles.

A radial physical contact means an actual common point p and
separating unit normal n with det(p,n)=0. It need not be a bridge
and need not have positive force unless a later statement says so.
No new radiality is inferred for an arbitrary contact.

## 1. Exact geometry of an already radial contact

For p!=O orient e so p=t e with t=|p|>0 and the inner unit U
lies in e.x<=t while the outer unit V lies in e.x>=t. Then

    t<=d,       dist(O,V)=t,                            (1)

and p is V's unique nearest point. The actual inward unit segment
p-[0,1]e belongs to U. This is the geometric proof in
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md Section 3, after radiality
has already been supplied; none of these deductions needs the
edge to be a graph bridge.

That proof also puts the inner U within distance max(R-2,0)
of O and makes U physically circle-clear. In particular a radial
contact cannot join two physical circle-touching units. This is
a geometric consequence for the stated radial contact, not an
assertion that all nonbridge contacts are radial.

If U avoids O even on its boundary, its outward radial support
has

    1<t<=d.                                           (2)

Indeed choose an own coordinate whose interval misses zero and
reflect so that interval is [a,a+1], a>0. The radial point has
positive coordinate on that axis, so its outward direction has
positive component there. Support maximization puts that point
at the far coordinate a+1>1, proving (2).

## 2. An origin-free unit has at most one outward radial contained neighbor

Let U be any actual unit avoiding O. Suppose it has one or more
physical outward radial contacts to contained neighbors. Fix an
own unit axis u on which U's interval is [a,a+1], a>0.
At each such contact p=t e, Sections 1 and (2) give

    p.u=a+1>1,     e.u>1/d>60/61,
    |e.Ju|<11/61.                                     (3)

This is one fixed own axis u for all the contacts. No force
balance or body-degree hypothesis is used.

For each actual outer neighbor center c, its halfwidth along e
is at least 1/2, so

    c.e>=t+1/2>3/2,      |c|<M=91/60.

Its transverse component along Je has magnitude less than
sqrt(181)/60<27/120. Resolving c along e,Je and using (3) gives

    c.u>(3/2)(60/61)-(27/120)(11/61)
          =3501/2440=:L_*.                             (4)

Every such center belongs to the same open cap rectangle. The
square of that rectangle's diameter is

    (M-L_*)^2+4(M^2-L_*^2)
       =52124381/53582400<1.                           (5)

Thus there cannot be two distinct outer neighbors. This statement
includes unstressed physical contacts and all radial support
features. It uses their physical half-planes, not fictitious leaf
or degree-two equations.

## 3. No other radial contact can meet an origin-free genuine leaf root

Let X be the actual root of a genuine leaf L and suppose X avoids
O. The full genuine-leaf alternatives exclude D and S with d<=1,
since those roots contain O. Therefore L is S, d>1, its real
outward radial application on X is d e_L, and

    dist(O,X)<=epsilon=d-1<1/60.                       (6)

Let T!=L be another actual unit avoiding O, with a radial physical
contact to X. A contact at O is already impossible. At a nonzero
contact orient its inner and outer endpoints as in Section 1.

If X were outer, the origin-free inner T would give radial distance
t>1, whereas (1),(6) give t=dist(O,X)<=epsilon. This is impossible.
If X is inner, both the real L and the distinct T are outward radial
contained neighbors of X, contrary to Section 2.

Consequently no such radial contact X-T exists. The conclusion
needs no force on XT and no degree premise at T. Its genuine
leaf hypothesis is retained exactly.

## 4. Uniform original-leaf triangle with a radial opposite edge

Let X,H,K be three actual pairwise-touching units. X has precisely
two positive pair forces toward H,K and one positive pair edge
to a genuine leaf L. Thus X has its true degree three, is
physically circle-clear, and its real force/moment equations are
retained. Assume X,H,K all avoid O, K physically touches the
containing circle, and the actual HK contact is radial. H,K may
carry arbitrary other positive forces and original circle loads.

**Radial-triangle theorem.** This entire actual configuration is
impossible.

By Section 1 the physical boundary K is the outer endpoint of
HK. Write its unchanged contact as

    p=t e, 1<t<=d,
    H subset {x:e.x<=t}, K subset {x:e.x>=t}.           (7)

H is physically circle-clear, as a geometric fact. X has a real
S leaf and d>1 by Section 3. Put e_L for its actual leaf direction
and alpha>0 for the leaf force magnitude at X.

Write n from H to X and m from X to K, with original magnitudes
mu,nu>0. The genuine complete X equation is

    alpha e_L=mu n-nu m.                               (8)

No equation at K consisting of two forces is used. K's only load
premise in the local proof is physical circle contact.

The two physical normals at H in triangle H,X,K cannot be
parallel. Opposite signs prevent its neighbors from touching.
Equal signs would make n=e and put all of X in e.x>=t>1,
contrary to (6). Hence their actual geometric concurrence exists
on the radial HK line:

    q_H=h e, h<=t.                                    (9)

All proper-port statements in this section are the purely physical
triangle fact of RADIAL_TRIANGLE_CONCURRENCE.md Section 1. They
do not require zero external moment at H or K relative to this
triangle, which may fail when it is a face of a larger block.

## 5. The complete X-pair cover forces h<0

### 5.1. Nonparallel X: its concurrence is on the positive leaf ray

Let q_X=q e_L be the genuine nonparallel X concurrence. Torque
at X and its real radial leaf gives this proportionality for a
real scalar q. It is strictly positive.

To see this, X contains d e_L and avoids O, so convexity makes
it avoid the entire nonpositive e_L ray. If q<=0 and one actual
proper length at X vanished, q_X would belong to X, a contradiction.
If both lengths a_1,a_2 were positive, the convex combination
of its actual ports with weights proportional to mu/a_1,nu/a_2
would be

    q_X-(alpha/W)e_L=(q-alpha/W)e_L in X,
    W=mu/a_1+nu/a_2>0.

This is again on the forbidden nonpositive ray. Thus q>0. This
argument used only the real X equation and physical properness.

Suppose first the K pair is also nonparallel. Its geometric
concurrence is q_K=k e with k>=t>1 by properness on KH.
At HX and XK the proper relations give

    q_X-q_H=lambda n, q_K-q_X=eta m,
    lambda,eta>=0.                                    (10)

The directions e_L and e are independent. If they were parallel,
all three concurrence points would be collinear. Any nonzero
difference in (10) would make its force direction parallel to e;
equation (8) then makes the other direction parallel too, contrary
to the present nonparallel X pair. The only other possibility is
q_H=q_X=q_K=p. Then both original X cycle ports equal p, and their
positive sum -alpha e_L is an outward normal at p. If e_L=-e,
this contradicts q_X=q e_L with q>0 and p=t e. If e_L=e, the
point p minimizes e_L on X while d e_L maximizes it. Its width
would be d-t<1, impossible for a unit square. Thus independence
holds, and lambda,eta are strictly positive in (10).

Substitute (10) into (8) and compare the independent e coefficient:

    (mu/lambda)h+(nu/eta)k=0.

Since k>0, this proves h<0.

If the K pair is parallel, its outward normals toward H and X
must have the same sign. Hence m=e. Equation (8) becomes
mu n=alpha e_L+nu e. Nonparallelism at X makes e_L,e independent.
The HX proper relation is q_X-q_H=lambda n with lambda>0.
Comparing its e coefficient with the last force identity gives

    h=-lambda nu/mu<0.

This covers the entire parallel K domain without assigning K a
finite concurrence or a degree-two equation.

### 5.2. Parallel X, with both original wall means retained

The two X outward cycle normals have the same sign and equal
-e_L by (8). If X is tilted to its real S leaf, both applications
are its unique far vertex. Their actual zero origin moment makes
the two inward leaf-frame components equal, placing that vertex
at radius sqrt(2)-d<r. For this last strict inequality,
sqrt(2)-d<10/7-91/100=363/700<14/25<r.
It cannot belong to the physical boundary K.
Thus the parallel X is aligned:

    X=[d-1,d]e_L+[ell,ell+1]Je_L, -1<=ell<=0.

Both actual X wall applications have e_L coordinate d-1. Their
transverse heights have a positive weighted mean zero. K's point
cannot have height zero, since its norm would be d-1<1/60<r.
Thus the two heights have strictly opposite signs.

K cannot also be parallel. Its two outward normals would imply
e_L=-e, making H's two outward normals opposite, which was already
excluded in Section 4. Hence q_K=k e, k>=t>1, is well defined.
Properness at H and K toward X shows that their concurrences have
the same Je_L coordinates as their respective actual X wall ports.
Those coordinates are h(e.Je_L) and k(e.Je_L). They have strict
opposite signs, while k>0, so again h<0.

Sections 5.1--5.2 exhaust the actual X and K pairs and give

    q_H=h e, h<0.                                    (11)

## 6. Every aligned X contradicts the actual small H port

For an aligned genuine S root X, the entire X-only physical-
triangle feature calculation in
GLOBAL_CLOSURE_TWO_TRIANGLE_TIP_LEAVES_HUB_CLEARANCE.md Section 3
uses only the real three-force X equation and the other body's
physical boundary point. It does not use that body's degree-two
equation. Apply that calculation with the actual boundary K.

Explicitly, parallel X pairs are westward and have opposite-height
original wall means. In a nonparallel pair an X-owned vertical
axis contradicts the physical nonobtuse-normal lemma and vertical
balance; a horizontal axis would make the pair parallel. The two
strict contacts are therefore its left vertices, with opposite
actual heights. They cannot be opposite vertices, and right
vertices cannot balance the true eastward leaf. Reflect so K's
height is y>0 and H's z<0, with y-z<=1.

Since |d-1|<9/100 and every boundary point has norm at least r,

    y^2>(14/25)^2-(9/100)^2>(11/20)^2,
    |z|<9/20,
    |p_HX|^2<(9/100)^2+(9/20)^2=1053/5000<1.          (12)

On the other hand choose an own axis u of the origin-free H
whose interval is [a,a+1], a>0. Its radial support in (7) has
u coordinate a+1>1, so e.u>0. By (11), q_H.u<0. Properness
at H gives p_HX=q_H+b n with b>=0. Because p_HX.u>=a>0,
one has b>0 and n.u>0. The actual HX port must therefore be
on H's far u face:

    p_HX.u=a+1>1.                                     (13)

This contradicts (12). It covers all original aligned sliders,
parallel means and endpoint-valued applications at X.

## 7. Every tilted X contradicts the exact two-neighbor center cap

It remains a tilted genuine S root. Section 5 already proves
its pair is nonparallel with q_X=q e_L, q>0. Write its true
leaf chart

    X=d e_L+[0,1]u_X+[0,1]v_X,
    u_X.e_L=-a, v_X.e_L=-b,
    a>=b>0, a^2+b^2=1.

Its own coordinates are [0,1]^2 and q_X has own coordinates
((d-q)a,(d-q)b). If q>d, both are negative. Properness then
excludes every side-axis contact, since its unchanged other
coordinate would be negative. At either adjacent vertex the
vector from q_X has the wrong strict normal sign. The real leaf
vertex cannot belong to another unit: its S leaf fills a local
half-plane there, while tilted X leaves two sectors each narrower
than a unit's right-angle tangent cone. Only the far vertex remains.

Both cycle ports would therefore be that far vertex. As in
Section 5.2 the real X moment makes a=b and its radius
sqrt(2)-d<r, impossible for the actual boundary K. Hence

    0<q<=d.                                           (14)

This is the complete pure X feature argument before any
intact-petal support estimate; K's true higher degree is retained.

Use the same own axis u of H as in (13). Properness at X on
the HX edge gives q_X=p_HX+c n, c>=0. Since n.u>0,

    q_X.u>=p_HX.u>1.

By (14), e_L.u>1/d. The actual S leaf center therefore satisfies

    c_L.u=(d+1/2)e_L.u>(d+1/2)/d>91/61>L_*.           (15)

The unchanged radial HK support has t<=d and t e.u=a+1>1,
so e.u>60/61. K's center has c_K.e>=t+1/2>3/2 and norm<M.
Exactly the calculation in Section 2 gives

    c_K.u>L_*=3501/2440.                              (16)

Both actual distinct centers c_L,c_K lie in the same cap rectangle
of squared diameter (5), strictly below one. This contradicts
physical interior disjointness. The tilted alternative is excluded.

## 8. Complete local conclusion and retained scope

The radial-triangle theorem used only the true three-force leaf
root X, physical K boundary contact, the actual radial HK support,
and radius-free properness for the physical triangle. H and K
retained every additional force. In particular K may be a genuine
loaded degree-three diamond hub; no part of its circle load was
split and no third hub force was dropped.

Both finite-concurrence and parallel alternatives, all side means,
all proper-length endpoints and both leaf-root frame types are
covered. An actual outside unit containing O openly supplies the
required origin avoidance of X,H,K in the intended block caller.

This source does not by itself assert a whole diamond or mixed-
cell closure; the original graph, private loads and remaining
nonradial moment cases need their separate exact assembly.

No numerical pose, modified physical stress, new selected normal,
reset application, physical motion, Lean compilation, CI, remote
write or shared-ledger edit is used.
