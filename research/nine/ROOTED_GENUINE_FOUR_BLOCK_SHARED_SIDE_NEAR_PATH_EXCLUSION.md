# A genuine four-block excludes a near parallel neighbor with an outside boundary path

Date: October 27, 2026.

**Status: complete proposed geometric-port extension and whole parallel-
frame caller, frozen for full root and separate independent review.**
No original force application is moved. No ledger or remote is changed.

Keep the common canonical nine-square packing and its compatible
selected physical certificate, with the same global atom/body selector.
Assume

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60.

Let Q0 be a genuine terminal four-body block at H, retaining all its
original private degrees, loads and means. H has arbitrary further
forces and O belongs to int H.

## 1. Exact geometric-port theorem

Suppose HX is an actual positive edge outside Q0, and H,X share a
nontrivial physical side segment I. The segment lies on an actual
own H side with positive support height sigma<=epsilon.

Suppose some point p of the closed segment I satisfies |p|<3/8.
The original positive HX application p_0 may be elsewhere in I.
It is not replaced by p in any force or moment equation.

Suppose an actual simple positive path

    H-X-X2-...-L

has every vertex after H outside Q0's private vertices, and L is
a distinct physical boundary unit. No degree, load, equation or
concurrence is imposed on any path vertex.

**Theorem.** This configuration is impossible.

This extends the geometric routing point in
ROOTED_GENUINE_FOUR_BLOCK_SHALLOW_SMALL_OUTSIDE_PATH_EXCLUSION.md,
SHA256 af48df7728a18b20f7c3bc0f305bca95762266b6d1fc34cf32e51d5ae912de8c.
That frozen source itself requires the original HX application
to be the small point. The separate argument below removes that
requirement only for an actual shared side.

## 2. A simultaneous physical embedding may cross the shared side at p

First choose a point p' in the relative interior of I sufficiently
close to p that

    |p'|<3/8.

This is possible even if p is an endpoint of I. Both H and X contain
one side of a full neighborhood of p', so their union contains that
neighborhood. No third interior-disjoint actual unit can contain p',
or any relative-interior point of I.

Represent the one graph edge HX by the segments from c_H to p'
and from p' to c_X, with an arbitrarily small compatible smoothing
near p'. This is a geometric representative of the same positive
body-pair edge, not a different positive contact row.

To see that this representative is compatible with the entire
selected embedding, use the usual radial center-to-boundary stars
inside every actual convex square. Distinct boundary points give
disjoint open radial segments except at their common center.
No other H or X neighbor has an application in the relative
interior of I, by the neighborhood observation above. Thus the
new HX segments cross no other edge inside H or X.

All remaining multiple physical junctions retain the same small
compatible occupied-sector routings as before. Endpoint interactions
with H or X are left at their original actual points. A shared-side
HX interaction is between adjacent occupied sectors, so moving its
geometric crossing into I introduces neither missing opposite
diagonal at a four-unit junction. The selected body-pair graph and
all its outside boundary-access spokes stay unchanged.

Equivalently, the full simultaneous physical embedding can be
constructed from the outset with the HX crossing at p'. It has
the same actual square centers and graph edges and every original
circle-access corner. Its geometric drawing does not determine
the physical force means.

In particular the actual scalar atoms, original unit normal and
aggregate application p_0 are still those of the selected stress.
All private force and moment arguments below use those unchanged
data. Only the topological HX branch is drawn through p'.

## 3. The complete genuine-Q0 and circle-order proof still applies

Use the exact full Q0 mask cover in Sections 2--3 of af48df77.
Selected K4, tip-root diamond, empty and sole-adjacent C4,
sole-opposite C4 and adjacent-two C4 have their complete original
exits. A genuine opposite-two C4 is excluded by the full shallow
open-origin theorem. The remaining Q0 is either an all-three-load
C4 or a hub-rooted diamond.

Its two actual loaded degree-two endpoint tips are B,C, with an
actual physical boundary path B-J-C between them. J retains its
true degree two or three. No path vertex outside Q0 is B,C or J.

Choose the transverse sign on the actual shallow own face so that

    H=[sigma-1,sigma] times [-w,1-w], w>=1/2.

The full shallow-strip extraction gives w>16/25 and, after naming
the endpoint tips,

    0<=p_HB,x<=sigma, p_HB,y<-16/25;
    p_HC,x<0.

These remain the original positive force applications, not points
chosen for this topological extension.

The geometric HX crossing p' is on x=sigma with transverse height
between -3/8 and 3/8. It is therefore distinct from both of these
actual Q0 ports, with the same counterclockwise root order

    HX, HC, HB.

Restrict the one simultaneous embedding of Section 2 to the tree
with branches H-X-...-L, H-C, H-B. It gives the same actual
circle-access order L,C,B as the complete proof of af48df77.
Consequently the boundary path B-J-C runs clockwise, and the true
B2 moment equation gives

    det(p_HB,n_HB)<0.

This last equality uses only the original B circle load and its two
original pair applications. The HX force or its moment is never
used to identify this sign.

The complete local theorem
ROOTED_SHALLOW_NEGATIVE_MOMENT_BOUNDARY_TIP_EXCLUSION.md,
SHA256 6b1dd09bdb8fca98335d5df992a2fa400818296d00ca3f33798cf240be9cb245,
now excludes that actual shallow B port with its boundary neighbor J.
The proof retains the complete J3 when Q0 is a diamond.

This proves the geometric-port theorem, including every original
Q0 mask and all actual side endpoints.

## 4. A parallel-frame near neighbor always supplies the geometric port

Add the assumptions that X and H have parallel actual square frames,
that they physically touch by their original positive edge, and

    X meets the closed D_epsilon.

We prove that this entire situation is impossible whenever X has the
outside positive boundary path of Section 1.

If the contact contains a segment of positive length, choose the
normal to that actual shared face, with H on the lower side.
In the common own axes,

    H=[sigma-1,sigma] times I_H,
    X=[sigma,sigma+1] times I_X,
    0<sigma<1, 0 in int I_H.

Both transverse intervals have length one, and I_H intersect I_X
has positive length. Because X meets D_epsilon, its actual distance
from O is at most epsilon. The point of X closest to O is

    p=(sigma,y_*),

where y_* is the closest point of I_X to zero. In particular

    0<sigma<=epsilon, |p|<=epsilon<3/8.

Moreover y_* belongs to I_H. If I_X contains zero, this is immediate.
If I_X is strictly positive, its lower endpoint y_* cannot exceed
the upper endpoint of I_H because the intervals meet, and the
lower endpoint of I_H is negative. The negative case is the same
argument with signs reversed. Thus p belongs to the actual closed
shared segment. Sections 1--3 apply, whatever the original HX mean.

If the contact is a single point, parallel unit frames make it a
common corner P: X occupies the outward quadrant at that H vertex.
Since O is strictly inside H, P is the unique nearest point of X
to O. Therefore

    |P|<=epsilon.

The original application is necessarily P. Both incident own H
face heights are positive and at most |P|<=epsilon. Choose either
one; it contains the same actual positive HX point. The original
af48df77 theorem applies directly, without any geometric rerouting.

These are all parallel-frame contacts between interior-disjoint
actual unit squares. No selected force line, leaf type or neighbor
degree was needed.

## 5. Exact uses and limits

The complete result permits a genuine leaf at an arbitrary-degree X:
its actual positive path H-X-L supplies the outside boundary path.
It therefore applies to a privately decorated hub as well as a tip,
provided its real closed epsilon-disk intersection and parallel
H/X frames are separately established.

The proof does not assign a stress force at the geometric point p'
or change an endpoint atom. It retains the original support-minimal
certificate and its compatibility. All equations inside Q0, including
the true private K3, are unchanged.

For oblique H/X frames with only one actual contact point, the
geometric-port extension does not move that point to a nearby face.
Such a caller must still establish a small actual point by its own
full physical argument. No complete two-private-leaf graph or
C2.44.b2 cell is claimed here.

