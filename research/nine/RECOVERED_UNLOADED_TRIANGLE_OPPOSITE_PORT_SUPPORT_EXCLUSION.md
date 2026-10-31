# A touching-return star excludes opposite ports of its actual third neighbor

Date: October 28, 2026 UTC. Author: root continuation.

**Status: newly reconstructed and strengthened radius-free hand theorem,
submitted for fresh independent review.** This is not a byte restoration
of the historical source at hash
`50272f234a1fcc8fc535e50ffb21a17e7790826d9f8ad5cd43ec168e76f89661`.
No historical review is represented as a review of these new bytes.

## 1. Complete physical interface

Retain actual interior-disjoint closed unit squares A,B,C,D,T. The
unloaded square A has exactly the three original positive neighbors
B,D,T. The actual squares D,T physically touch. The actual pairs
B,C and C,D also physically touch, with B,C carrying its unchanged
original positive normal and application. The other true degrees,
loads, forces, circle masks, individual weights, and all additional
physical contacts are arbitrary and are retained.

Let n be the actual B-to-A unit normal, with unchanged application P.
Let m be the actual B-to-C unit normal, with unchanged application Q.
Assume

    n.m<=0,                 n.(P-Q)>=1.                 (1)

Then this complete physical configuration is impossible. No circle,
radius, origin, side ownership, generic-normal, or special mean
hypothesis is imposed.

The proof also gives a useful owner implication: if B owns its
original B-to-A normal n, then its original B-to-C normal must satisfy

    n.m>=0.                                              (2)

This implication does not change a normal at B and does not require
B to be unloaded or to have any particular degree.

## 2. Complete weak unit reach at a supported point

Let Q be any actual minimum-m support point of a unit square K, and
let n be a unit vector with n.m<=0. Then

    n.(z-Q)<=1 for every z in K.                         (3)

At a vertex, let e,f be its inward orthonormal edge directions. Their
m components are nonnegative. Both n.e and n.f cannot be strictly
positive: otherwise expanding n.m in this frame would make it
strictly positive, since at least one m component is positive. Thus
at most one inward edge contributes a positive n component, and
that component is at most one. Every z-Q is an independent convex
combination of e and f, which proves (3).

At a side-interior point, write z-Q=s*m+t*Jm with 0<=s<=1 and t
in the unchanged actual tangent interval of length one containing
zero. The normal contribution is nonpositive; the positive tangent
contribution is at most one. Side endpoints are covered by the
vertex proof, or the same closed interval argument.

If n.m<0, (3) is strict. For a vertex, equality would require an
inward edge to be exactly n, contradicting its nonnegative m
component. For an interior side point the transverse component
has magnitude strictly below one. This strict refinement is not
needed in the closed-endpoint theorem (1).

## 3. Apply the unchanged A support and the unchanged C support

The complete all-normal touching-return theorem applies at the true
unloaded A3 with third neighbor B and return pair D,T. Its original
A-to-B normal is -n, at the same physical P. Therefore

    (-n).z<(-n).P for every z in D union T,

or equivalently

    n.z>n.P for every z in D union T.                    (4)

The actual C has minimum-m support at its original Q. Equations
(1) and (3) give

    n.z<=n.Q+1<=n.P for every z in C.                    (5)

The whole closed C lies in the closed half-plane (5), whereas the
whole closed D lies strictly in the opposite half-plane (4). Hence
C and D have no common point, contrary to their actual contact.
Singleton contacts, side endpoints, and positive shared segments
are all excluded by the same strict separation.

## 4. Owned-face consequence at B

Suppose B owns n and n.m<0. Rigidly normalize B=[0,1]^2 and n=East.
Its unchanged BA application P has x=1. The negative x component
of m forces its unchanged BC application Q onto x=0, regardless
of the other component, the support owner at C, and every mean
endpoint. Therefore n.(P-Q)=1, and the complete theorem applies.

Thus every surviving owned-face configuration must have n.m>=0,
as asserted in (2). Equality is not automatically excluded: it
needs the actual port-gap condition in (1). No whole original
family is marked closed solely from this necessary condition.

## 5. Literal broad applications and limits

The lower-house graph AT,DT,AD,AB,BC,CD,BL supplies exactly the
interface in Section 1 with the genuine A3, its actual triangle
TD, and its original B3 and D3 forces. The real leaf BL, all
three completing squares, and the full nine-square packing stay
present. The theorem applies at every radius and every leaf type
whenever (1) holds; its owned-face consequence applies at every
radius without a port estimate.

More generally B,C,D,T can have arbitrary true degrees, provided
A remains the true unloaded three-force star and the two physical
return and cross contacts really exist. The conclusion does not
create a nonexistent C-D edge, aggregate a higher-degree A, or
assume all of B's other forces have a common application.

## 6. Operative source and verification boundary

The only nontrivial geometric input is the complete theorem

`UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md`,
SHA256
`406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87`.

I reread its complete all-normal feature proof before this
reconstruction. It uses its exact perpendicular-axis input at
SHA256 `6630675274998befc40e87bfe67e15f0bdf0d74b7b814f82ccbc42b71dea4b24`.
The complete mean and equality coverage required here is supplied
by those original proofs. The weak reach lemma in Section 2 is
proved in full above, so the extension n.m=0 is explicit.

No force or normal is deleted, no shared mean is replaced, and no
completion square is omitted. No numerical pose, compilation, CI,
ledger credit, or remote action is part of this manuscript.
