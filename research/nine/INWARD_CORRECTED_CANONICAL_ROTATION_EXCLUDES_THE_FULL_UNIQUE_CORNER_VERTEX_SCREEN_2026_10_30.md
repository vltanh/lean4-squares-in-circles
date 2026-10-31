# An inward correction removes the complete radial-diagonal rotation survivor

Date: October 30, 2026. Author: common-certificate continuation.
Input mathematics unchanged from `26804c07`; live continuation head
reported as `3132896f` adds only the progress note.

**Status: complete proposed uniform hand exclusion, awaiting separate
full-source review.** This proof finishes the entire full-screen family
of the previous one-body canonical rotation theorem. It is independent
of the positive degrees, circle masks and other forces of the two
neighbors. Screened additional physical contacts, including zero-weight
ones, are also included. No original inventory flag changes here.

The old rotation alone made the center move outward to second order.
Adding an explicit inward translation makes every screened contact open
while strictly decreasing the actual center norm. The construction is
an exact physical motion, not merely a first-order velocity test.

## 1. Complete original scope

Fix the same finite original packing, first minimizing its containing
radius R and then `Phi=sum_i |c_i|^2`. Assume `R>sqrt(2)`.
Retain the original physical force-and-torque certificate.

Let S be a loaded square with exactly two original positive body-pair
forces, both nonzero, and exactly one physical circle corner z, with
its actual positive coefficient. Its two original force lines are
nonparallel. Assume their proper concurrence is

    q=tau*z in S, 0<tau<=1,
    p_i-q=alpha_i*n_i, alpha_i>=0,

where the applications and outward normals are the original ones.
In the project radius window this properness is supplied by the local
two-force theorem after its true-degree and nonparallel premises are
established. No such local theorem is extended beyond its printed
radius range: properness is an explicit premise here.

Impose the complete actual-contact screen of the preceding rotation
theorem. For every physical neighbor T of S, including every neighbor
whose original edge weight is zero, there is an actual fixed separator
normal n_T outward from S which uniquely exposes its contact vertex
p_T, and

    p_T-q=alpha_T*n_T, alpha_T>=0.

At the two positive neighbors these are their original applications
and selected normals. All other actual squares remain in place.
This screen excludes a shared segment and any contact at which S owns
a side. It does not infer absence of an extra contact from its zero
coefficient. Exactly two actual neighbors is a sufficient special case
when both positive contacts satisfy the stated vertex condition.

**Theorem 1.** No such original canonical packing and screened loaded
body exist. In particular, the radial-diagonal alternative left by the
preceding one-body theorem is completely excluded at this full scope.

## 2. The exact preceding necessary geometry

For clarity, recall how the prior necessary geometry follows. Rotate
S about q by an angle theta and keep every other square fixed. At
each screened contact, its same uniquely exposed vertex remains exposed
locally and its support displacement is

    alpha_T*(cos(theta)-1)<=0.

Thus every actual contact remains separated. Noncontacts have positive
compact-set distance. At the unique circle corner the exact formula is

    |q+Rot_theta(z-q)|^2
      =R^2-2*tau*(1-tau)*R^2*(1-cos(theta))<=R^2.

The other three corners are strictly inside. This is a full feasible
two-sided physical motion. With

    A=q.(c-q), B=det(q,c),

its Phi difference is `2A*(cos(theta)-1)-2B*sin(theta)`.
Canonical minimality gives `B=0` and `A<=0`.

Put `sigma=1/sqrt(2)` and `e=z/R`. Since q is a positive multiple
of z, `B=0` makes c radial as well. The corner distance sigma and
disk containment force

    r=R-sigma, c=r*e, z=(r+sigma)*e,
    q=(r+delta)*e, 0<=delta<=sigma.

Here `A<=0` gives `delta>=0`, and membership of q in the same
actual square gives `delta<=sigma`. The outer circle vertex cannot
be shared: the short inward radial segment from a contained circle
corner lies in that square's open interior, so two squares sharing
it would overlap.

The two positive applications are uniquely exposed vertices. They
cannot coincide because their proper normal lines would then be
parallel. If one were the inner radial vertex, its outward force
would be radial; the positive circle force and the remaining pair
force would then force the second normal to be radial too. Therefore
the two positive applications are the two opposite lateral vertices.
Their exact original geometry is

    p_+=r*e+sigma*Je, p_-=r*e-sigma*Je,
    alpha=sqrt(delta^2+sigma^2),
    n_+=(-delta*e+sigma*Je)/alpha,
    n_-=(-delta*e-sigma*Je)/alpha.

Strict vertex exposure gives `delta<sigma`. The transverse force
equation equates the two positive magnitudes. Its radial equation and
the strictly positive circle coefficient then give `delta>0`.
Consequently

    0<delta<sigma<r.                                      (1)

The last inequality is exactly the present lower radius assumption
`R>sqrt(2)`. These are the unchanged original points and normals;
they are not a new contact selection.

## 3. The corrected actual motion

Write `u=1-cos(theta)`. Rotate S about q and then translate it inward
by `2*delta*u` in the radial direction:

    S_theta=q+Rot_theta(S-q)-2*delta*u*e.                  (2)

Every other original square stays fixed. We show that (2) is feasible
for both signs of every sufficiently small theta and strictly lowers
Phi whenever theta is nonzero.

### 3.1 The two positive contacts strictly open

At either positive lateral port the support displacement in its same
original normal is

    -alpha*u-2*delta*u*(e.n_+)
      =(-alpha+2*delta^2/alpha)*u
      =((delta^2-sigma^2)/alpha)*u<0,                    (3)

and the same formula holds for n_-. Translation does not affect which
vertex is exposed; strict exposure under the small rotation persists.
The original fixed neighbor still lies on the other side of its
original supporting line. Hence the whole two squares remain separated,
with a strict gap at each formerly positive contact.

### 3.2 Every screened zero-weight contact also strictly opens

There are only three non-circle vertices of the same radial square.
At either lateral vertex, the screen `p-q=alpha_T*n_T` forces exactly
the same corresponding normal and coefficient as in (3). Thus (3)
also handles every extra screened contact there.

At the inner vertex `p_0=(r-sigma)*e`, the screen forces

    n_T=-e, alpha_T=sigma+delta.

Its corrected support displacement is exactly

    -(sigma+delta)*u+2*delta*u
      =-(sigma-delta)*u<0.                              (4)

The remaining outer vertex is the unshareable circle corner. This
exhausts every actual contact allowed by the full screen. No favorable
sign of a supplemental normal has been assumed without checking the
actual vertex and its proper ray.

### 3.3 Every circle and noncontact constraint remains valid

The unique circle corner under (2) is

    z_theta=(R-(sigma+delta)*u)*e
              +(sigma-delta)*sin(theta)*Je.              (5)

Direct expansion gives

    |z_theta|^2-R^2
      =-2*[R*(sigma+delta)-(sigma-delta)^2]*u
         +4*sigma*delta*u^2.                             (6)

The bracket is positive. In fact `r>delta` implies
`R>sigma+delta`, so it is strictly greater than `4*sigma*delta`.
Because `0<=u<=2`, (6) is strictly negative whenever `u>0`.
Only a neighborhood of zero is needed. The other three actual
vertices begin strictly inside the disk and remain so by continuity.
Convexity of the disk then contains the entire square.

Every original square not touching S has positive distance from S
and stays disjoint under sufficiently small motion. Pairs not involving
S are unchanged. Intersecting finitely many neighborhoods with those
for strict exposed-vertex labels verifies all original constraints
for both signs of theta. Extra physical squares are not discarded.

## 4. The actual secondary objective decreases exactly

The center of (2) is

    c_theta=(r-delta*u)*e-delta*sin(theta)*Je.

Using `sin(theta)^2=2u-u^2`, its squared norm satisfies the exact
identity

    |c_theta|^2-|c|^2=-2*delta*(r-delta)*u.                (7)

Every factor on the right except the leading sign is positive for
sufficiently small nonzero theta by (1). All other centers are fixed.
Thus (2) remains in the same radius-R packing space while strictly
decreasing the original Phi, a contradiction. Theorem 1 follows.

The correction is essential: the uncorrected rotation alone raises
Phi in the radial-diagonal alternative. The explicit translation in
(2) fits within the strictly positive second-order separation at all
screened ports, as (3)--(4) verify with their original normals.

## 5. A mixed-mask ownership consequence for every no-long C7

This corollary retains its own complete physical hypotheses and does
not assert that every original C7 satisfies them.

In the same original radius/Phi-minimizing packing, suppose an entire
positive simple C7 has `t` loaded vertices and
`k=7-t` isolated unloaded transmitters. Let `s` count loaded bodies
with two physical circle corners, and let `d_D` count its diagonal
transmitters. Assume every physical-unique loaded body has exactly its
two positive cycle neighbors as actual neighbors and satisfies the
nonparallel proper two-force premises above. Assume all seven original
positive contacts are physical singletons and retain the original
strict point-normal convention.

A physical-unique loaded body cannot supply strict vertices at both
its positive contacts: that would meet the full screen of Theorem 1.
It must therefore own a side at at least one of its two contacts.
Each side transmitter owns sides at both original positive contacts.
At a singleton under the stated convention at most one endpoint owns
a side; the other endpoint supplies a strict vertex. Every contact
is counted as only one edge, and vertex/vertex edges contribute no
owner incidence.

Counting these required incidences gives

    (t-s)+2*(k-d_D)<=7=t+k,
    hence s+2*d_D>=k.                                   (8)

No condition has been imposed on the individual two-circle weights;
s counts physical masks and retains zero coefficient endpoints. The
consequence in the all-side no-long cases is the whole-mask reduction

| Positive loads t | Isolated transmitters k | Required two-circle loads s |
| ---: | ---: | ---: |
| 4 | 3 | at least 3 |
| 5 | 2 | at least 2 |
| 6 | 1 | at least 1 |

With one diagonal transmitter, (8) remains the exact corresponding
count. A positive shared segment would allow both bodies to own the
same side direction and is expressly outside this singleton count.
An unscreened additional actual contact at a physical-unique loaded
body also remains a genuine separate alternative.

Thus the result excludes complete screened-star features even when
their neighbors have two physical circle corners, and it places all
three no-long C7 load patterns under one necessary mask inequality.
It does not claim closure of every remaining two-circle mask.

## 6. Exact sources and verification boundary

| Source | SHA-256 | Use |
| --- | --- | --- |
| `CANONICAL_ROTATION_OF_UNBLOCKED_UNIQUE_CIRCLE_TWO_FORCE_BODIES_2026_10_30.md` | `94f4d2ed11af153196d7e68644c5a21b0f3e4619abcb2b042d54a00d1450bda3` | Complete original-contact rotation screen and its exact necessary radial-diagonal geometry, reconstructed in Section 2. |
| `ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md` | `be6636a018df64f52a48f382dc21b453a208d0a929fdeaa7cb5bef9c30822c06` | Original `(R,Phi)` minimum and its full-packing comparison domain. |
| `FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md` | `7d0c4092ba133a832cf963f329b1c3a6442a3260576f16319293835b39e6d282` | Project-window nonparallel proper two-force caller, with no boundary-neighbor premise. |
| `PHYSICAL_CONTACT_STRESS.md` | `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5` | Full original force, moment and actual-application conventions. |

All four operative sources were read in full during this continuation.
The correction, every extra screened port, the exact objective change,
and the ownership count are proved above. Neither a side application
nor a variable shared mean is frozen to a vertex. The second physical
circle corner at any neighbor remains untouched and may have zero
weight. No post-extraction normal change is made.

This is a hand theorem. No numerical pose search, mesh, computational
packing certificate, Lean/Lake compilation, CI, original inventory
mutation, or remote publication is used or claimed.
