# The current tree already supplies one planar physical force-and-torque certificate

Date: October 30, 2026.

Input tree: `4d2b3d62ce489b3251f0241d6c592e868fd7a410`.

**Status: independent current-source reconstruction and scope correction.**
This audit verifies the existing physical certificate construction. It
does not claim a new packing inequality, a newly closed original fine or
coarse cell, the complete G4.2.c audit, or Lean verification.

## 1. The distinction that the latest handoff missed

The caution about `PLANAR_STRESS_CORE.md` is correct: its 19-atom
translational certificate cannot simply be identified with the angular
certificate in `ROTATION_STATIONARY_STRESS.md`. Those two older sources
explicitly decline that identification.

However, the current repository contains a later, separate construction:

1. `PHYSICAL_CONTACT_STRESS.md` obtains one normalized certificate with
   force and angular balance and actual physical application points.
2. `PHYSICAL_BODY_GRAPH_UNCROSSING.md` selects matched free normals before
   extraction and planarizes that same physical certificate while
   preserving all body forces and moments.
3. `UNIQUE_POSITIVE_COMPONENT.md` proves uniqueness of its positive
   component by the physical boundary-port order.

The common-domain source already invokes precisely this later pipeline.
Consequently the existence of a common planar physical force-and-torque
certificate is not an outstanding gap in the current argument. The
remaining G4.2.c obligation is to audit the actual downstream generic
conditions and theorem callers in that common selection. This is a
correction of the location of an open obligation, not closure credit.

## 2. Independent reconstruction of the physical local branch

Let a fixed global minimizer consist of unit squares with centers
`c_i`, local angle variables `theta_i`, and squared radius `q`. Compactness
of the bounded pose space and continuity of the finite separating-axis
disjunction give existence of such a minimizer from a hypothetical
subcritical packing. Use one smooth circle inequality at every corner:

    C_ik = |c_i + a_ik(theta_i)|^2 - q <= 0.

All originally disjoint closed pairs remain disjoint in a sufficiently
small common neighborhood, by positive set distance and finiteness.
Thus only actual touching pairs need active contact rows.

For a physical contact point `p` and common supporting unit normal `d`
oriented from body `i` to body `j`, the desired gradient is

    (d, -d, d . J(p-c_i), -d . J(p-c_j))                     (2.1)

in the two centers and two body angles. The three exhaustive contact
types each have a locally sufficient smooth branch with this gradient.

### Vertex against relative side interior

Let body `i` own the supporting side and let `p=c_j+a_j` be the unique
contacting corner of `j`. The constraint

    1/2 - d_i(theta_i) . (c_j+a_j(theta_j)-c_i) <= 0

is a separator in a neighborhood: the contacting corner uniquely
minimizes the other body's projection at the base point, and this strict
choice persists. If it did not uniquely minimize, the two bodies would
share a positive side segment instead of this contact type. Differentiate
the owner's normal, using `d_i'=Jd_i`; the identity
`-Jd . x = d . Jx` gives (2.1), including the owner's angular term.

### Vertex against vertex, with singleton intersection

The two right-angle tangent sectors have no common nonzero ray, since
such a ray would yield a positive shared segment. Their strict common
normal interval is therefore nonempty. Choose any normal `d` in this
interval before multiplier extraction. The two selected corners remain
unique extremes in a small neighborhood, so

    d . (c_i+a_i(theta_i)-c_j-a_j(theta_j)) <= 0

is a sufficient physical separator. Its derivative at the common point
is (2.1). The chosen normal may remain fixed in this branch; it is not
an owner-axis constraint. The physical derivative is all that is used.

### Positive shared side segment

In local coordinates take the base centers `(0,0)` and `(1,t)`, with
aligned axes and `0<=t<1`. The actual common endpoints are

    p_- = (1/2,t-1/2),    p_+ = (1/2,1/2).

Impose both rows

    B_- = 1/2-u_i . (c_j+(-u_j-v_j)/2-c_i) <= 0,
    B_+ = 1/2+u_j . (c_i+(u_i+v_i)/2-c_j) <= 0.             (2.2)

For `delta=theta_j-theta_i<=0`, the first selected corner is a minimum
of `j` in direction `u_i`, so `B_-<=0` is a genuine separator. For
`delta>=0`, the second selected corner is a maximum of `i` in direction
`u_j`, so `B_+<=0` is a genuine separator. Hence the conjunction is
sufficient for both signs and at the tie. At the base point the two
gradients are exactly (2.1) at the two actual common endpoints. Reflect
the construction for negative `t`; `t=0` retains two actual endpoints.

This branch need not contain every neighboring physical packing.
It contains the minimizing pose and only physical packings locally,
which suffices to inherit local minimality. No unsupported
differentiation of an absolute-value cusp is required.

## 3. Normalized physical equilibrium and atom bound

Use the direction

    dot c_i = c_i,    dot theta_i = 0,    dot q = K

with `K` larger than all `2(c_i+a_ik).c_i`. Every active circle row then
strictly decreases. Every active contact row has derivative

    d . (c_i-c_j) = -h_i(d)-h_j(d) <= -1.

The finite active-gradient alternative therefore applies without an
abnormal multiplier. It yields nonnegative circle weights `lambda_ik`
and physical contact weights `mu_e`, with

    sum lambda_ik = 1,
    2 sum_k lambda_ik p_ik + sum_e s_ie mu_e d_e = 0,
    2 sum_k lambda_ik p_ik . J(p_ik-c_i)
       + sum_e s_ie mu_e d_e . J(p_e-c_i) = 0.               (3.1)

Every positive atom uses an actual common support point or an actual
circle corner. The center dilation is only a constraint-qualification
direction; it is not claimed to lower the packing radius.

At the base pose, every contact gradient (2.1) is orthogonal to

    T=(Jc_1,...,Jc_n,1,...,1,0).

Indeed its center terms are `d.J(c_i-c_j)` and its angular terms are
`d.J(c_j-c_i)`. Circle rows give `2p.Jp=0`. This calculation remains
valid for a fixed-normal singleton row even though that row is not
globally invariant away from the base contact. Thus all active
gradients lie in a subspace of dimension at most `3n` in the `3n+1`
pose/radius variables. Elementary conic thinning preserves (3.1) and
normalization with at most `3n` positive scalar atoms.

The bound for nine bodies is 27 atoms, not the older translational
bound of 19. Shared-side endpoint atoms may subsequently be aggregated
at their true weighted mean; (3.1) is affine in the application point,
so both force and moment are preserved.

## 4. Planarization preserves the same physical equations

At a point common to four squares, four disjoint right-angle sectors
fill a turn. The squares form an aligned `2x2` junction. Let its axes
be `u,v` and its quadrants be SW, SE, NE, NW. Before extraction choose

    n_+ = a u+b v   on SW -> NE,
    n_- = a u-b v   on NW -> SE,
    a,b>0, a^2+b^2=1.                                      (4.1)

These are valid strict singleton normals. A separate parameter can
be used at every physical four-body junction; the two opposite
normals at one junction share the same `a,b`.

Suppose the extracted opposite-edge magnitudes are `mu,nu>0` and put
`s=min(mu,nu)`. Subtract `s` from both. At the same physical point `p`
add the following existing side-endpoint atoms:

| Pair | Direction | Weight |
| --- | --- | ---: |
| SW to SE | `u` | `sa` |
| NW to NE | `u` | `sa` |
| SW to NW | `v` | `sb` |
| SE to NE | `v` | `sb` |

The subtracted and added forces at SW, NE, NW, SE are respectively

    s(au+bv), -s(au+bv), s(au-bv), s(-au+bv).

They agree body by body. All contributions act at the same `p`, so
their moments `f.J(p-c_i)` agree body by body as well. This is the
missing preservation that the older translational rerouting did not
assert. These new atoms already belong to the original physical local
branch because the adjacent full shared sides have endpoint `p`.

At least one crossing opposite pair disappears. Added positive-length
side pairs cannot be opposite singleton pairs at another junction.
Consequently repeating at finitely many junctions terminates without
creating a new crossing elsewhere. Restrict conic thinning to the
then-positive atom universe. It restores the 27-atom bound and cannot
restore a removed opposite pair.

Draw pair edges through their actual applications, with each half-edge
in the corresponding square interior. Distinct square interiors do
not overlap. At a common application point, three sectors support a
triangle and four sectors support the cyclic edges and at most one
diagonal. Small local perturbations therefore give a planar body graph.
They are drawing perturbations, not changes to the physical packing,
normals, means, or equilibrium equations.

Every physical circle corner has an interior spoke to its body's
center and an exterior continuation. A circle corner cannot belong to
two contained squares: if its inward side axes are `w_1,w_2`,
containment implies `z.w_j<=-1/2`, so a short inward radial segment is
interior to that square. Two such squares would overlap. The drawing
perturbations can avoid all the finitely many circle spokes. Hence
every physical circle-touching graph vertex, including a body with
zero circle coefficient, lies on the exterior face.

## 5. Unique component and later minimal-support selection

Summing the circle forces of a positive component gives
`sum lambda_z z=0`. Its positive circle ports therefore have no gap
longer than a semicircle. Two disjoint plane components with boundary
ports cannot have alternating ports: a path between two ports is a
crosscut separating the two boundary arcs. Thus all ports of a second
component would lie in one open gap of the first. A gap of length at
most a semicircle has a strict separating midpoint direction, which
contradicts the second component's zero weighted port sum.

A contact-positive component with no circle weight is impossible:
dot its force equations with the centers and sum. Every positive edge
contributes `-mu_e(h_i+h_j)<0`. An isolated loaded body is handled by
the same port argument or the standard square corner identity when
the radius is greater than the one-square radius. Normalization
therefore leaves exactly one positive component.

One may then minimize the number of positive atoms over the nonempty
family of normalized physical certificates for the fixed normal system
having the same stipulated physical noncrossing properties: local sector
order, all circle-access spokes, and at most one positive opposite pair
at each four-square junction. Alternatively fix an already noncrossing
surviving atom universe and minimize inside it. Abstract graph planarity
alone is not this selection class. Existence uses the well-ordering of
the possible finite
support sizes, not compactness of the multiplier set. Any branch
rescaling or later deletion must continue to use this same physical
atom system and the new actual positive degrees.

This reconstruction checks the structural pipeline. It does not
validate the small-core exclusion theorems used in later applications
of support minimality.

## 6. Exact interface to generic normal selection

The construction works for every choice of strict singleton normals,
subject only to the matching (4.1) needed for the planarization. Thus
it also works on any independently proved nonempty open subdomain of
those parameters. The current global common-domain source constructs
such a product for its four retained nondense prelists.

For a finite list of proper polynomial avoidance conditions in those
parameters, clear their legitimate denominators and multiply the
nonzero numerators. A polynomial ring over a field has no zero
divisors, and a nonzero real polynomial cannot vanish on a nonempty
open box. Hence one common choice avoids them all before extraction.
One may alternatively use the source's algebraic-independence
construction over the countable field generated by the fixed geometry.

Neither argument proves that a proposed polynomial is nonzero after
the actual physical geometry and matching substitutions. Neither
permits a coefficient depending on an as-yet unknown contact weight
or shared-side mean to be treated as fixed geometry. Neither proves
that the four listed nondense rules exhaust every later operative
source without a source inventory. These are genuine downstream
obligations, distinct from existence of the physical planar stress.

The useful audit interfaces for each downstream selector are therefore:

1. Its prelist depends only on fixed physical geometry.
2. Its variables are genuine independent or matched normal parameters.
3. Each avoided polynomial is nonzero on the actual physical branch;
   identically degenerate branches receive separate proofs.
4. No additional nondense interval is presumed compatible without proof.
5. The post-extraction caller has the stated actual degrees, physical
   circle masks, complete force lists and complete shared means.

The generic-choice theorem and physical construction jointly solve
the existence step once these interfaces hold. A new proof of
planar torque stress is unnecessary for each local family.

## 7. Correct current boundary

**Verified existing structural result:** a hypothetical subcritical
packing yields a minimizer and one selected normalized, planar,
physical force-and-torque certificate, with at most 27 atoms and a
unique positive component. Every one of the nine physical squares
remains in the packing.

**Still open:** the complete downstream G4.2.c audit; the original
140 fine and 22 coarse sharp/completion obligations; the unrestricted
sharp-radius assembly; equality classification; and Lean verification.

No original inventory identifier or checked flag changes as a result
of this audit. The current handoff should distinguish the old separate
certificates from the already available later common certificate,
while retaining the downstream audit as open.

## 8. Exact input pins

All listed files were read from the materialized input tree.

| Source | SHA-256 |
| --- | --- |
| `SPARSE_MINIMIZER_STRESS.md` | `b182276dace03bf64d9903145e8861022712b05f7ff7317ad62f30f97850e9ac` |
| `PHYSICAL_CONTACT_STRESS.md` | `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5` |
| `PHYSICAL_BODY_GRAPH_UNCROSSING.md` | `bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe` |
| `UNIQUE_POSITIVE_COMPONENT.md` | `a971b4f2925c28be1d1e528d3bb01bf0c325e8de87675fe9a114416fab28380c` |
| `GLOBAL_COMMON_NORMAL_DOMAIN_AFTER_FORCE_FREE_C7_AND_ALGEBRAIC_SELECTION_2026_10_29.md` | `557d3f5904a6ba09250a2167c6495cf3555d02536cf016a5ee09c0ccf84cfb20` |
| `GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md` | `39aa9e31a6de4ecdff535a8136f5c3330e6bb653903951fde812ee522d128d4a` |

The full nondense geometric prelists and all downstream caller
dependencies are not re-certified by these pins or by this audit.
No numerical pose search, angle mesh, Lean compilation or CI was used.
