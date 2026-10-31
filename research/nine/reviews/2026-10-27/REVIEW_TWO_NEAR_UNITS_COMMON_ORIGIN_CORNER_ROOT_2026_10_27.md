# Root full review: two actual near units at one origin corner

Date: October 27, 2026.

**Verdict: PASS for the complete physical lemma and its exact conditional
owner reduction.** No whole original graph or ledger cell closes here.

The entire reviewed source is
GENERAL_TWO_NEAR_UNITS_AT_ONE_ORIGIN_CORNER.md, SHA256
`682b48f2f82b6ae35bfc7ef1a5efa900942fc115f2485048385c5b3403de151d`.
Sections 1–3 are self-contained. Section 4 uses the already fully
reviewed GENERAL_SMALL_ORIGIN_CORNER_CONTACT_KERNELS.md,
SHA256 `b977be65217728c0363e8bab030bdb3d11b1b8ef75cc32d295a8337c4ea01477`,
and its physical input ROOTED_SMALL_ORIGIN_CORNER_TWO_BOUNDARY_NEIGHBORS.md,
SHA256 `6ebda6299f692af6380ad36b98420aeb3155cf95a6b586e1df3848807d4cf467`.
Those exact blobs are unchanged at publication boundary
`8304072dbc91bcbe726d651c10403351f9566853`.

## Complete sector argument

In the inward H frame at its actual corner P, closed-origin containment
gives O-P=ai+bj with both margins nonnegative. If a>epsilon, each
actual near-disk point has strictly positive i displacement from P.
The disk may be closed and its point may be on the near unit's boundary;
the strict inequality still holds.

The disjoint-interior hypothesis excludes any closed point of one
actual square from the open interior of another, by density of the
former interior. Thus P is a boundary point of each near unit and
its tangent sector cannot enter the open first quadrant of H. Its
direction toward its near point consequently lies in (-pi/2,0].

The full actual sector has width pi/2 or pi. In the lift contained
in [-3pi/2,0], its upper endpoint beta is strictly greater than
-pi/2, while its lower endpoint alpha is at most -pi/2. Therefore
the whole nonempty interval (-pi/2,beta) lies strictly inside the
sector. The two near units have a common open interval of such
directions. A sufficiently small positive displacement from their
same physical P would enter both open interiors, a contradiction.
Interchanging the inward axes proves both margins at most epsilon,
and the norm bound follows by orthogonality.

This checks epsilon=0, equality at the disk boundary, a direction
along an H side, and P in the relative interior of a near-unit side.
The proof does not assume the near units avoid O or carry any force.
It does require O in closed H; it makes no origin-free extension.

## Exact small-port and shallow-support cover

A non-owned normal strictly exposes an H vertex. Two such actual
ports of norm below 3/8 must be the same vertex, since distinct
unit-square vertices are at least one apart while the two ports
are less than 3/4 apart. Both original near units really contain
that same point, so the physical theorem gives a corner of norm
at most sqrt(2)epsilon<1/40.

For two H-owned shallow normals, the opposite-axis choice is
excluded by unit width, and different adjacent axes give the same
small-corner conclusion. Two occurrences of the same H-owned side
remain a complete retained case with both original means unchanged.

In the mixed owner case, the non-owned port is an actual H vertex.
It cannot be on the opposite side of the shallow owned face: that
side has distance at least 1-epsilon>59/60 from O, whereas the port
has norm below 3/8. The vertex therefore lies on the shallow face.
This establishes only incidence. It does not make the owned port
equal that vertex, put the owned-contact neighbor at the vertex,
or place the other unit wholly beyond the shallow face. The source
explicitly retains all of these physical possibilities.

## Conditional boundary-neighbor application

When H has two distinct touching physical boundary neighbors, the
accepted b977 physical kernel excludes an actual corner of norm
below 1/40 in the stated critical/high circle range. It needs no
positive circle multiplier or degree premise at either neighbor.
Consequently only the same-side owned/owned and the mixed-owner
interfaces remain under all of the new theorem's explicit near-point,
small-port and shallow-support assumptions.

Neither retained interface is excluded in this source. A graph
caller must establish those assumptions using its true original
stars; the local lemma cannot manufacture them by deleting forces.
There is no new fine ID, original-domain closure or checkbox credit.
No Lean, CI, workflow, physical motion or equilibrium modification
was used in this review.
