# Full independent review of the fresh straddling-support-port exclusion

Date: October 27, 2026.

Reviewer: rooted_blocks. **Decision: ACCEPTED, with no correction.**

## 1. Exact source and scope

I read the whole source
`CLOSE_SUPPORT_PORTS_STRADDLING_NORMALS_FRESH_EXCLUSION.md`, SHA-256
`f3c83072e2e09bc844bbd1a79813ab76b7979d008980ce9b2be07f25b85811d2`,
and independently derived its complete supporting-feature argument and
corner comparison. The theorem is self-contained; it imports no earlier
normal-selection, stress, concurrence, circle-mask, or pocket theorem.

The conclusion is exactly the stated physical impossibility for one
contained actual unit square with two actual ports P,Q. Their original
outward normals must have positive horizontal components, strictly
opposite vertical components, and strictly positive dot product. The
actual distance is less than one; both actual x coordinates are less than
−29/30 and both actual absolute y coordinates are less than 1/4.

These hypotheses do not require a force equation or a positive load.
The proof does not make a whole-graph claim. A caller must verify the
outward-normal convention literally, reversing both incoming normals
when appropriate. The original means and all side endpoints are retained.

## 2. Exhaustive actual feature cover

If the ports coincide, an interior point cannot support a nonzero
normal and a relative side interior has just one outward unit normal.
The strictly opposite vertical signs therefore force the coincident
point to be an actual vertex, with both normals in its closed normal
cone.

If the ports differ, they cannot both be vertices, since distinct
vertices of a unit square are separated by at least one. Two relative
side interiors also cannot satisfy the premises: on the same side the
normals agree, on adjacent sides their dot product is zero, and opposite
sides are separated by one. The remaining case is a vertex and a
relative side interior. A nonincident side is at distance at least one
from that vertex. Hence the side is incident; its axis is a generator
of the vertex normal cone and the other actual supporting normal is in
the same closed cone.

Thus the asserted common cone belongs to one of the original ports,
so the original coordinate bounds apply at its actual vertex V. An
axis normal at a vertex is included as a vertex case. No original mean
is moved and no strict cone-interior assumption is inserted.

## 3. Exact opposite-corner obstruction

The strict opposite y signs allow a positive linear combination of the
two normals with zero y component. Its x component is positive, so
East lies in the common closed cone. Each actual inward side vector
therefore has nonpositive x component. For orthonormal inward vectors
u,v, their two x components have squared sum one and hence
u_x+v_x≤−1. Orthogonality also makes their y components have opposite
weak signs, so |u_y+v_y|≤1.

The source uses the actual opposite corner V+u+v. Its exact expansion
has the independent lower bound

    |V+u+v|² > (29/30)²+2+2(29/30)−1/2
               =3931/900.

The V_y cross term is bounded below by −1/2; discarding V_y² only
weakens the lower bound. Since V_x<−29/30 and u_x+v_x≤−1, the
horizontal cross term has the required strictly positive lower bound.
The two rational identities were independently recomputed with exact
fractions, including

    3931/900−1105/256=2959/57600>0.

This violates actual containment. All allowed coincident ports,
side-axis endpoints, and weak generator coordinates were covered.

## 4. Acceptance

The source proves its entire declared degree-free and force-free
statement. No inference uses a force-line intersection, an assumed
concurrence, a replacement mean, or an additional physical contact.
There is no unresolved mathematical or original-scope qualification.
This record does not change shared metadata or promote any caller whose
literal hypotheses have not separately been established.
