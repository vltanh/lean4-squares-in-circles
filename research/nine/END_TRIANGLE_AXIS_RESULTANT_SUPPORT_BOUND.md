# An axis-aligned end-triangle resultant has a stronger support bound

**Status: complete hand local theorem; root and separate independent full
hand audits passed.** Work in the common
selected certificate and the declared radius window

    79/40 <= R <= sqrt(1105)/16.

Let H,C,E be a positive physical triangle with C,E true loaded
degree-two tips. H may have arbitrary additional positive forces.
Let M=F_C+F_E be their actual nonzero circle resultant. Suppose
N=M/|M| is a side axis of the actual square H. Every original
physical mask and actual contact mean is retained.

**Theorem.** Both actual HC,HE applications belong to H's support
side in direction N. Consequently

    h_H(N)<59/60.                                  (1)

Together with the general end-triangle support theorem, one may
also retain h_H(N)<min(sqrt(R^2-1/4)-1,59/60). No physical tip is
replaced by an abstract radial leaf in this statement.

## 1. Parallel root normals

Write n,m for the outward H-to-C and H-to-E normals, with positive
magnitudes mu,nu. Summing the genuine tip equations gives

    M=mu n+nu m.

Opposite parallel normals would place C,E beyond opposite supports
of H, separated by a positive unit width, so they could not touch.
In the remaining parallel case n=m=N. Both actual applications are
therefore on the maximizing N side, including every shared mean
and coincident mean endpoint.

## 2. Nonparallel root normals cannot have an H side owner

Suppose first n is an H side axis parallel to N. Projection of
M=mu n+nu m onto the perpendicular H axis then forces m parallel
to N too, contrary to the present nonparallel case. This covers
both n=N and n=-N.

If n is instead one of H's two transverse side axes, the physical
unit-triangle owned-normal lemma gives n.m>=0. But M.n=0, whereas

    (mu n+nu m).n=mu+nu(n.m)>0,

which is a contradiction. The same two alternatives apply with
n,m exchanged. Thus neither actual root normal is an H side axis.
This argument includes a normal owned by both touching squares;
being an H axis is the only property used.

## 3. The complete strict-vertex cover selects one support side

Both actual root applications are now vertices strictly exposed by
their normals. In the orthonormal H frame with first axis N and
second axis JN, both components of each normal are nonzero.
Their positive transverse components sum to zero, so the two
transverse signs are opposite. Their actual vertices therefore lie
on opposite transverse faces of H, and cannot be the same vertex.

Opposite vertices are impossible for a physical unit-square triangle,
by the complete strict support-span argument in
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section2. Hence the two
vertices are adjacent and lie on the same N-orthogonal side of H.

At both of these vertices the longitudinal signs of the strict
normals are the same: positive on H's maximizing N side, negative
on its minimizing side. The equation

    mu(n.N)+nu(m.N)=|M|>0

selects the maximizing side. Thus both actual applications belong
to that side, in every nonparallel alternative as well.

This covers all owners and free point normals. The axis cases were
handled before the strict-vertex argument, so no parameter endpoint
has been discarded.

## 4. The full support consequence

If h_H(N)>=59/60, the complete all-mask theorem
END_TRIANGLE_HIGH_FACE_EXCLUSION.md now applies to the two actual
applications on that one side and gives a contradiction. Therefore
(1) holds. The earlier bound h_H(N)<sqrt(R^2-1/4)-1 remains valid
independently and gives the stated minimum of the two bounds.

The proof uses no force equation at H beyond the actual aggregate
identity supplied by C,E. Every additional neighbor of H remains,
as do every physical circle-corner split, every original shared mean
and all other packing squares. It is a uniform necessary condition,
not a claim that all end-triangle resultants align with a root axis.
No numerical sample, normal reselection, Lean compilation or CI is
used.
