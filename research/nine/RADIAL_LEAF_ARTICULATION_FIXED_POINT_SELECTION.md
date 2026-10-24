# Fixed-point normal selection at a radial-leaf articulation

**Status: complete hand selection theorem; root and independent full hand
audits passed.** Work in
\[
                       79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
Let A be a radial-leaf articulation with exactly two other positive
pair edges. Suppose both of their neighbors physically touch the
circle, and both actual intersections with A are distinct singleton
points. No assumption is made on either neighbor's circle-weight
split or on any other shared-side mean.

**Theorem.** A compatible necessary certificate can be selected so
that neither of these two singleton edges is a free vertex/vertex
contact. Both have actual side-axis owners. This holds for both S
and D leaves, and for every physical circle mask of the neighbors.

The theorem preserves the existing strict, nonradial and matched
point-normal convention. It selects normals before multiplier
extraction; it does not rotate a force in an existing certificate.

## 1. No boundary neighbor shares the leaf's radial application

Write e for the outward direction from A toward its leaf L, and p
for that leaf edge's application. The radial leaf theorem gives
\[
 p=h e,\quad h=\sqrt{R^2-1/4}-1
       \quad\text{for S},
 \qquad
 p=r e,\quad r=R-\sqrt2
       \quad\text{for D}.
\tag{2}
\]
For an S leaf, p is the midpoint of its inner side. Rotate e east.
Locally L occupies the entire half-plane to the right of p; A lies
in the left half-plane and contains p.

If p is in the relative interior of an A side, A locally occupies
the left half-plane and there is no remaining open sector for a
third square. If p is an A vertex, its open interior sector has
angle90 degrees inside that left half-plane. When both of its rays
are strictly inside that half-plane, the two remaining sectors each
have angle strictly less than90 degrees, again leaving no room for
the interior sector of a third unit square.

The only possible third square through p occurs when one A ray is
vertical. The complementary90-degree sector then forces that square
to be aligned with L and A. The two inner units are exactly
\[
           [h-1,h]\times[0,1],\qquad
           [h-1,h]\times[-1,0].
\tag{3}
\]
Their maximum squared corner norm is at most h^2+1<R^2. Indeed
\(9/10<h<61/60\), so h>1/2 and
\(\max(h^2,(h-1)^2)=h^2\), while
\(R^2=(h+1)^2+1/4>h^2+1\).
Thus any such third square is physically circle-clear.

For a D leaf, the selected nonradial point-normal convention makes
p an A-side-interior point: a vertex/vertex bridge at nonzero p
would require the forbidden radial point normal. The A side is
perpendicular to e. Its local half-plane has angle180 degrees;
the D leaf's90-degree vertex sector is centered in the opposite
half-plane, leaving two45-degree gaps. No third unit square fits
through p.

Consequently, in either leaf case, neither of the physically
circle-touching neighbors in the theorem can have its A application
at p.

## 2. Every other collinear A vertex is too central for a boundary neighbor

For a D leaf, choose e as one A side axis. Its radial application p
lies strictly inside the supporting side. The tangential coordinate
zero is therefore strictly between that side's two endpoint
coordinates; no A vertex lies on the line spanned by e.

For an S leaf, let q be an A vertex collinear with e, and suppose
q is not p. If e has two nonzero components in A's own frame,
choose their signs positive. Then p is A's unique support vertex,
and
\[
                 A=p-[0,1]v-[0,1]w.
\]
Neither adjacent vertex is collinear with e. The opposite vertex
is collinear only when e=(v+w)/sqrt(2), in which case
\[
                               q=(h-\sqrt2)e.
\tag{4}
\]
If e is an A side axis, a collinear A vertex exists only when p
is an endpoint of its support side. The other collinear vertex is
\[
                               q=(h-1)e.
\tag{5}
\]
These possibilities exhaust all four vertices, including aligned
endpoint support states.

Both non-leaf possibilities have norm strictly less than r=R-sqrt(2).
For (4), h<sqrt(2) and
\[
                  h+R>\frac9{10}+\frac{79}{40}
                         =\frac{23}{8}>2\sqrt2.
\tag{6}
\]
For (5), |h-1|<1/10<r. The last inequality follows already from
R>=79/40 and sqrt(2)<3/2.

Every point q of a circle-touching unit square has norm at least r:
choose its circle corner z and use
\(R\le|q|+|z-q|\le|q|+\sqrt2\).
Thus no q in (4)--(5) can be an application shared with one of the
boundary neighbors in the theorem.

Combining Sections1--2, any singleton A-neighbor contact which is
a vertex of A satisfies
\[
                                \det(q,e)\ne0.
\tag{7}
\]
In particular this holds for every candidate free vertex/vertex
normal in the theorem.

## 3. The complete force-and-torque determinant

Let q,s be the two distinct singleton applications on A, with
outward normals n,m, and positive pair magnitudes mu,nu. Write alpha
for the leaf magnitude. A is physically circle-clear by the radial
leaf reduction. Its force and origin torque equations are
\[
 \alpha e+\mu n+\nu m=0,
 \qquad \mu\det(q,n)+\nu\det(s,m)=0.
\tag{8}
\]
The leaf contributes zero torque because p is radial. Eliminating
mu,nu after taking a determinant with e gives the necessary identity
\[
 D(n,m)=\det(e,n)\det(s,m)
                  -\det(e,m)\det(q,n)=0.
\tag{9}
\]
Suppose the edge at q is free. Fix the other normal m.

If det(e,m) is nonzero, the left side is det(W,n), where
\[
                         W=\det(s,m)e-\det(e,m)q.
\tag{10}
\]
If W were zero, q would be collinear with e, contrary to (7).
Hence this is a nonzero linear function of the free normal. Its
zero directions can be avoided in the allowed open strict interval.

If m is parallel to e, the force equation in (8) would require n
parallel to e too. Avoiding those at most two directions excludes
this alternative as well.

If both normals are free, q and s are distinct physical junctions,
so their parameters are independent. First choose m nonparallel to
e; the preceding nonzero linear function then supplies n with
D(n,m) nonzero. Therefore D is not identically zero on the product
of the two open normal intervals. Its zero set has empty interior.
This covers the full two-free alternative, not just a fixed value
of the second normal.

## 4. Simultaneous selection and the exact C4 consequence

Before obtaining a stress, prelist the finitely many physical leaf
assignments, leaf types/directions, articulations, pairs of boundary
neighbors and distinct singleton applications. The list is purely
physical and does not use any extracted circle weights. Apply the
nontrivial determinant or finite-direction exclusions above to each
candidate.

The two junction parameters in a product condition are independent
because q!=s. At a four-square junction, the chosen parameter is
matched only with its opposite pair at that same point; this does
not identify parameters at q and s. The finite open dense exclusions
can be imposed inside the previously allowed strict, nonradial,
matched-junction and generic normal domain. No side mean is chosen
or constrained by this selection.

After the physical certificate is obtained, planar uncrossing keeps
surviving point normals and adds only existing shared-side forces.
Conic thinning only deletes atoms. Every final star with the stated
physical singleton premises was in the prelist, so the theorem
survives both operations.

At the canonical minimizer of
FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md, the two A-tip contacts
in the opposite-loaded-pair C4 are distinct singletons, and both
tips physically touch the circle. The present theorem consequently
makes **both A-tip contacts side-axis-owned for every physical
circle mask**, including the remaining mixed mask. Arbitrary means
on the unloaded transmitter's two sides remain.

This replaces no physical two-corner mask by a unique-corner one.
It proves an exhaustive owner reduction; the mixed-mask metric or
completion exclusion, the all-three-loaded C4 and diamond domains,
and all four arbitrary extras remain separate obligations.

No numerical pose argument, secondary condition beyond the cited
C4 application, Lean compilation, CI or relaxed point-normal
convention is used.
