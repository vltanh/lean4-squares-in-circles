# Every loaded end triangle uses one actual side of its root

**Status: complete uniform hand routing theorem; root and separate independent
full hand audits passed.** Work with the common selected
certificate in the declared window

    79/40 <= R <= sqrt(1105)/16.

Let H--C--E--H be a positive physical triangle whose tips C,E are
genuinely loaded and have exact positive degree two. The root H may
have arbitrary additional positive forces. Let M=F_C+F_E be the
actual nonzero sum of their circle forces. Every physical mask,
individual zero corner weight, original shared-side application mean
and other packing square remains.

**Theorem.** There is an actual side of H, with outward side-axis
normal N, such that both actual HC and HE applications lie on that
side and M.N>0. Its actual outward support height P=h_H(N) satisfies

    P < 39/40.                                      (1)

The normal N need not be parallel to M. This theorem identifies a
common actual side; it does not allow replacing either actual mean
by an endpoint or selecting a preferred side when several are possible.

## 1. Complete parallel and axis-resultant alternatives

Write n,m for the actual outward H-to-C and H-to-E unit normals,
with positive magnitudes mu,nu. The genuine tip force sum gives

    M = mu n + nu m.

Opposite parallel normals would place C,E beyond opposite H supports,
preventing their physical contact. If n,m are parallel, therefore
n=m=M/|M|. If this common direction is an H side axis, both actual
applications lie on that maximizing side. Otherwise it strictly
exposes one H vertex, and both actual applications are that vertex.
Either adjacent side has strictly positive dot product with M and
serves as the required side. This covers every actual mean endpoint.

For nonparallel n,m, if M/|M| is an H side axis, the complete
END_TRIANGLE_AXIS_RESULTANT_SUPPORT_BOUND.md puts both actual
applications on its maximizing side. This includes every root owner
and the strict-vertex alternatives; no extra assumption on a mean is
needed.

## 2. A nonaxis resultant and the true maximizing application

Assume now n,m are nonparallel and M has nonzero components along
both H side axes. Its support on H has a unique maximizing vertex F.
The full maximizing-port theorem of
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md supplies an actual root
application equal to F. Its sole both-H-owned perpendicular exception
is excluded by BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md, whose
two tips have precisely the true degrees and loads required here.

Call the other actual application p, and its actual normal m after
interchanging C,E if necessary. All possible features of p are as
follows.

If m is an H side axis, the physical triangle nonobtuse-normal lemma
gives n.m>=0. Hence

    M.m = mu(n.m)+nu > 0.

F is therefore on H's maximizing m side. The other application p
is on the same support side by its actual normal. This proves the
required common-side claim, with every shared mean retained.

If m is not an H side axis, it strictly exposes a vertex p. It cannot
be the vertex opposite F. Indeed, if the first normal n also strictly
exposes F, the physical unit-triangle strict support-span theorem
excludes opposite vertices. If n is instead an H side axis whose
actual endpoint mean is F, a strict normal at the opposite vertex
would have n.m<0, contradicting the same owned-normal nonobtuse lemma.
These two cases exhaust the normal at the actual point F.

Thus p equals F or is adjacent to it. In the adjacent case take their
common H side. In the equal case take either adjacent side at F.
The outward normal of each such side has positive dot product with M,
because M has both side-axis components nonzero and F maximizes M.
This proves the common-side conclusion in every nonaxis alternative.

## 3. The uniform support consequence and precise use

The side obtained in Sections1--2 contains both original root means.
END_TRIANGLE_HIGH_FACE_EXCLUSION.md therefore excludes P>=39/40 and
gives (1). If its height also satisfies P>=4/5 or P>=29/30, then
END_TRIANGLE_FACE_RESULTANT_ANGLE.md supplies respectively

    (M/|M|).N > 1/2,    or    (M/|M|).N > 4/5.

Every use requiring a particular side of H must still identify that
side from its actual features. The theorem gives existence of a
common side and cannot replace such a location argument by an
arbitrary choice. All additional H forces remain in the original
certificate, and only C,E use degree-two force and torque statements.
No new normal selection, physical movement, numerical sample, Lean
compilation or CI is used.
