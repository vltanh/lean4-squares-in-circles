# Generic physical normal selection removes vertex/vertex articulation contacts in the D branch

**Status: complete hand certificate-selection argument; independent
hand audit passed.** The physical stress can be selected with the existing
strict/nonradial point-contact conventions, planar body graph,
at-most-27 scalar-atom bound, and unique positive component, and with
the following additional property:

> In a surviving D-leaf triangle-plus-leaf component, neither triangle
> edge incident to the clear articulation is a point-only
> vertex/vertex contact.

Together with `D_LEAF_ARTICULATION_CONTACT_LOCALIZATION.md`, the exact
remaining articulation alternatives are therefore:

1. two horizontal leftward reactions, with application points anywhere
   permitted on the articulation's left side;
2. reactions at its opposite left corners, each of which lies in the
   relative interior of a side of the corresponding loaded neighbor.

The second alternative has both contact axes owned by the loaded
neighbors. This is a selection theorem for a necessary minimizing
certificate, not an assertion about every physical stress. Section 6
gives an exact positive D core inside the radius window that explains
why the distinction is necessary. Neither remaining alternative nor
the entire D completion problem is excluded here.

## 1. The articulation, and the variable-application issue

Use the declared window

\[
                  79/40\le R\le\sqrt{1105}/16.
\]

For a D leaf \(L\) attached to the clear articulation \(A\),
rotate so its bridge points right. Put

\[
 s=1+\sqrt2-R,\qquad
 A=[-s,1-s]\times[h-1,h],\qquad 0<h<1.                  \tag{1}
\]

The bridge acts in direction \(e_x\) at \((1-s,0)\),
and has positive magnitude \(\mu_L\). Name the other triangle
bodies \(B,C\). Their positive outward contact forces on \(A\)
have magnitudes \(\mu_B,\mu_C\), unit normals \(n_B,n_C\),
and genuine shared application points \(p_B,p_C\).

For a positive-length shared side the application point is a
stress-dependent weighted mean, not a fixed chosen vertex. A generic
argument must not hold this mean fixed while changing the certificate.
The following elementary fact removes exactly that problem here.

**Support-span lemma.** If \(p\) minimizes \(n\cdot x\) on a
unit square \(T\) and \(n_y<0\), then

\[
                         \max_T y-p_y<1.                 \tag{2}
\]

At a uniquely minimizing vertex, orient the two inward unit side
vectors \(u,v\). Their \(n\)-projections are positive.
Since \(n_y=u_y(n\cdot u)+v_y(n\cdot v)<0\), at least one
of \(u_y,v_y\) is negative. The upward span is at most the other
positive component, strictly less than one: a vertical upward side
would have negative \(n\)-projection. If the minimum is a side,
its inward perpendicular direction is \(n/|n|\), with negative
vertical component. The greatest height is on the minimizing side,
whose vertical span is strictly less than one. This proves (2) also
for an arbitrary application point along a shared side.

If \(n_C=e_y\), the whole square \(C\) lies in \(y\ge h\).
The horizontal bridge and vertical force balance on \(A\) force
\((n_B)_y<0\), so \((p_B)_y=h-1\). Equation (2) then puts
all of \(B\) strictly below \(y=h\), contradicting its contact
with \(C\). Reflection excludes \(n_C=-e_y\), and the same
argument applies with \(B,C\) interchanged.

Thus a triangle contact normal at \(A\) cannot be vertical.
If one is horizontal, vertical force balance makes the other
horizontal as well. A strict point-only vertex/vertex normal on the
aligned square \(A\) has both coordinate components nonzero,
so it cannot occur in this horizontal alternative.

Consequently, **if a D articulation has any positive point-only
vertex/vertex triangle edge, both triangle normals are nonaxis
directions**. Both application points are then fixed vertices of
\(A\), and neither contact is a positive-length shared side.
Their vertical components have opposite signs, so the two points
are distinct, one at height \(h\) and the other at height \(h-1\).
In particular both heights are nonzero. This conclusion already
resolves every variable shared-side application before generic
normal selection is used.

The stronger complete localization in
`D_LEAF_ARTICULATION_CONTACT_LOCALIZATION.md` proves that both
horizontal components are strictly negative, so these two fixed
vertices are specifically the upper-left and lower-left corners.
Its proof includes arbitrary circle-corner weight splits and does
not impose a generic-normal assumption.

## 2. A necessary determinant at the clear articulation

The force and origin-moment equations on \(A\) are

\[
 \mu_Bn_B+\mu_Cn_C+\mu_Le_x=0,                         \tag{3}
\]

\[
 \mu_B\det(p_B,n_B)+\mu_C\det(p_C,n_C)=0.               \tag{4}
\]

The bridge contributes zero origin moment. Eliminate the two positive
triangle magnitudes between the vertical component of (3) and (4).
Every such stress must satisfy

\[
 E:=(n_B)_y\det(p_C,n_C)
       -(n_C)_y\det(p_B,n_B)=0.                         \tag{5}
\]

Suppose \(AB\) is a point-only vertex/vertex contact. As shown in
Section 1, any possible positive D star using it has fixed
\(p_B,p_C\), with \((p_B)_y\ne0\) and \((n_C)_y\ne0\).
Hold \(n_C\) fixed and expand (5) as a function of \(n_B\):

\[
 E=(n_C)_y(p_B)_y(n_B)_x
   +\bigl(\det(p_C,n_C)-(n_C)_y(p_B)_x\bigr)(n_B)_y.
                                                               \tag{6}
\]

The coefficient of \((n_B)_x\) is nonzero. Thus (5) is a
nonzero linear equation in the freely chosen unit normal \(n_B\).
It cannot hold identically on any open interval of strict common
support normals. At most two antipodal unit directions satisfy it.

No circle-load vector of \(B\) or \(C\) was fixed in this
argument. Their possible two-corner weights may change arbitrarily:
equation (5) is a necessary equation on the **unloaded articulation**
alone, and its only application points are the fixed vertices
just established.

## 3. Make all choices before the physical KKT argument

Work at a fixed hypothetical minimizing packing, before choosing the
smooth physical feasible branch of `PHYSICAL_CONTACT_STRESS.md`.
There are finitely many physical touching pairs and finitely many
ordered candidates \((A,L,B,C)\) for a D-leaf triangle-plus-leaf
component.

At a point-only vertex/vertex contact, the common normals strictly
exposing its point on both squares form a nonempty open angular
interval. Use one free parameter for each such contact, with the
following existing exception. At a four-square junction, the two
opposite-pair normals are chosen in the matched form

\[
au+bv,\qquad au-bv,\qquad a,b>0,\quad a^2+b^2=1,        \tag{7}
\]

as in `PHYSICAL_BODY_GRAPH_UNCROSSING.md`. These two opposite
contacts use one joint parameter. Each individual normal still
ranges over a nonempty open strict interval when that parameter
varies. Different physical junctions have independent parameters.

For every geometric D-star candidate with at least one point-only
articulation edge, impose the avoidance of (5), whenever its contact
types and locations permit the nonparallel alternative of Section 1.
All other candidate contact types have already been excluded there
without a determinant condition.

If both articulation edges are point-only contacts, their two
application points are distinct vertices, one above and one below
the horizontal axis. Their parameters are therefore independent:
the matching in (7) only couples opposite pairs **at the same
physical junction**. If the other articulation edge is a
vertex/side contact, its normal and point are fixed by the actual
geometry. In either case, varying a freely selectable articulation
normal while holding all other parameters fixed makes (5) the
nonzero linear condition (6).

It follows that the zero set for each forbidden determinant is
closed and has empty interior in the finite product of open
parameter intervals. To see the latter directly, any open parameter
box permits the indicated single normal to vary over an open arc,
on which a nonzero linear equation cannot hold throughout.
Its complement is open and dense. A finite intersection of these
open dense complements is nonempty: successively choose a smaller
nonempty open box avoiding each of the finitely many closed zero
sets.

The prior exclusions of radial directions at nonzero point contacts,
and any already imposed exclusions of square-diagonal directions,
remove only further finite direction sets and can be retained
simultaneously. Thus all new and prior normal choices can be made
**before** constructing the smooth branch and invoking the physical
stress theorem.

There is no change of a contact normal after obtaining a stress.
Every selected point normal is still a genuine strict common
support normal, so the branch's feasibility and strict expansion
direction are unchanged.

## 4. Compatibility with planarity, thinning and aggregation

Run the original physical KKT/conic argument with the choices just
made. Then perform the exact junction uncrossing from
`PHYSICAL_BODY_GRAPH_UNCROSSING.md`. The matching in (7) was
retained, so the same force-and-torque replacement is available.
The uncrossing deletes or decreases opposite point-contact forces
and adds only genuine adjacent shared-side endpoint forces. It
never changes a surviving point-only contact's normal or point.

Conic thinning again uses only the current positive atom types and
restores at most \(3n\) positive scalar atoms. Aggregating shared
side endpoints may change their weighted-mean application points,
but Section 1 already handles every such mean: a horizontal
shared-side normal cannot coexist with a strict point-only
articulation normal, and a vertical normal is impossible outright.

Suppose the resulting positive graph nevertheless had a D-leaf
triangle-plus-leaf component with a point-only articulation edge.
Its actual force and torque equations would imply (5), with exactly
the preselected normals and the fixed vertices covered by the
avoidance condition. This is a contradiction. This reasoning applies
to the final graph, so it does not assume that the same candidate
component existed before uncrossing or thinning.

The planar embedding, the \(3n\)-atom bound, and the exterior-face
property for physical circle-touching bodies are therefore retained.
The proof of `UNIQUE_POSITIVE_COMPONENT.md` applies unchanged to
this selected planar certificate. The other normal-based reductions
remain valid because all their required strict/nonradial choices
were retained.

## 5. Exact surviving D contact alternatives

**Theorem 5.1.** A minimizing physical stress can be selected with
all the preceding certificate properties and with no point-only
vertex/vertex articulation edge in a D-leaf triangle-plus-leaf
component.

By `D_LEAF_ARTICULATION_CONTACT_LOCALIZATION.md`, exactly the
following two articulation alternatives remain.

**Parallel-left alternative.** Both outward normals from \(A\)
are \(-e_x\). Their application points lie on \(x=-s\),
with possibly varying shared-side means, and satisfy

\[
                         \mu_By_B+\mu_Cy_C=0.
\]

**Opposite-corner alternative.** After exchanging \(B,C\),

\[
 p_B=(-s,h),\quad p_C=(-s,h-1),\qquad
 n_B=(-\cos\phi,\sin\phi),\quad
 n_C=(-\cos\psi,-\sin\psi),
\]

where \(0<\phi,\psi<\pi/2\), and

\[
                       h=\frac{\tan\phi}{\tan\phi+\tan\psi}.
\]

Each contact is a point because its normal is nonaxis for \(A\).
Its point is a vertex of \(A\). It is not a vertex of the
neighbor by Theorem 5.1, so it lies in the **relative interior of
a side of that neighbor**. Both axes are thus genuinely owned
by \(B,C\), respectively.

The physical \(BC\) contact, one- or two-circle-corner cases,
every circle-weight mask, and every remaining physical square are
still unrestricted. Neither surviving alternative is declared
infeasible by this selection theorem.

## 6. Exact control: arbitrary allowed normals admit a D core in the window

The selection qualification cannot be dropped. Here is an exact
positive physical D core satisfying the older strict/nonradial point
conventions, at a radius inside the declared window.

Put

\[
 c=\frac{\sqrt3}{2},\qquad
 P=\frac32+\sqrt2+c,\qquad
 R=\frac P2+\frac{3}{8P},\qquad
 s=1+\sqrt2-R,
\]

\[
 X=s+\frac12+c=P-R,\qquad
 T=\frac{(c-\tfrac12)s+(1-c)/2}{cX}.                    \tag{8}
\]

The identity defining \(R\) gives

\[
                         R^2=X^2+c^2.                   \tag{9}
\]

All radius bounds can be checked rationally. We have
\(189/50<P<19/5\): for the lower bound use
\(\sqrt2>707/500\) and \(\sqrt3>433/250\), each verified
by squaring; the upper bound follows from
\(\sqrt2<17/12\) and \(\sqrt3<7/4\). Also \(P>15/4\).
Therefore

\[
 R>\frac{189}{100}+\frac{15}{152}>\frac{79}{40},
 \qquad
 R<\frac{19}{10}+\frac1{10}=2<\frac{\sqrt{1105}}{16}.
                                                               \tag{10}
\]

In particular \(2/5<s<9/20\). Directly from (8), using
\(4/5<c<9/10\), one has \(0<T<1/4\) and \(c-XT>0\).
For example the numerator in \(T\) is positive and less than
\((2/5)(9/20)+1/10=7/25\), while \(cX>34/25\);
also \(cXT<7/25<c^2=3/4\).

Take

\[
                     A=[-s,1-s]\times[-1/2,1/2],
\]

and attach the radial D leaf with inner vertex \((1-s,0)\)
and outer vertex \((R,0)\). Define \(B\) by its vertex
\(p_B=(-s,1/2)\) and inward orthonormal side vectors

\[
                         u=(-1/2,c),\qquad v=(-c,-1/2).
\]

Let \(C\) be the reflection of \(B\) in the horizontal axis.
The two nonarticulation contacts and outer circle vertices are

\[
 p_{BC}=(-s-c,0),\qquad z_B=(-X,c),\qquad z_C=(-X,-c).
                                                               \tag{11}
\]

Both \(B,C\) lie in \(x\le-s\), with their respective
rightmost points exactly \(p_B,p_C\). The lowest point of \(B\)
and highest point of \(C\) are both \(p_{BC}\). Thus all
three triangle contacts are actual point-only contacts, and the
four open square interiors are pairwise disjoint. The leaf lies
in \(x\ge1-s\) and is closed-disjoint from \(B,C\).

Equation (9) puts \(z_B,z_C\) on the circle. The other three
vertices of \(B\) are \((-s,1/2)\),
\((-s-1/2,1/2+c)\), and \((-s-c,0)\). They are strictly
inside: for the middle one the squared-radius deficit is
\(2sc+1/2>0\), for the last it is \(s+c+1>0\), and for
the first it is immediate from (9). Reflection handles \(C\).
Every corner of \(A\) has squared norm less than
\((3/5)^2+1/4<R^2\), and the usual D-leaf formula verifies
all its vertices. Thus the entire physical core lies in the disk.

Use the following unnormalized positive circle weights and contact
force vectors:

\[
 \lambda_B=\lambda_C=1,\qquad \lambda_L=\frac{2X}{R},
\]

\[
 F_{A\to B}=2X(-1,T),\qquad
 F_{A\to C}=2X(-1,-T),\qquad
 F_{B\to C}=(0,-2(c-XT)),\qquad
 F_{A\to L}=4Xe_x.                                    \tag{12}
\]

The first two directions strictly expose the appropriate vertices
on both bodies: on \(B\) the inward projections are
\(1/2+cT>0\) and \(c-T/2>0\), while on \(A\) both
normal components have the strict corner signs. The vertical
\(BC\) normal strictly exposes its two touching vertices.
None of these point normals is radial. For \(AB\), a radial
normal would require \(T=1/(2s)>1\), whereas \(T<1/4\);
the \(AC\) case is its reflection. At \(p_{BC}\ne0\),
the normal is vertical and the radius horizontal.

The force equations follow immediately from (9), (11), and (12).
The only independent cycle moment equation is

\[
                  X(1/2-sT)=(s+c)(c-XT),                 \tag{13}
\]

which is exactly the defining equation for \(T\) in (8).
The two moments at \(A\) cancel by reflection and the bridge
moment is zero. Thus every body has both force and torque balance.
Dividing all weights and contact forces by \(2+2X/R\)
normalizes the total circle weight to one.

This is a positive physical triangle-plus-leaf core at
\(R\) strictly between \(79/40\) and \(2\). It does not
assert a nine-square completion or a minimizing packing. Its two
vertex/vertex articulation normals satisfy the exceptional
determinant (5), as they must, and are removed by the additional
pre-KKT selection proved above. The example therefore documents
the exact boundary between arbitrary physical stress and the
selected certificate used in Theorem 5.1.
