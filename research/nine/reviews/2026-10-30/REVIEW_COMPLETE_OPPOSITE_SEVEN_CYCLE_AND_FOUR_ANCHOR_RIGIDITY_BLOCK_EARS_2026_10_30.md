# Complete opposite seven-cycle and four-anchor rigidity: full independent assembly review

Date: October 30, 2026 UTC.

**Verdict: PASS at the full stated scope. No mathematical repair requested.**

Reviewed source:

`COMPLETE_OPPOSITE_LONG_SHORT_SEVEN_CYCLE_SHARP_RADIUS_AND_FOUR_ANCHOR_RIGIDITY_2026_10_30.md`

Frozen source length: 17,582 bytes.

SHA256:
`4b094c6e45c844ee804db13ed1bde76f0be8e30db037b9fc5c97b59be025a670`.

I read the entire frozen source, reconstructed the local theorem and the
literal cycle caller, and checked every displayed dependency hash. All
eight pins match the current files. This is a review of the complete
mathematical join, including contact-type coverage and equality, rather
than a check of the final scalar inequality alone.

Review provenance: I authored the independent tangent-wrapper proof
listed as the last optional input, and earlier completed full reviews
of the endpoint-alignment source, the endpoint contact-locus source,
the unequal-floor profile, the alternative wrapper source, and the
return-side/order source. The joined assembly is another author's work.
Its main proof can use the alternative wrapper independently of my
tangent proof. Neither that provenance nor an arithmetic check is used
as a substitute for reconstructing the full join below.

## 1. Domain and preservation of the actual certificate

The local theorem retains actual squares in the disk about the unchanged
origin with q<=Q=1105/256. It requires the actual positive path
A--U--V--B, genuine unloaded full-degree-two U,V, and full-degree-two
A,B with actual other neighbors D,C respectively. The four marked
units A,B,C,D physically touch the circle. C,D may have arbitrary
additional positive edges. Their whole-square conditions C,D in y>0
and dist(C,D)>=1 are explicit local assumptions.

The original weights, support normals, contact means, circle masks and
all other actual packing units remain. The theorem does not obtain a
degree-two endpoint by deleting a positive edge. It does not infer
torque balance from a translationally selected graph. Its force and
moment assumptions concern one unchanged full certificate.

These are precisely the assumptions of the frozen endpoint-alignment
theorem. That source's mixed and both-tilted cases therefore apply
without any new physical-circle or endpoint-degree premise. The local
theorem does not need an embedding after its two whole-return-square
assumptions have been supplied.

## 2. Aligned endpoints and the independent floor parameters

After endpoint alignment, the actual long means remain
(s-1,t),(s,t),(s+1,t), with |s|<1/60 and |t|<=9/16. Genuine long
transmission and the actual support equations give width one at each
internal body and actual endpoint centers
(s-3/2,y_A),(s+3/2,y_B). The gap-two coupled-height estimate gives
|y_A|+|y_B|<=1/8; it does not set either center height equal to t.

The complete contact-locus input applies to each above-side physical
boundary return. Its actual return normal is either vertical upward
or strict inward/upward at the upper-inner endpoint vertex. The
horizontal inward normal is excluded by the actual inward-face lemma,
and the outward own side is contact-free. Thus the original return
force has strictly positive y component.

Since the only other positive body force at each endpoint is
horizontal, full vertical balance forces a strictly negative total
circle y resultant. An aligned endpoint with y_i>0 has its physical
circle contact only at the upper outer corner, where y is positive.
This is impossible even when one initially allows arbitrary zero or
positive weights on the physical circle mask. At y_i=0 the two circle
corners are retained with their original separate weights.

Consequently y_A,y_B<=0 and
f_i=y_i+1/2 belongs to [3/8,1/2], with f_A+f_B>=7/8. Both floors are
actual, independent endpoint upper-side heights. No shared floor or
floor for a transmitter is inserted.

## 3. Complete section cover at each endpoint

For B the actual square is
[s+1,s+2] times [f_B-1,f_B], and its actual circle equation is
(s+2)^2+(1-f_B)^2=q. The horizontal coordinate x=s+1 lies in
(59/60,61/60), exactly the domain of the wrapper input.

The complete alternative wrapper proof covers all original contacts:
an above-floor return uses the whole-square floor profile; a return
that passes below the floor must use the actual upper-inner endpoint
vertex in the relative interior of its own side. In the latter case
the unchanged normal is the return's own axis and the full original
side slider is retained. The side chart has alpha,beta>0 and actual
slider 0<r<1. Vertex/vertex and endpoint cases are included in the
above-floor/forbidden-inward-halfplane cover, not dropped by a
generic-position assumption.

Both alternatives give a nondegenerate actual section at y=5/4 and
ell_C<=sqrt(Q-(f_B+1)^2)-1. A below-floor wrapper gives strict
inequality. An above-floor tilted return also gives strict inequality.
In the only possible equality case C is aligned, its actual bottom is
f_B, and its upper outer corner lies on the Q circle. The alternative
input proves all of these claims over the full angle/slider domain;
the tangent proof is a second derivation rather than an additional
unproved restriction.

Reflection in the y axis gives the actual D section and
r_D>=1-sqrt(Q-(f_A+1)^2), with the same strictness and reflected
equality statements. The reflection preserves the common horizontal
section height, the original geometric poses and the independent f_A.

## 4. Actual section order

The source explicitly establishes the order needed by the metric
chain. This is essential: a left endpoint bound for C and a right
endpoint bound for D alone would not justify it.

Every original B--C contact point has x>=s+1>59/60. The horizontal
width of any unit square is at most sqrt(2)<89/60. Therefore every
point of C has x>59/60-89/60=-1/2. Likewise every point of D has
x<1/2, using its actual A--D contact. These statements do not require
a normal direction, a shared support owner, or a center-order argument.

The two nonempty closed section intervals are disjoint, since an
overlap would give dist(C,D)=0. Their gap in whichever order occurs
is at least one, because their interval endpoints are actual square
points and dist(C,D)>=1. If C's interval were left of D's, that gap
would be strictly less than 1/2-(-1/2)=1. Hence D's interval is left
and C's right. All strict signs follow from the open x bounds, so
neither a limiting endpoint contact nor interval degeneracy is hidden.

## 5. Sharp chain and complete equality implications

With g(Y)=sqrt(Q-Y^2), the source's chain is now justified literally:

    1 <= dist(C,D) <= ell_C-r_D
      <= g(f_B+1)+g(f_A+1)-2
      <= 2g(1+(f_A+f_B)/2)-2
      <= 2g(23/16)-2 = 1.

The first metric upper bound uses the original section endpoint points.
Both floors lie in [3/8,1/2], so g is strictly decreasing and strictly
concave throughout the entire argument interval. The exact final
identity is Q-(23/16)^2=9/4. Therefore every comparison is equality.

Strict concavity gives f_A=f_B; strict decrease then gives their sum
7/8, hence each is 7/16 and y_A=y_B=-1/16. Equality rules out every
below-floor wrapper and every tilted above-floor return. The complete
profile equality descriptions put D,C at centers (-1,15/16) and
(1,15/16), with both aligned. Their upper outer corners have squared
norm Q. Actual containment in q<=Q therefore forces q=Q; no assumption
of contact with the larger auxiliary circle has replaced containment.

The original endpoint circle equations then read
(2-s)^2+(9/16)^2=Q and (2+s)^2+(9/16)^2=Q. Both horizontal quantities
are positive and Q-(9/16)^2=4, so s=0. This gives centers
(-3/2,-1/16),(3/2,-1/16), and the actual width-one long support
equalities put the U,V horizontal center coordinates at -1/2,+1/2.
They do not fix either transverse coordinate.

At the equality pose, B meets C exactly along
[1,3/2] times {7/16}. At the left endpoint C is in the relative
interior of its lower side; at the right endpoint B is in the relative
interior of its upper side; in the interval interior both are.
Accordingly the common unit support normal is uniquely upward even at
the two segment endpoints. The same holds at A,D by reflection. Thus
the original normals are proved vertical, with no replacement of a
vertex mean, a shared-side mean, or an actual force atom.

## 6. The cycle's lower radius window is derived

For the literal cycle A--U--V--B--C--W--D--A, the common long normal
and full moments give the original means and widths above. At the end
means, the unit-square normal-chord fact gives actual contained points
(s-2,t) in A and (s+2,t) in B. It applies to both a support vertex and
every original weighted mean on a supporting side. Hence

    q >= max((s-2)^2+t^2,(s+2)^2+t^2)
      = (2+|s|)^2+t^2 >= 4.

Thus R>=2>79/40, exactly supplying the lower radius range of the
return-side theorem. If q>Q there is no exclusion problem; in the
case requiring proof, q<=Q, its upper range also holds. The lower
window has not been imported as an independent cycle hypothesis.

The compatible actual cycle sectors and physical circle spokes give
the marked order used by the return-side theorem. That theorem places
the entire original C,D in the same halfplane y>1/120 after one common
reflection. It applies with arbitrary marked degrees at C,D and does
not modify their contact means or orientations.

The actual D--W--C path has genuine unloaded full-degree-two W.
Translational balance gives one signed original normal m. Telescoping
actual support equalities gives a support gap equal to width_W(m),
at least one. Thus every original c in C,d in D satisfies
m.(c-d)>=width_W(m)>=1, and dist(C,D)>=1. No discrete width or
horizontal short normal is assumed in this step. These are all the
remaining hypotheses of the local theorem.

## 7. Equality for the short path and the exact closure scope

After applying the local theorem, the fixed C,D geometry has actual
points c,d at a common height with c-d=e_x and distance one. Their
unchanged short support inequality implies
1>=m.e_x>=width_W(m)>=1. Hence m=e_x and width_W(m)=1. The elementary
unit-square width formula then makes W side-normal to e_x, and the
actual supports at x=-1/2,+1/2 give its horizontal center zero. Its
vertical center and original force-line height remain subject to the
actual full equations. They have not been set to zero or identified.

This closes the entire opposite (2,0,1,0) seven-cycle family below Q,
including all previously tilted, oblique, shared-side and two-circle
mask cases. It also proves the broader local separated-return theorem.
Additional positive edges at C,D and all unstressed or stressed
completion units remain present. The seven actual bodies already force
the bound, so a nine-unit caller needs no completion search for this
feature.

The source correctly keeps the adjacent (2,1,0,0) orbit separate, since
its neighbor of B is an internal transmitter rather than the physical
boundary return C. Other seven-cycle families, branching large blocks,
smaller stressed cores, completion geometry and common-selection
obligations are not declared closed by this result. Equality describes
four boundary anchors and actual directions, not the entire packing.

No numerical pose search, Lean/Lake compilation, CI run, ledger change,
stress reselection, or discarded actual square entered this review.
