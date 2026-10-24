# An end triangle requires another load outside the positive radial-neighbor class

**Status: complete uniform hand implication and whole-mask applications;
root and separate independent full hand audits passed.**
Work in the common selected certificate and radius window

    79/40 <= R <= sqrt(1105)/16.

Let H--X--Y--H be an end triangle in a connected positive component:
X,Y have exact positive degree two, whereas H may have arbitrary
additional positive neighbors. Every actual packing square, physical
circle mask, zero individual circle weight and original contact mean
is retained. Write F_V for the actual total circle force of body V,
and M=F_X+F_Y.

## 1. The uniform force obstruction

The complete end-triangle theorem gives

    c_H . M > 0.

Its exact-degree premise is used only at X,Y. H is physically clear,
since X,Y are loaded boundary bodies and a boundary H would make a
forbidden physical boundary triangle.

Let B be the set of all other positively circle-loaded bodies of the
component. Summing every genuine body force equation, including all
unloaded bodies and every additional force at H, gives

    M + sum_{V in B} F_V = 0.

Consequently

    sum_{V in B} c_H . F_V = -c_H . M < 0.          (1)

In particular B is nonempty and at least one V in B satisfies
c_H . F_V < 0.

If V physically touches H and has two physical circle corners, then
RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md gives c_H.z>0 at both corners.
Its proof uses only physical contact and gives the uniform margin
c_H.z>121/1600. Nonnegative original weights of positive total
therefore imply c_H.F_V>0, including a zero individual corner weight.
Such a V cannot supply the negative summand in (1).

**Theorem.** Some other positively loaded body either does not
physically touch H, or has one physical circle corner and contributes
strictly negative pressure c_H.F_V<0. More precisely, there is a
body V with c_H.F_V<0, and any such V which touches H must have a
unique physical circle corner z_V, with c_H.z_V<0.

Thus the entire class in which every other positive load physically
touches H and has two physical circle corners is impossible. The
statement permits arbitrary extra unloaded bodies, arbitrary other
positive edges and arbitrary completion squares. No force at H or
at any other body has been omitted.

## 2. A complete physical-mask exit in the opposite-load C4 attachment

Use the graph H--A--B--C--H with attached triangle H--X--Y--H,
and exact positive block-load set AC. This is the full orbit
M6.TB4.C4.LAC in TRIANGLE_FOUR_BODY_BLOCK_LOAD_COVER.md. A,C
are the only loads outside X,Y, and both physically touch H.
The real B is a true unloaded degree-two side transmitter; H keeps
all four positive pair forces.

If A,C both have two physical circle corners, both summands in (1)
are strictly positive, a contradiction. The entire two-radial mask
is therefore excluded, without the canonical secondary minimizer
used in the earlier opposite-load C4-with-leaf theorem.

Every remaining physical mask has at least one unique-circle-corner
tip with c_H.z<0. Up to exchanging A,C, the complete remaining
physical-mask families are:

* Both A,C have one physical circle corner; at least one of their
  two actual corner vectors has strictly negative dot product with c_H.
* A has one physical circle corner and C has two; the actual unique
  A corner has strictly negative dot product with c_H. Reflection
  covers the reversed physical mask.

All original shared means and all three arbitrary extras remain in
both open families. These full necessary mask restrictions do not
exclude either remaining family or close the whole load orbit.

## 3. A complete physical-mask exit at a diamond hub

Let the diamond have hubs H,K and tips A,B, with the triangle
H--X--Y--H attached at H. Its exact remaining block-load set is KAB.
Every one of K,A,B physically touches H. Their true degrees are
three,two,two, while H has degree five. The theorem therefore
excludes the entire mask in which K,A,B all have two physical
circle corners. At least one of their unique circle corners must
have strictly negative dot product with c_H.

The only allowed root-preserving symmetry exchanges A,B and fixes K.
Writing U for one physical circle corner and S for two, the complete
remaining mask representatives, in the order (K,A,B), are

    (U,S,S), (S,U,S), (U,U,S), (S,U,U), (U,U,U).

Each representative includes its A/B reflection and every original
positive total circle load with nonnegative individual corner weights.
The negative-pressure condition applies to at least one actual U
corner. All five complete physical-mask families remain open, as do
the whole diamond-hub attachment and C2.34.b0.

This proof uses only the established whole end-triangle pressure,
the independently established physical radial-neighbor pressure and
the actual complete force sum. There is no new normal selection,
force splitting, movement, sampled angle premise, Lean compilation
or CI.
