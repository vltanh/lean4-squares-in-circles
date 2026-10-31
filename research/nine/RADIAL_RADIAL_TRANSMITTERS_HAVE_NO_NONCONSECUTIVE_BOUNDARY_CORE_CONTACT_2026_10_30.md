# Radial/radial transmitters have no nonconsecutive boundary core contact

Date: October 30, 2026. Author: joint-pockets continuation.

**Status: complete additive hand theorem, frozen for separate full review.**
This strengthens the accepted bilateral-boundary theorem without
changing that source or its review pin. The conclusion is actual
noncontact, including every zero-weight pair and every side endpoint.

## 1. Original whole-family statement

Keep the exact original setting of [T]: a compatible physical
certificate whose entire positive component is a simple cycle with
at least three loaded bodies, in
\[
            79/40\le R\le\sqrt{1105}/16.
\tag{1.1}
\]
Let \(X-U-Y\) be an actual side-normal singleton channel whose loaded
endpoints \(X,Y\) each have two physical circle corners. Individual
corner weights may vanish. Retain all actual bodies, true degrees,
original forces, means, circle masks and physical touching relations.

**Theorem 1.1.** The only physically boundary core bodies touching
\(U\) are its two original positive neighbors \(X,Y\).

This includes physical boundary bodies with zero total circle load.
It does not exclude actual contacts with circle-clear core bodies
or with additional squares.

The literal short-C7 consequence in Section 4 says that, in the
remaining two-RR pattern, the unique loaded body has exactly its
two positive neighbors among the core as actual physical neighbors.
Its possible contacts with both completion squares are retained.
A further generic-contact consequence removes its direct free
vertex/vertex edge, with the existing selected-certificate premise
explicit.

## 2. A uniform support and radius lemma

We first prove a geometric statement independent of any stress.

**Lemma 2.1.** Let \(W\) be an actual unit square with center
\(c=(c_x,c_y)\), where \(c_y\le0\). Suppose
\[
                 \min_{p\in W}p_x=\frac12
\]
and its exposed face on \(x=1/2\) contains a point with
height greater than \(-1/10\). Then
\[
                   \max_{p\in W}|p|^2<\frac{31}{8}.
\tag{2.1}
\]

*Proof.* If the exposed face is one vertex, use that vertex
\(p=(1/2,y)\). If it is a vertical side, choose its upper endpoint
as \(p\). In both cases \(y>-1/10\). The two actual unit edges
pointing into \(W\) at this vertex can be written
\[
       u=(a,b),\qquad v=(b,-a),\qquad
       a,b\ge0,\qquad a^2+b^2=1.
\tag{2.2}
\]
The vertical-side case is \(a=1,b=0\); thus it has not been omitted.
Set
\[
             t=a-b,\qquad s=a+b=\sqrt{2-t^2}.
\]
The actual center is \(c=p+(u+v)/2\). Therefore
\[
                -\frac1{10}<y\le\frac t2,
\tag{2.3}
\]
and \(t\in[-1,1]\).

The center has nonnegative coordinates along both inward axes:
\[
 \begin{split}
 c\cdot u
   &=\frac12+\frac a2+by>\frac25,\\
 c\cdot v
   &=\frac12+\frac b2-ay\\
   &\ge \frac12+\frac b2-\frac{a(a-b)}2
    =\frac{b^2+b+ab}{2}\ge0.
 \end{split}
\tag{2.4}
\]
Consequently the opposite corner \(z=p+u+v\) is a farthest corner
of \(W\). This assertion also holds if the second quantity in
(2.4) is zero and two corners tie. Its squared radius is exactly
\[
       |z|^2=\left(\frac12+s\right)^2+(y-t)^2.
\tag{2.5}
\]
For fixed \(t\), this is convex in \(y\). The interval in (2.3)
is contained in \([-1/10,t/2]\), which is nonempty. Its two
endpoint values satisfy
\[
 \begin{split}
 F(t/2)
    &=\frac94+s-\frac34t^2
       \le\frac94+\sqrt2,\\
 F(-1/10)
    &=\frac{113}{50}+s+\frac t5
       \le\frac{123}{50}+\sqrt2.
 \end{split}
\tag{2.6}
\]
This includes \(t<0\); no sign of \(t\) was used except
\(-1\le t\le1\). Since
\[
 \sqrt2<\frac{283}{200},\qquad
 \frac{123}{50}+\frac{283}{200}
             =\frac{31}{8},
\]
both endpoint values are strictly below \(31/8\).
Convexity proves (2.1). \(\square\)

The lemma is a bound for the entire square, not only for its contact
point or one preferred circle corner. A shared side, an endpoint of
a shared side, and a point-only exposed vertex are all included.

## 3. Apply the lemma to every other physical boundary core body

Use the unchanged RR channel coordinates from [T]:
\[
 \begin{gathered}
 d=\sqrt{R^2-\tfrac14}-1,\qquad d>\frac9{10},\\
 U=[-\tfrac12,\tfrac12]\times
        [b_U-\tfrac12,b_U+\tfrac12],\\
 d-\tfrac12<b_U<d+\tfrac12.
 \end{gathered}
\tag{3.1}
\]
Here the outward direction is \(N=(0,1)\). For every physical
boundary core body \(W\ne X,Y\), the full all-physical-spoke
argument in [T] gives
\[
                         (c_W)_y<0.
\tag{3.2}
\]
Its complete contact cover also proves that any actual contact
with \(U\) must be in the relative interior of a vertical side
of \(U\), with a horizontal common separator. In particular
every such contact point has height
\[
            y\ge b_U-\tfrac12>d-1>-\frac1{10}.
\tag{3.3}
\]
The top and bottom corners have already been excluded in [T];
the present argument covers every remaining vertical-side contact.

Suppose such a contact exists. Reflect the horizontal coordinate if
necessary. The common separator then puts
\[
               \min_{p\in W}p_x=\frac12,
\]
and the exposed face contains the actual contact point from (3.3).
Equations (3.2)--(3.3) put \(W\) under Lemma 2.1. Hence
\[
                  \max_{p\in W}|p|^2<\frac{31}{8}.
\]
But \(W\) is physically boundary, so its maximum squared corner
radius is exactly \(R^2\), whereas
\[
 R^2\ge\left(\frac{79}{40}\right)^2
      =\frac{6241}{1600}
      =\frac{31}{8}+\frac{41}{1600}.
\tag{3.4}
\]
This is a contradiction. Thus \(W\) does not touch \(U\).

The two endpoints \(X,Y\) do touch \(U\) by their original positive
contacts. This proves Theorem 1.1. All boundary-circle weights,
shared contact means and actual zero-weight neighbors were kept.
There is no motion or canonical-minimum premise in this theorem.

## 4. Literal unique-load physical-neighbor consequence in the two-RR C7

Consider the exact original seven-cycle
\[
          X-U_+-A-U_3-D-B-U_--X,
\tag{4.1}
\]
where \(X,A,B\) are physically two-circle loaded bodies, \(D\)
is physically one-circle loaded, and the three \(U\)'s are genuine
unloaded side transmitters. Thus \(U_+,U_-\) are RR, while \(U_3\)
is radial/unique. This is the remaining two-RR short-C7 pattern
identified in [N], Section 8, with its two actual completion squares.

**Corollary 4.1.** The only actual core neighbors of \(D\) are \(B\)
and \(U_3\).

Indeed Theorem 1.1 excludes actual contacts from \(D\) to both
\(U_+\) and \(U_-\). The physical normal-channel theorem [L],
Lemma N.1, gives
\[
                         \operatorname{dist}(A,D)=1
\]
on the original \(A-U_3-D\) channel, so \(A\) cannot touch \(D\),
even at a zero-weight pair.

Finally \(X\) cannot touch \(D\). The boundary centers are in their
actual cycle order \(X,A,D,B\), by the full physical order in [T]
and its direct force-polygon input. Both angular arcs from \(X\)
to \(D\) contain another physical boundary center, namely \(A\)
or \(B\). The all-physical boundary contact rule in [A], Theorem 3.2,
requires a touching pair to be consecutive along an empty minor arc.
It therefore excludes the pair \(X,D\).

These are all other core bodies. The two positive neighbors \(B,U_3\)
do touch \(D\), proving the corollary. The actual central square and
the actual occupied-pocket square may still touch \(D\), possibly
at shared segments or degenerate junctions. No physical-neighbor-two
premise for the full packing is inferred.

## 5. The direct edge at the unique load is not a positive free VV edge

Use additionally the same compatible generic selection as the
accepted mixed shared-block theorem [M]. Its Theorem 6.1 permits a
maximal shared block incident to a positive free vertex/vertex edge
only if that block contains a body with at least two positive
circle-corner coefficients.

Suppose \(D-B\) in (4.1) were a positive free VV edge.
If \(D-U_3\) is a singleton, the maximal shared block at that end
is the singleton body \(D\). This zero-edge block is included in
[M], Section 3: its virtual translation is simply \(Jz_D\);
there are no internal shared-edge work terms. It has one positive
circle atom.

If \(D-U_3\) is shared, its maximal shared block is exactly
\(\{D,U_3\}\). The other edge \(U_3-A\) cannot be shared because
the radial endpoint theorem makes its original application a
strict inner vertex of \(A\), with a strictly exposing normal.
The block again has only the one positive circle atom of \(D\);
\(U_3\) is genuinely unloaded regardless of any physical circle
mask. In either case [M], Theorem 6.1, gives a contradiction.

Thus the direct \(B-D\) contact is an actual side-owned singleton
or a shared segment. The physical local contact convention treats
every point-only vertex/vertex pair as a free VV pair before
selection, so no additional fixed-normal VV case is left over.
This is a statement about the surviving original positive edge.
It changes no actual zero-weight contact or its normal.

## 6. Exact remaining scope

The original full physical remainder is now more precise: in the
two-RR C7 pattern, the unique loaded body has only its two positive
neighbors in the core, its direct edge has a genuine side feature,
and its additional physical neighbors, if any, are among the two
actual completion squares.

The common central square may still block several transmitters.
The radial/unique third transmitter and its occupied exterior square
remain. Neither this no-contact theorem nor the generic feature
join supplies a feasible motion of those extra bodies. No whole
mixed-mask or original coarse-gate closure is asserted.

## 7. Frozen complete inputs

| Label | Complete source | SHA-256 | Role |
| --- | --- | --- | --- |
| [T] | RADIAL_RADIAL_SIDE_TRANSMITTERS_ARE_TRANSVERSELY_FREE_OF_ALL_BOUNDARY_CORE_BODIES_2026_10_30.md | 658e5ddc2a2f0494510d82057495f74d5274fd053f77e0e7e00724fdd98209ed | Entire RR chart, all-physical boundary-center order, and complete vertical-side contact cover. |
| [A] | CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Used only in this source's Section 4: its Theorem 3.2 is the angular-neighbor rule for all physically boundary squares. |
| [L] | PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md | ec8be96131806c998d8a768526d2deb644c28be72559d34e033c8d07d917ffab | Used only in this source's Section 4: its Lemma N.1 gives exact set distance one for the original channel. |
| [M] | MIXED_SHARED_BLOCK_GENERICITY_AND_COMPLETE_PARALLEL_SHORT_C7_EXCLUSION_2026_10_30.md | e5761145e8f5f83fe4cfab2ddee8be20c75058ef25f8923cc052807a6f52ad77 | Used only in this source's Section 5: its complete Theorem 6.1 includes a singleton block under the original common selection. |
| [N] | RADIAL_RADIAL_TRANSMITTERS_CAN_SLIDE_OUTWARD_AND_CANNOT_FORM_A_CLOSED_TWO_BODY_BLOCKER_NETWORK_2026_10_30.md | 0fbcce339700b2d2e23fa30a516a64c2773e868b90ed60f695fcc93ac4cafff7 | Identifies (4.1) as the exact two-RR short-C7 remainder; Sections 4--5 also apply when that exact pattern is assumed directly. |

The new support lemma and noncontact proof are complete above.
All complete direct inputs have been read, with their full original
scope retained. The discussion with common-certificate supplied
independent arithmetic checks before this source was frozen; a
separate full review is still required for the new combined source.

No original source or checked flag is modified. No numerical search,
orientation grid, computational packing certificate, Lean/Lake
invocation, CI dispatch or remote edit is used.

