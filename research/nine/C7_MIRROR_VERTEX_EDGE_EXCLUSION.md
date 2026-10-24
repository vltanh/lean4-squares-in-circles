# A selected positive C7 has only side-axis-owned contacts

**Status: complete hand selection argument; independent full hand audit passed.**
In the remaining radius range

\[
                 \frac{\sqrt{17}}2\le R\le\frac{\sqrt{1105}}{16},
 \tag{1}
\]

the physical common normals can be selected before stress extraction
so that every edge of an all-boundary positive C7 is an actual side
axis of at least one incident square. This completes the free-normal
reduction. It does not assert one owner per square: bodies with zero
or two owned edges, positive-length shared sides, and every physical
circle mask remain in the all-owned domain.

The new step excludes the sole free-edge type left by
`C7_RADIAL_VERTEX_EDGE_EXCLUSION.md`: the mirror contact between the
unique-corner ends of two pinned blocks of length two. Both limiting
normal directions at that contact are retained. They require
incompatible shared-side means at a radial anchor whose other
contact has a fixed normal. At least one limiting direction therefore
gives a strict cone failure, which persists for nearby strict common
normals.

## 1. The exact mirror module and the fixed anchor contact

Put

\[
 q=R^2,\qquad c=\sqrt{q-9/4},\qquad
 a_0=\sqrt{q-1/4},\qquad d=a_0-1,
\]

\[
                  \phi=\arctan\frac{3}{2(c-1)}.
 \tag{2}
\]

The bounds needed below are

\[
 \sqrt2\le c\le23/16<3/2,\qquad a_0\ge2,
 \qquad d<c<a_0,
 \qquad \frac\pi4<\phi<\frac\pi2.
 \tag{3}
\]

The strict inequality d<c follows from
\(c^2-d^2=2a_0-3>0\).

The pinned-edge classification gives a radial anchor A, followed in
positive circular order by its parallel unique-corner neighbor B:

\[
 A=[d,d+1]\times[-1/2,1/2],\qquad
 B=[c-1,c]\times[1/2,3/2].
 \tag{4}
\]

B has unique circle corner \(z_B=(c,3/2)\). Its free contact with
the other length-two block is at

\[
                         p=(c-1,3/2).
 \tag{5}
\]

The other block is the reflection of this one in the line through
the origin and p; its radial anchor has angle \(2\phi\). The
genuine common-normal interval, directed from B to the other
unique-corner body, is exactly

\[
                         2\phi\le\arg n\le\pi.
 \tag{6}
\]

Indeed B's outward vertex cone is \([\pi/2,\pi]\). Reflection in
the line at angle \(\phi\) sends this cone to the other body's
outward cone; taking its negative gives the other inward cone
\([2\phi,2\phi+\pi/2]\). Their intersection is (6). Its interior
is nonempty.

Both circle-corner multipliers of A are positive by the pinned-block
theorem. Its shared-side contact with B has application

\[
                        (x,1/2),\qquad d\le x\le c.
 \tag{7}
\]

Its other contact is point-only because this is a maximal shared-side
block. That contact must be at the opposite inner vertex

\[
                           p_-=(d,-1/2).
 \tag{8}
\]

For completeness, the outer radial face is excluded by the width
bound, the inner radial face by the shallow-contact lemma, and the
outer circle vertices cannot be shared. An application on the same
tangential face as (7), including its inner vertex, has the same
origin-moment sign and cannot balance torque. A contact in the
relative interior of the opposite tangential face would give two
tangential forces, forcing both circle weights to vanish. This
leaves (8).

The radial/radial exclusion has already removed every free edge at
A. More directly, the vertex-shell lemma says that a vertex/vertex
neighbor at (8) would itself be radial, producing such an excluded
edge. Thus the other contact is a genuine vertex/side contact with
a unique physical normal. Write its incoming directed normal as

\[
                       n_-=(s,t),\qquad s,t\ge0,
 \qquad s^2+t^2=1.
 \tag{9}
\]

This normal is fixed by the physical packing, independently of the
normal chosen at (5).

## 2. The two limiting free normals force two different shared means

As in the radial-edge exclusion, normalize the common positive
origin moment of the directed C7 forces to H=1. Take

\[
                  n=(-C,S),\qquad C>0,\quad S\ge0
 \tag{10}
\]

in the interval (6). Let its magnitude at B be \(\mu\), let the
incoming shared-side magnitude be \(\nu\), and let B's circle
multiplier be \(\lambda\ge0\). Translation gives

\[
          \nu e_y-\mu(-C,S)-2\lambda(c,3/2)=0,
\]

and hence

\[
             2\lambda c=\mu C,\qquad
             \nu=\mu\left(S+\frac{3C}{2c}\right).
\]

The two origin moments give

\[
                  \mu\bigl((c-1)S+3C/2\bigr)=1,
 \qquad           \nu x=1.
\]

All these denominators are positive throughout the closed interval
(6). Consequently the necessary shared mean is the continuous
function

\[
       x(n)=c\frac{(c-1)S+3C/2}{cS+3C/2}
            =c-\frac{cS}{cS+3C/2}.
 \tag{11}
\]

At the endpoint \(n=-e_x\), this gives

\[
                              x=c.
 \tag{12}
\]

At the other endpoint, \(\arg n=2\phi\), use

\[
 \frac SC=-\tan(2\phi)
          =\frac{3(c-1)}{9/4-(c-1)^2}.
\]

Substitution into (11) gives

\[
       x=x_*:=c\frac{c^2-2c+13/4}{c^2+5/4}.
 \tag{13}
\]

The means (12)--(13) are forced by the unique-corner body's full
translation and torque equations. They are not choices of contact
applications.

## 3. A fixed anchor normal cannot support both endpoint means

Moment normalization at A fixes the incoming magnitude in (9) to
\(1/(dt+s/2)\), while the outgoing shared-side magnitude is
\(1/x\). Its circle resultant m would therefore satisfy

\[
                 2m=\frac{(s,t)}{dt+s/2}-\frac1x e_y.
 \tag{14}
\]

Every nonnegative combination of A's two circle corners
\((a_0,\pm1/2)\) satisfies

\[
                            |m_y|\le\frac{m_x}{2a_0}.
 \tag{15}
\]

If s=0, use the limiting mean x=c from (12). Then (14) has zero
radial component and strictly positive transverse component, since
d<c. This already violates (15) strictly, and the violation persists
near that endpoint. It remains to treat s>0. Put k=t/s, including
k=0. Substitution into (14)--(15), multiplying only positive factors,
yields

\[
                   \left|k(x-d)-\frac12\right|
                       \le\frac{x}{2a_0}.
 \tag{16}
\]

If \(x\le d\), its left side is at least \(1/2\), whereas its
right side is at most \(d/(2a_0)<1/2\). Such a mean is impossible.
For \(d<x<a_0\), equation (16) is equivalent to the closed interval

\[
 \frac{a_0-x}{2a_0(x-d)}
       \le k\le
 \frac{a_0+x}{2a_0(x-d)}.
 \tag{17}
\]

We claim that the intervals (17) at \(x=x_*\) and \(x=c\) are
disjoint. If \(x_*\le d\), the former endpoint already fails
strictly, so suppose \(x_*>d\). Its lower endpoint exceeds the upper
endpoint at c precisely when

\[
 \frac{a_0-x_*}{x_*-d}>\frac{a_0+c}{c-d}.
\]

Since d=a_0-1, expanding both sides shows this is equivalent to

\[
                     x_*<\frac{c(2a_0-1)}{2c+1}.
 \tag{18}
\]

There is a short uniform rational separation. Equations (3) and (13)
give

\[
 c^2-2c+13/4=(c-1)^2+9/4\le625/256,
 \qquad c^2+5/4\ge13/4,
\]

and therefore

\[
 x_*\le\frac{23}{16}\frac{625}{256}\frac4{13}
       =\frac{14375}{13312}<\frac{13}{12}.
 \tag{19}
\]

The last strict inequality is \(172500<173056\). On the other hand,
\(a_0\ge2\) and the increasing function \(c\mapsto3c/(2c+1)\)
give

\[
 \frac{c(2a_0-1)}{2c+1}
       \ge\frac{3c}{2c+1}
       >\frac{21}{19}>\frac{13}{12},
 \tag{20}
\]

using \(c\ge\sqrt2>7/5\) and \(252>247\). Thus (18) holds with
a strict margin throughout (1).

No fixed k can satisfy (16) at both endpoint means. At least one
endpoint of (6) therefore has a strict failure of the necessary
circle cone (15), or has its mean strictly outside the permitted
segment (7). The functions in (11) and (14) are continuous at both
endpoints with positive denominators. That failure persists on a
nonempty one-sided open interval of strict common normals in (6).
Choose the free normal in this interval. The full mirror module then
cannot belong to a positive C7.

## 4. Simultaneous choice before stress extraction

The normal choice depends only on the physical module, R, and the
fixed external normal (9). It does not use a stress multiplier or a
chosen shared-side mean. Equation (11) merely computes a necessary
mean for a prospective moment-normalized stress.

If the physical circle-contact graph is not C7, it cannot underlie
this all-boundary branch. If that graph has a radial/radial edge,
the prior radial-edge selection already excludes a positive C7.
Otherwise every physical radial endpoint's point contact is of
vertex/side type by the shell lemma. Its normal is fixed, so the
choice above can be made for each prospective mirror length-two
edge using its actual physical external contact. All remaining
free-edge candidates are excluded by the previous block and profile
selections.

Different free edges have independent common-normal parameters.
The mirror blocks have nonparallel frames, since their distinct
radial anchors cannot have parallel frames among seven physical
circle-touching squares. Hence the mirror contact is not a matched
four-square junction. The new open restriction is also on a
different physical edge from the radial-run restrictions and the
length-three-pair exclusions. The finite open-dense generic choices
remain available inside the resulting open product.

Uncrossing changes no surviving fixed point normal and only adds
shared-side pairs. Thinning only deletes atom types. Thus every
final mirror edge retains the preselected normal and remains subject
to the strict contradiction in Section 3. No normal is changed after
multipliers are extracted.

## 5. The complete side-axis reduction

Combine the finite generic block selection, pinned-profile theorem,
radial-edge exclusion and the present mirror-edge exclusion. No free
vertex/vertex edge survives in an all-boundary selected positive C7.
Every point edge therefore has an actual side-axis owner; shared-side
edges already have their common side axis.

**Theorem.** In the radius range (1), the necessary planar physical
certificate can be selected so that every edge of any resulting
all-boundary positive C7 has a side-axis owner.

This completes the unrestricted choice-of-normal reduction for this
branch. It preserves all owned-contact patterns, square orientations,
positive-length shared-side means, and zero circle multipliers. The
geometric completion problem remains: show that the resulting C7
cannot contain two further interior-disjoint unit squares. No
one-owner-per-body condition, regularity theorem, center-cover bound,
or completion capacity is inferred here. \(\square\)
