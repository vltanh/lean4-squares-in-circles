# Simultaneous rotations exclude singleton-contact cycles with complete moving stars

Date: October 30, 2026. Author: joint-pockets continuation.
Comparison tree: `4d2b3d62ce489b3251f0241d6c592e868fd7a410`.

**Status: complete proposed uniform hand exclusion, awaiting independent
review.** The preceding one-body rotation required both positive contacts
of its moving loaded body to expose vertices of that body. This theorem
allows loaded bodies to own sides at their contacts: neighboring vertex
suppliers rotate faster in a compatible simultaneous motion.

The theorem excludes every positive simple cycle having both loaded and
unloaded vertices, under the complete physical hypotheses below. It covers
both side and diagonal transmitters, every cycle length, and every load
arrangement. In particular it treats the four-, five-, and six-loaded
short-C7 classes simultaneously, without a side/diagonal subdivision.

The hypothesis about all actual contacts is essential. Every moving body
must have exactly its two positive cycle neighbors as actual physical
neighbors, and its incident contacts must be singletons. Side transmitters
stay fixed and may have additional zero-weight physical contacts. Physical
circle corners of unloaded bodies are retained. No unrestricted short-C7
parent or original ledger cell is claimed closed.

## 1. Original objects and exact hypotheses

Fix a finite original packing in the origin-centered disk `D_R`, first
minimizing R and then `Phi=sum_i |c_i|^2`. Retain its original physical
force-and-torque certificate. Suppose an entire positive body-pair
component is a simple cycle, with at least two loaded and at least one
unloaded vertex. Every vertex therefore has full positive pair degree two.

For the geometric argument use the slightly larger open interval

\[
                    \sqrt2<R<\frac3{\sqrt2}.                \tag{1.1}
\]

The closed project window `79/40<=R<=sqrt(1105)/16` lies strictly
inside (1.1). At each loaded vertex assume:

1. There is exactly one physical circle corner z, with its actual
   coefficient positive. A second physical corner with zero coefficient
   would violate this hypothesis.
2. The original two positive force lines are nonparallel, with their
   genuine proper concurrence

   \[
     q=\tau z\in S,\quad 0<\tau\le1,\qquad
     p_i-q=\alpha_i n_i,\quad \alpha_i\ge0.                 \tag{1.2}
   \]

   Here `p_i,n_i` are the original actual applications and outward
   normals. In the project window these local conclusions are supplied
   by `FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md`, Lemma 1.1, once true degree
   and nonparallelism have been established.

At an unloaded vertex the full physical two-force theorem makes the
transmission either side normal, of width one, or diagonal, of width
`sqrt(2)`. This follows directly from opposite equal forces and torque:
the opposite support applications must differ parallel to their normal;
for a non-side normal they are opposite vertices, so the normal must
be a diagonal. Their original applications and any actual side means
remain fixed.

Define the **moving set M** to consist of all loaded bodies and all
diagonal unloaded transmitters. Keep side transmitters and every other
original packing square fixed. Impose these complete physical conditions:

* Each member of M has exactly two actual physical neighboring squares,
  namely its two original positive cycle neighbors. Thus it has no
  additional zero-weight physical contact that is omitted from the motion.
* Every physical contact incident to M is a singleton. In particular no
  positive shared segment is rotated away without its endpoint constraints.
* At a vertex/vertex singleton, the original selected separator strictly
  exposes the common vertex in both bodies. This is the existing strict
  point-normal convention, not a new post-extraction choice.

A singleton that is a vertex of one body and lies inside a side of the
other has a fixed side owner and a strict vertex supplier. The vertex is
indeed uniquely exposed in the side normal: otherwise an adjacent side
of the vertex supplier would be collinear with the other side through
an interior point, producing a positive common segment. All singleton
contacts incident to M therefore have either one side owner and one
strict vertex supplier, or two strict vertex suppliers.

## 2. Rotation centers for diagonal unloaded bodies retain their circle masks

Put `sigma=1/sqrt(2)`. For a diagonal transmitter choose the unit
transmission direction d and let `e=Jd`. Its actual contact vertices are

\[
                       p_\pm=c\pm\sigma d.                 \tag{2.1}
\]

If it is physically circle-clear, choose its rotation center to be
`q=c`. Both ports then have positive normal-line coefficients sigma,
and containment persists under any sufficiently small rotation.

If it physically touches the circle, neither port in (2.1) can be on
that circle. A containing-circle point cannot belong to two contained
squares: the inward radial segment at that point lies inside each
square that contains it. Thus a circle corner has to be one of the
other two vertices. Choose the sign of e so it is

\[
                     z=c+\sigma e,\qquad c=x d+y e.
\]

Its squared norm must strictly exceed those of both contact ports.
The squared-norm differences are `2sigma(y-x)` and
`2sigma(y+x)`. Therefore

\[
                            y>|x|\ge0.                      \tag{2.2}
\]

The opposite remaining vertex `c-sigma e` has strictly smaller norm
as well. Thus this is the unique physical circle corner; no zero-weight
physical corner has been discarded. Choose

\[
  q=\tau z,\qquad \tau=\frac{y}{y+\sigma}\in(0,1),
  \qquad q-c=-\frac{\sigma x}{y+\sigma}d.                   \tag{2.3}
\]

By (2.2), this point lies strictly between the two actual contact
vertices in (2.1). Both original outward normals are `d,-d`, and
both coefficients in `p-q=alpha n` are strictly positive.

Consequently every moving diagonal transmitter has a center q on its
actual force chord with positive port coefficients. If it touches the
circle, q is a positive inward multiple of its actual unique circle
corner. This choice changes no normal, weight, application, or degree;
it specifies only the center of the proposed physical rotation.

## 3. A vertex supplier never has zero normal-line coefficient

The diagonal moving bodies already have strict positive coefficients.
We next prove the same for every loaded body at a contact where it
supplies a vertex. Suppose instead `p=q` at such a contact.

Use the loaded square's own orthonormal coordinates, with its unique
circle corner `z=(a,b)` and square `[a-1,a] x [b-1,b]`.
Uniqueness gives `a,b>1/2`, and `a^2+b^2=R^2`. Since `q=tau z`
is a physical vertex and cannot be the unshareable circle corner,
the only possibility is

\[
 a=b=R/\sqrt2,\qquad q=(a-1,a-1).                         \tag{3.1}
\]

The two adjacent vertices cannot be positive multiples of z. For
the opposite vertex, proportionality forces `a=b`, proving (3.1).
This is the radial inner vertex of a radial-diagonal square.

Consider its other positive application p'. If `p'!=q`, (1.2)
makes the outward normal a positive multiple of `p'-q`. Both own
coordinates of this vector are nonnegative. If both are positive,
that normal strictly exposes the outer circle corner, which cannot
be shared. If one coordinate is zero, the support is an outer
side of the square. Its support coordinate is `a=R/sqrt(2)`.
A neighboring unit square on the outward side has width at least
one and would therefore contain a point with projection at least
`a+1>R`; the last inequality follows from `R<2+sqrt(2)`, which
is weaker than (1.1). This is also impossible.

Hence both applications equal q. Each original normal strictly exposes
that vertex, by the singleton and point-normal hypotheses in Section
1. These are all actual physical contacts of this loaded body. The
single-body complete-contact rotation theorem therefore applies with
both coefficients zero. Equivalently, directly rotate that body about
its fixed contact vertex q: the two strict fixed separators persist,
its circle corner moves inward, and all noncontacts remain separated.

Writing `c=(R-sigma)e` and `q=(R-sqrt(2))e`, one has

\[
        \det(q,c)=0,\qquad
        q\cdot(c-q)=(R-\sqrt2)\sigma>0.
\]

The exact Phi change is `2q dot(c-q)(cos(theta)-1)<0` for small
nonzero theta, contradicting the original canonical minimum. This
also follows from Theorem 3.1 of the preceding rotation manuscript.
We have proved:

\[
 \text{every moving vertex supplier has }p-q=\alpha n
                  \text{ with }\alpha>0.                 \tag{3.2}
\]

An owned-side coefficient may still be zero; it is not discarded.

## 4. The contact ownership graph admits an open cone of angular rates

At each singleton having a side owner, orient an arrow from the vertex
supplier to the side owner. Retain only arrows whose endpoints both
belong to M. Vertex/vertex contacts contribute no arrow. This directed
graph has no directed cycle.

Indeed it is a subgraph of the original simple cycle. If a side
transmitter occurs, removing that fixed vertex breaks the underlying
cycle into paths. If there is no side transmitter, the original cycle
still contains an unloaded vertex, now a moving diagonal transmitter.
It supplies strict vertices at both incident contacts, and therefore
has no incoming ownership arrow. A directed cycle in the underlying
simple cycle would have to use every original vertex and give each
one an incoming arrow, which is impossible.

For an arrow `i->j`, write the original common normal n outward from
the vertex supplier i. At their actual common point p, put

\[
                   p-q_i=\alpha n,\qquad
                   p-q_j=-\beta n,\qquad
                   \alpha>0,\quad\beta\ge0.               \tag{4.1}
\]

Choose one positive angular rate `a_i` for every member of M, with

\[
       a_i>\left(1+\sqrt{1+\beta/\alpha}\right)a_j
                  \quad\hbox{on each arrow }i\to j.       \tag{4.2}
\]

Such choices form a nonempty open subset of `R^M`. To construct one,
process the finite acyclic graph from its sinks backward. After all
successor rates have been chosen, choose the current rate strictly
larger than the finitely many specified multiples of those rates,
and positive. All inequalities are strict, so a neighborhood of
the resulting rate vector also satisfies them.

Each fixed side transmitter is always the side owner, never the vertex
supplier, at its incident contacts in the present singleton domain.
Its rate can be regarded as zero. Contacts with it do not impose a
positive lower bound on any moving side-owner rate.

## 5. Every rate vector in that open cone gives a complete feasible motion

For a fixed rate vector from Section 4, rotate each moving square i
about its chosen fixed point q_i through angle `a_i theta`:

\[
                S_i(\theta)=q_i+R_{a_i\theta}(S_i-q_i).     \tag{5.1}
\]

All other original squares stay fixed. We prove feasibility for both
signs of every sufficiently small theta.

### 5.1 Vertex against a fixed side transmitter

Keep the original separator normal n fixed. Its unique vertex label
in the moving body remains uniquely exposed for small theta. The
support displacement is exactly

\[
                          \alpha(\cos(a_i\theta)-1)\le0.
\]

So the original separating halfplanes still keep their open interiors
disjoint.

### 5.2 Two moving strict vertices

Keep their original separator n fixed. Their two opposite exposed
vertex labels persist. The difference of the two supporting values,
relative to their common value at zero, is

\[
       \alpha(\cos(a_i\theta)-1)
               +\beta(\cos(a_j\theta)-1)\le0.
\]

Here both coefficients are positive by Section 3, but nonnegativity
alone is enough for this exact separation.

### 5.3 A moving vertex against a moving owned side

Use the side owner's genuinely rotating separator
`n_theta=R_(a_j theta)n`. Its rotated actual point on that side is
`q_j-beta R_(a_j theta)n`. The vertex supplier's rotated contact
vertex is `q_i+alpha R_(a_i theta)n`. Their difference of
supporting values is exactly

\[
 F_{ij}(\theta)
   =-(\alpha+\beta)\cos(a_j\theta)
      +\alpha\cos((a_i-a_j)\theta)+\beta.                 \tag{5.2}
\]

It has zero value and first derivative at zero. Its second derivative
there is

\[
 F_{ij}''(0)
       =-\alpha a_i^2+2\alpha a_i a_j+\beta a_j^2<0,       \tag{5.3}
\]

where the strict inequality is exactly (4.2). Hence (5.2) is
negative for all sufficiently small nonzero theta of either sign.
The original vertex is still uniquely exposed in the rotating normal
by continuity. The other body's side is its actual rotated supporting
side. Thus this negative gap proves separation of the full rotated
squares, not just of the two named points. The case `beta=0` is
included in (4.2)--(5.3).

### 5.4 Every remaining original constraint

All actual contacts touching a moving body have just been treated:
each member of M has exactly its two positive physical neighbors.
Pairs disjoint as closed squares at theta=0 have a positive distance,
and stay disjoint for sufficiently small theta. Pairs of fixed bodies
are unchanged. There are finitely many pairs.

For a loaded body the unique circle corner and its q satisfy (1.2).
For a physically boundary diagonal transmitter they satisfy (2.3).
In either case the exact circle formula is

\[
 |q+R_{a_i\theta}(z-q)|^2
       =R^2-2\tau(1-\tau)R^2(1-\cos(a_i\theta))\le R^2.
\]

All other vertices were strictly inside and remain so locally.
All vertices of a physically circle-clear diagonal transmitter stay
inside by continuity. Fixed bodies retain their full physical circle
masks. Convexity of the disk turns the vertex checks into containment
of each whole actual square. Intersecting finitely many neighborhoods
proves a genuine full-packing feasible curve for both signs of theta.

No stress support is required to persist in the competing packing.
The comparison is with the original `(R,Phi)` minimum on all actual
packings, not within a presumed fixed-contact family.

## 6. The open family of motions makes every loaded center radial

At a moving body define `B_i=det(q_i,c_i)`. Differentiating its
actual center path in (5.1) gives

\[
                      \Phi'(0)=-2\sum_{i\in M} a_i B_i.    \tag{6.1}
\]

Since both signs of theta are feasible, canonical minimality forces
(6.1) to be zero for every rate vector in the nonempty open cone of
Section 4. A real linear functional that vanishes on a nonempty open
set is identically zero. Consequently

\[
                              B_i=0\quad(i\in M).          \tag{6.2}
\]

At a loaded body, q is a positive multiple of its unique circle
corner z. Thus c is collinear with z. Since `|z-c|=sigma` and
the opposite vertex is also in `D_R`, the only possible alignment is

\[
                 z=Re,\qquad c=(R-\sigma)e                 \tag{6.3}
\]

for a unit e. Indeed writing `c=kappa z`, a nonpositive kappa
would give `|z-c|>=R>sigma`; kappa=1 gives zero offset, and
kappa>1 puts `2c-z` outside the disk. Hence `0<kappa<1`,
which gives (6.3).

This argument uses only the first derivative of Phi over an open
family of motions. It does not incorrectly infer separate signs of
the individual second derivatives from one combined inequality.

## 7. Every original loaded port now has a uniform projection bound

Fix a loaded body after the necessary alignment (6.3). Put

\[
              r=R-\sigma,\qquad a=R/\sqrt2.
\]

In its own side coordinates the actual square is
`[a-1,a] x [a-1,a]`, with outer circle corner `(a,a)`.
An actual contact in the relative interior of an outer side would
have support value a and leave a unit neighbor a point with projection
at least `a+1>R`; this is impossible. The outer circle vertex cannot
be shared either.

The inner radial vertex cannot be a positive application. Section 3
has excluded a zero coefficient at a vertex application. If this
inner vertex p had `p-q=alpha n` with `alpha>0`, the proper radial
q in the square would force `n=-e`. The original force equation

\[
                         \mu n+\nu n'+2\lambda R e=0
\]

would then make the other positive normal n' radial as well,
contradicting the assumed nonparallel force lines.

Every original application is therefore either on an inner side or
at a lateral vertex. On an inner side its outward normal is the
negative own axis, so exactly

\[
                              p\cdot n=1-a.                \tag{7.1}
\]

For a lateral vertex write `q=(r+delta)e`. Proper inclusion of
q in the square gives `-sigma<=delta<=sigma`. The genuine strict
vertex exposure improves this to `-sigma<delta<sigma`. With
`t=Je`, its actual point and normal are

\[
     p=r e\pm\sigma t,\qquad
     n=\frac{-\delta e\pm\sigma t}
                            {\sqrt{\delta^2+\sigma^2}}.
\]

Consequently

\[
 p\cdot n=g(\delta)
       =\frac{\sigma^2-r\delta}{\sqrt{\delta^2+\sigma^2}}
                         >g(\sigma)=1-\frac R{\sqrt2}.    \tag{7.2}
\]

For completeness, `g'(delta)=-sigma^2(r+delta)/
(delta^2+sigma^2)^(3/2)<0` throughout this interval, because
`r+delta>=R-sqrt(2)>0`. Unlike the one-body survivor theorem,
no assumption `delta>=0` is needed.

Equations (7.1)--(7.2) establish the uniform original-port bound

\[
             \boxed{p\cdot n\ge1-\frac R{\sqrt2}>-\frac12}
               \quad\hbox{at every loaded positive port}. \tag{7.3}
\]

Both side-owned and strict vertex contacts are included. The last
inequality is strict by the upper bound in (1.1).

## 8. An actual unloaded run contradicts this bound

Take any maximal nonempty run of unloaded cycle vertices, with loaded
endpoints A,B. They are distinct because there are at least two loads.
Every internal vertex has original full positive degree two and zero
circle load. Force balance preserves one common positive magnitude
and signed normal n through the run. Torque makes each consecutive
application difference its actual support width times n. These widths
are positive and at least one. Thus the genuine application telescope
is

\[
                  p_B-p_A=L n,\qquad L\ge1.                 \tag{8.1}
\]

The original outward normal at A is n and that at B is `-n`.
This is the exact physical normal-channel identity, with no internal
body removed or assigned a fictitious degree. Taking its scalar
product with n and using (7.3) gives

\[
\begin{split}
 L&=-p_B\cdot(-n)-p_A\cdot n\\
  &\le 2\left(\frac R{\sqrt2}-1\right)
       =\sqrt2 R-2<1,                                    \tag{8.2}
\end{split}
\]

contradicting (8.1).

**Theorem 8.1 (all-width simultaneous-rotation cycle exclusion).**
No original radius/Phi-minimizing packing in (1.1) has a full positive
simple-cycle component satisfying Section 1. Every cycle size,
every placement of loaded vertices, every side/diagonal transmitter
assignment, and every physical circle mask of an unloaded body is
included. Loaded bodies may own sides; they were not artificially
treated as vertex suppliers at all contacts.

**Short-C7 consequence.** Throughout the closed project window,
all four-, five-, and six-loaded short-seven-cycle patterns are
excluded at once whenever every loaded body has one physical circle
corner and the moving bodies have the full singleton/two-actual-neighbor
conditions of Section 1. The exact two additional original squares
remain fixed and present throughout the proof. They may physically
touch fixed side transmitters; they may not be ignored if they
touch any moving body.

## 9. Direct inputs and unchanged boundary of the result

| Source | SHA-256 | Consumed statement |
| --- | --- | --- |
| `CANONICAL_ROTATION_OF_UNBLOCKED_UNIQUE_CIRCLE_TWO_FORCE_BODIES_2026_10_30.md` | `94f4d2ed11af153196d7e68644c5a21b0f3e4619abcb2b042d54a00d1450bda3` | Full original feasible-rotation and Phi comparison; Section 3 uses its zero-coefficient single-body case, also reconstructed explicitly above. |
| `ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md` | `be6636a018df64f52a48f382dc21b453a208d0a929fdeaa7cb5bef9c30822c06` | Existence and exact original scope of the `(R,Phi)` minimum. |
| `FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md` | `7d0c4092ba133a832cf963f329b1c3a6442a3260576f16319293835b39e6d282` | Local proper concurrence for the true-degree-two, nonparallel loaded caller, including its one-physical-circle-corner inclusion. |
| `PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md` | `ec8be96131806c998d8a768526d2deb644c28be72559d34e033c8d07d917ffab` | Actual normal-channel telescope; the needed force, torque and width steps are repeated here. |

All four direct sources were read in full. The circle containment,
ownership graph, zero-coefficient case, exact moving-side constraint,
open rate cone, first-derivative conclusion and final port bound are
proved above. No new generic normal selection or mean substitution is
made after extraction.

The remaining unrestricted C7 alternatives include additional physical
contacts at a proposed moving body, positive-length shared segments,
and two physical circle corners at a loaded body. Those are actual
geometric cases, not removable zero coefficients. This manuscript
does not claim that a suitable entire cycle necessarily satisfies
the extra physical hypotheses. No original fine/coarse flag changes,
equality classification, or full n=9 closure is asserted.

No numerical pose search, mesh, computational packing certificate,
Lean/Lake invocation, CI dispatch, metadata change or remote mutation
was used. The source awaits a separate complete nonauthor review.
