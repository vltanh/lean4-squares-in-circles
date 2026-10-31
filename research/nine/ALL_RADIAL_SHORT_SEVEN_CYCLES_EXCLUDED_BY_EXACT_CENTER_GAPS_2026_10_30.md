# Exact radial-pair gaps exclude every all-radial short seven-cycle

Date: October 30, 2026. Author: joint-pockets continuation.
Input mathematical tree: 3132896f3c306faecfdd69daafb0b577bf7d70a1.

**Status: complete proposed uniform hand theorem, awaiting separate
independent review.** Every physical-two-circle loaded mask of a short
positive C7 is excluded at once, with either transmitter width and with
all actual additional contacts unrestricted. No canonical motion or
physical-neighbor-count hypothesis is used.

The proof gives the exact set distance between any two actual radial
squares in terms of their minor center angle. An original transmitter
channel realizes that set distance, so its actual width fixes the
corresponding angular gap. The physical spoke order identifies these
gaps with the actual consecutive gaps around the cycle; they are not
assigned an arbitrary branch of an inverse trigonometric function.

The same argument excludes every such all-radial short cycle with at
least seven bodies. If all its transmitters are side normal, it excludes
every cycle length, including nonalternating load patterns. These are
whole physical-mask conclusions, not a claim that the remaining unique
corner masks or the original unrestricted n=9 theorem are closed.

## 1. Original full domain and the exact statements

Keep the actual contained unit squares, their disjoint open interiors,
the original compatible physical certificate and the closed window

\[
                \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
                                                               \tag{1.1}
\]

Let an entire positive component be a simple cycle with at least three
loaded bodies. Every loaded body has two physical circle corners.
Either individual circle coefficient may be zero; only its total
load is positive. The word radial below describes that physical
two-corner geometry, not a requirement that its two weights be equal.

Every unloaded vertex is isolated among the unloaded vertices. Thus
it is one genuine true-full-positive-degree-two transmitter between
two consecutive loaded bodies. Its original width is either one or
square root two. It may physically touch the circle with zero circle
weight, and it may have arbitrary additional zero-weight contacts.
All original applications and full shared-side means are retained.

Write t for the number of loaded bodies, k for the number of unloaded
bodies, and m=t+k for the actual number of cycle vertices. The isolated
premise allows k=0. All physical squares outside the positive component
remain present, with arbitrary frames and contacts.

**Theorem 1.1.** This configuration is impossible whenever m is at
least seven. In particular it excludes the entire physical-two-circle
loaded mask of a short C7, simultaneously for four, five or six loads
and every side/diagonal transmitter assignment.

**Theorem 1.2.** If every unloaded transmitter in this same domain
is side normal, the configuration is impossible for every integer
cycle length m.

The statements do not assume that the positive cycle is the complete
physical contact graph. No zero coefficient is promoted to a positive
force, no existing positive force is deleted, and no competing packing
is introduced.

## 2. The actual radial unit and a strict exact angle window

A contained square with two physical circle corners has adjacent
farthest corners and the radial S form

\[
 S_e=[d,d+1]e+[-1/2,1/2]Je,\qquad
 d=\sqrt{R^2-1/4}-1.                                     \tag{2.1}
\]

Its center is \((d+1/2)e\), and its two physical circle corners
are \((d+1)e\pm Je/2\). An opposite pair of farthest corners
would force center zero and radius squared one half, outside (1.1).
The physical classification uses no load equation.

Put

\[
 \rho=\sqrt{d^2+1/4},\qquad
 \phi=\arctan\frac{1}{2d}.
                                                               \tag{2.2}
\]

Here rho is the norm of each inner radial vertex; it is not an
auxiliary radius assigned to the rest of the packing. In particular

\[
       \rho\cos\phi=d,\qquad
       \rho\sin\phi=\frac12.                            \tag{2.3}
\]

The full closed radius window implies the strict bounds

\[
                      \frac9{10}<d<\frac{61}{60}.        \tag{2.4}
\]

For the lower endpoint, the comparison after adding one and squaring
has reserve \((5841-5776)/1600>0\). For the upper endpoint compare
\(1041/256\) with \((121/60)^2\); after multiplication by the positive
denominators the reserve is
\(14641\cdot256-1041\cdot3600=496>0\).
Thus both inequalities in (2.4) remain strict at the original closed
radius endpoints.

We need the following exact improvement of the earlier
\(\pi/8<\phi<\pi/6\) window:

\[
                         \boxed{\frac{\pi}{7}<\phi<\frac{\pi}{6}}.
                                                               \tag{2.5}
\]

For the upper bound, (2.4) gives
\(\tan\phi<5/9<1/\sqrt3=\tan(\pi/6)\), since \(25/81<1/3\).

For the lower bound, (2.4) gives

\[
 d^2<\frac{3721}{3600}<\frac{25}{24},\qquad
                 \tan\phi>\frac{\sqrt6}{5}.              \tag{2.6}
\]

Let \(\theta=\arctan(\sqrt6/5)\), so \(0<\theta<\pi/4\).
For \(u=\tan\theta=\sqrt6/5\), the exact imaginary-part formula
for \((1+iu)^7\) gives

\[
 \begin{split}
 \sin(7\theta)
 &=\frac{u}{(1+u^2)^{7/2}}
                  \left(7-35u^2+21u^4-u^6\right),\\
 7-35\frac6{25}+21\frac{36}{625}-\frac{216}{15625}
 &=-\frac{3191}{15625}<0.
 \end{split}                                                \tag{2.7}
\]

Because \(0<7\theta<7\pi/4<2\pi\), this negative sine forces
\(7\theta>\pi\). Equation (2.6) gives \(\phi>\theta>\pi/7\).
This proves (2.5) without a rounded angle, numerical trigonometric
evaluation or sampled radius interval.

## 3. Exact distance between two physical radial squares

**Lemma 3.1 (full radial-pair distance).** Let A,B be two distinct
contained physical radial squares in (2.1), with disjoint open
interiors. Let their minor center angle be \(\gamma=2a\), where
\(0<a\le\pi/2\). Then

\[
 a\ge\phi,\qquad
 \operatorname{dist}(A,B)
       =2d\sin a-\cos a
       =2\rho\sin(a-\phi).                               \tag{3.1}
\]

If \(a<\pi/2\), the two facing support points attaining this distance
are precisely inner vertices. Their transverse coordinates agree.
At \(a=\phi\) the sets touch at their common inner vertex. At
\(a=\pi/2\) the two inner radial faces are parallel and distance
is \(2d\); no prescribed mean on either face is needed.

*Proof.* Distinct actual radial squares cannot have the same radial
axis direction, because (2.1) would make them identical. Normalize
the bisector of their minor center arc to the positive vertical
axis and write

\[
 e_A=(-\sin a,\cos a),\qquad e_B=(\sin a,\cos a).
                                                               \tag{3.2}
\]

The reflection across the vertical axis sends the entire actual
square A to B. It is used only to describe their existing geometry.
Neither square is moved in the packing.

First suppose \(0<a<\phi\). A point \((0,h)\) lies in the
open interior of A exactly when

\[
                 d<h\cos a<d+1,\qquad h\sin a<1/2.
                                                               \tag{3.3}
\]

There exists such a positive h: the condition \(a<\phi\) gives
\(d/\cos a<(1/2)/\sin a\), and also
\(d/\cos a<(d+1)/\cos a\). Choose h strictly between the common
lower endpoint and the smaller of these two upper endpoints.
Reflection fixes this point and puts it in B's open interior too.
This contradicts disjointness. Hence \(a\ge\phi\).

For \(0<a<\pi/2\), both sine and cosine are positive. The
unique maximum-horizontal support point of A and the unique
minimum-horizontal support point of B are their inner vertices

\[
 \begin{split}
 P_A&=(-d\sin a+\tfrac12\cos a,\ 
                            d\cos a+\tfrac12\sin a),\\
 P_B&=( d\sin a-\tfrac12\cos a,\ 
                            d\cos a+\tfrac12\sin a).
 \end{split}                                                \tag{3.4}
\]

For example \(P_A=d e_A-\tfrac12Je_A\), since the horizontal
projections of both \(e_A\) and \(Je_A\) are negative.
Every point of A lies to the left of \(P_A\)'s vertical support
line, and every point of B lies to the right of \(P_B\)'s.
Their horizontal gap is

\[
                    w_0=2d\sin a-\cos a\ge0,             \tag{3.5}
\]

where the nonnegativity is \(a\ge\phi\). Thus every pair of
points in A and B has distance at least \(w_0\), and the two
points in (3.4) attain exactly that distance because their
vertical coordinates agree. This proves the first distance
formula, including the touching endpoint \(a=\phi\).

When \(a=\pi/2\), (2.1) directly gives two opposite radial
squares with parallel inner faces at horizontal coordinates
\(-d,d\). Their distance is \(2d\), agreeing with (3.5).
The second formula in (3.1) follows from (2.3). QED.

In particular, for any nonnegative distance \(w\) supplied by such
a pair with minor angle at most pi,

\[
                \gamma=2\phi+
                   2\arcsin\frac{w}{2\rho}.              \tag{3.6}
\]

The inverse sine is its usual value in \([0,\pi/2]\).
Indeed \(a-\phi\) belongs to \([0,\pi/2-\phi]\), so
there is no second branch to choose in (3.1). Formula (3.6)
is valid at \(w=0\) as well.

## 4. The unchanged cycle applications realize these set distances

For clarity, the exact original transmission statement is recalled.
Let loaded squares A,B be joined by one original true unloaded
degree-two body U. Its full force equation propagates equal positive
magnitudes and one signed common normal n; its full torque equation
gives the original application difference

\[
                  P_B-P_A=w n,\qquad
                          w\in\{1,\sqrt2\}.              \tag{4.1}
\]

The full square transmission theorem supplies exactly those two
widths. Its original applications can be full side means. Every
point of A satisfies \(n\cdot x\le n\cdot P_A\), and every point
of B satisfies \(n\cdot x\ge n\cdot P_B\). Thus all cross distances
are at least w, while this actual pair attains w. Consequently

\[
                        \operatorname{dist}(A,B)=w.       \tag{4.2}
\]

This is Lemma N.1 of PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md,
not a deletion or contraction of U's occupied square. A direct
positive A--B edge instead has actual set distance zero.

One must also check which center angle appears in (3.6). The whole
mixed-cycle theorem in SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md does
exactly this at the present full original scope:

* The simultaneous physical circle spokes put the loaded center
  directions in their actual cycle order, with one total turn.
* Across any positive-reserve channel, the original endpoint supports
  and proper force polygon put the centers in the opposite closed
  upper quadrants of its outward channel frame. The outward consecutive
  center arc is its actual minor arc, of size in \((0,\pi]\).
* At a direct boundary edge, the physical angular-neighbor theorem
  gives the actual consecutive minor center arc. Its gap is strictly
  less than \(\arccos(9/25)<\pi\).

These are its complete Sections 3--5 conclusions. They permit physical
two-circle loads whose proper concurrences are outside their bodies,
unequal circle weights, individual zero circle coefficients and physical
boundary transmitters of zero total load. No concurrence-inside-body
premise is added here.

Therefore every consecutive loaded pair in the present original
cycle has exactly the angle to which Lemma 3.1 applies. If a channel
had the endpoint angle pi, Lemma 3.1 would give distance \(2d\).
But (2.4) gives \(2d>9/5>\sqrt2\), whereas (4.1) has width at most
square root two. That endpoint is impossible; all actual relevant
angles are strictly below pi. The limiting face case was nevertheless
retained in the distance lemma rather than silently omitted.

## 5. One formula covers direct, side and diagonal gaps

List the loaded bodies in their original positive circular order.
For each consecutive pair let \(w_i=0\) for a direct positive
edge, and let \(w_i\) be the actual width of its one intervening
unloaded transmitter otherwise. Equations (3.6) and (4.2) give

\[
              \gamma_i=2\phi+
                            2\arcsin\frac{w_i}{2\rho}.
                                                               \tag{5.1}
\]

Every term is an actual geometric consecutive gap; hence

\[
                              \sum_{i=1}^t\gamma_i=2\pi.
                                                               \tag{5.2}
\]

The complete three-value cover is:

| Original actual connection | Reserve \(w_i\) | Exact or necessary center gap |
| --- | ---: | --- |
| Direct loaded/loaded edge | \(0\) | \(\gamma_i=2\phi\) |
| One side-normal transmitter | \(1\) | \(\gamma_i=4\phi\) |
| One diagonal transmitter | \(\sqrt2\) | \(\gamma_i>4\phi\) |

For the middle row, (2.3) gives \(1/(2\rho)=\sin\phi\);
since \(0<\phi<\pi/2\), its inverse sine is exactly phi.
The last row follows by strict monotonicity of inverse sine.
Its argument is legitimate: either it comes from the actual distance
in Lemma 3.1, or directly \(\rho^2=d^2+1/4>53/50>1/2\)
gives \(\sqrt2/(2\rho)<1\). No claim that a diagonal radial-pair
channel can actually be realized is required for this necessary bound.

Because the unloaded vertices are isolated, there are precisely k
positive-reserve gaps and \(t-k\) direct gaps. The actual number of
cycle bodies is \(m=t+k\). Summing the table gives

\[
            2\pi=\sum_i\gamma_i
                  \ \ge\ 2\phi(t-k)+4\phi k
                  =2\phi m.                             \tag{5.3}
\]

This counts original bodies through their full actual widths; it
does not insert fictitious edges or assign a unit charge to a
branching network.

## 6. Whole-mask and size-independent contradictions

If \(m\ge7\), equations (2.5) and (5.3) give

\[
                      2\pi\ge2\phi m
                                 \ge14\phi>2\pi,
                                                               \tag{6.1}
\]

a contradiction. This proves Theorem 1.1, including either width
at every isolated transmitter.

If every transmitter is side normal, all inequalities in the gap
table are equalities. Equations (5.2)--(5.3) then give

\[
                          m=\frac{\pi}{\phi}.
                                                               \tag{6.2}
\]

But (2.5) places the right side strictly between six and seven.
No integer m satisfies (6.2). This proves Theorem 1.2 for every
cycle length, including k=0 and every mixed direct/channel pattern.

In particular, the short-C7 load arrangements need no separate
word-by-word enumeration. Whether \((t,k)\) is \((4,3)\), \((5,2)\)
or \((6,1)\), their same total is seven, and (6.1) excludes the
entire all-physical-radial loaded mask. Arbitrary extra physical
contacts, zero-weight circle corners, original shared means and
both completing actual squares cannot change these fixed set
distances or create another branch of the actual circle order.

For C7, this result says every surviving short cycle must have at
least one loaded body with a unique physical circle corner. It does
not assert that such a body's two positive contacts are vertex-owned,
that it has no extra physical neighbor, or that it admits any of the
canonical motions in other sources. Those separate premises remain.

A long unloaded run is outside this theorem. In particular a reserve
two channel is not charged by twice the side-gap increment without
proof: its exact inverse-sine contribution differs. The original
record-radius long-run configurations are not excluded by applying
the isolated-transmitter count beyond its stated domain.

## 7. Complete direct inputs and verification boundary

| Complete direct source | SHA-256 | Literal use |
| --- | --- | --- |
| SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md | 5dac2a88ac992ab72247e76eafcc5ee0fb1ad57a2ec4b11015d0caf07ec87635 | The full mixed simple-cycle properness, actual loaded center order and outward consecutive channel minor-arc statement; no inside-concurrence premise. |
| PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md | ec8be96131806c998d8a768526d2deb644c28be72559d34e033c8d07d917ffab | Exact original degree-two width propagation and physical set-distance realization, Lemma N.1 and the two square width alternatives. |
| RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md | 2d78bc2892c11e58007881ff84d57cc6606dce201bb46d412ef216c12577191e | Existing physical radial frame and full window bounds; its width-one radial-pair gap agrees with the complete distance formula proved here. No pocket capacity is needed for this proof. |

All three complete sources were read. The radial-pair distance lemma,
the strict pi/7 angle bound, the diagonal-inclusive gap comparison and
the entire integer/cycle join are proved in this manuscript. Earlier
accepted physical embedding and certificate prerequisites retain their
original scopes and transitive review obligations.

Root suggested extending the initial all-side count to both genuine
widths by the inverse-sine radial-pair formula. The author independently
derived the full actual-square distance lemma and its overlap/equality
cases before making that join. This author record is not an independent
review; separate full source review is required before adoption.

No fine or coarse ledger flag is changed here. No numerical pose or
angle search, mesh, computational packing certificate, Lean/Lake
invocation, CI dispatch, metadata edit or remote write was used.
