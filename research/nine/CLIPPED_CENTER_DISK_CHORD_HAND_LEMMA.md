# A guarded chord of the excluded original-center disk

Let the same original pair difference be `d=(dx,dy)`, and suppose physical
separation proves `||d||>=r>0`. For unit squares one may take `r=1`; the proved
relative-orientation lower bound may supply a larger exact rational radius.

Choose signs `sx,sy` and put `u=sx*dx`, `v=sy*dy`. Suppose independently proved
pair intervals give `u<=a`, `v<=b`, and the exact guard `a^2+b^2<r^2` holds.
Choose exact rational nonnegative numbers `p,q` such that

\[
p^2\leq r^2-a^2,\qquad q^2\leq r^2-b^2,
\qquad b+p>0,\quad a+q>0.
\]

Then the following closed linear inequality is necessary:

\[
\boxed{(b+p)u+(a+q)v\leq ab-pq.}
\]

To prove it, write `A=b+p>0`, `B=a+q>0`. The opposite strict halfplane,
intersected with `u<=a,v<=b`, is the portion of the triangle with vertices

\[
P_0=(a,b),\quad P_1=(-q,b),\quad P_2=(a,-p)
\]

strictly on the `P_0` side of its chord `P_1P_2`. Indeed both chord endpoints
satisfy `Au+Bv=ab-pq`, and the corner's excess is exactly `AB>0`. The two upper
bounds and the strict chord comparison imply `u>-q,v>-p`, so there is no
unbounded extra region. Equivalently define the three barycentric coefficients

\[
\mu=\frac{a-u}{a+q}\geq0,\qquad
\nu=\frac{b-v}{b+p}\geq0,\qquad
\lambda=1-\mu-\nu
=\frac{Au+Bv-(ab-pq)}{AB}>0.
\]

Their sum is one, and direct substitution gives
`(u,v)=lambda*P_0+mu*P_1+nu*P_2`.

The exact guards give `||P_0||^2<r^2` and `||P_1||^2,||P_2||^2<=r^2`.
Convexity of squared norm therefore gives
`||(u,v)||^2 <= lambda*||P_0||^2+mu*||P_1||^2+nu*||P_2||^2 < r^2`.
The positive corner weight makes this upper bound strict. This contradicts
`||d||>=r`. Equality on the chord is retained.

The implementation generates all four signed upper corners for each of the
36 original pairs, emitting a row only when the exact corner and positive
coefficient guards hold. Directed integer-square-root lower enclosures give
`p,q`; all three vertex norms, both chord equalities, and the positive corner
gap are checked in rational arithmetic and recorded. No separating axis,
orientation sign, or placement alternative is selected by this rule.

Unlike a coordinatewise quadratic secant, this inequality uses the convex
hull of the excluded disk region inside a proved pair quadrant. Its premises
must come from the actual original path and certified inherited difference
bounds. A numerical point never supplies a bound or a guard.

The frozen exact row source is `clipped_center_disk_chords.py`, SHA256
`1f72cd4727af4a4ffa5c22e67e0de4d82cc5f4acbf15d3f9ccd038097023b694`.
The single targeted pass leaves both whole shallow parents open. It produces
one candidate terminal on existing A source path43, with no new branches;
that overlay requires its own independent replay and does not change the
earlier frozen 818-terminal/22-pending checkpoint by itself.
