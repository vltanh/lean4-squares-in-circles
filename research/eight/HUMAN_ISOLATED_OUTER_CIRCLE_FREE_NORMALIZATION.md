# Isolated outer squares can be made strictly circle-free without changing a minimizing contact graph

**2026-10-12. Exact geometric representative-normalization theorem.**
This is a structural perturbation argument, not a
numeric cap-offset estimate. Its main application
is the k=7, centrally two-contact B2 root,
where the previously proved actual-leaf
argument forces every unstressed spectator
to be **completely isolated**.

## Theorem (circle-free isolated outer representatives)

Let a minimum-radius packing of eight genuine
unit squares, with pairwise disjoint interiors,
be contained in \(D_R\), with
\[
\sqrt2+1/2<R\le\sqrt{9789/2500}<2.
\]
Let T be any **completely isolated actual
square-contact vertex** of its full
square-square contact graph: T has *strict
positive closed-set distance* from every
other square.

Suppose its center p has \(|p|\ge1\)
(an **outer-center isolated square**).
Then there exists an arbitrarily small
translation of **T alone**, leaving all
other squares and all frames fixed, such that

1. T still has center norm **at least one**;
2. T remains **actually isolated** with
   strict positive distance to all other
   squares;
3. **all four true vertices of T**, and
   hence its entire square, lie **strictly
   inside** \(D_R\);
4. every actual square-square contact
   elsewhere in the packing is unchanged,
   so the *entire* actual contact graph
   is identical;
5. the modified eight-square packing
   still attains the **same least
   containing radius \(R\)**.

For finitely many isolated outer squares,
the perturbations may be performed
**successively** so that *all* of them
are strictly circle-free while preserving
every center's outer classification,
all actual contacts and the least
radius.

In particular, in the **k=7,
central actual-degree-two B2 outer-path
root**, the earlier
[HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md](HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md)
implies that a radius minimizer may be
chosen with all \(7-m\) spectators
**both truly isolated and strictly
circle-free**. Every true disk-circle
contact of that representative occurs
on the C-rooted stressed cycle; C
itself is circle-free, so all circle
contacts belong to its stressed
outer square labels.

## Proof

Let \(p\) be T's center and
\(r=|p|\ge1\). Its genuine unit
square has four vertices \(z=p+v\),
where every displacement v has
norm exactly \(1/\sqrt2\).
For any such vertex,
\[
\frac{p}{r}\cdot z
=r+\frac{p}{r}\cdot v
\ge r-\frac1{\sqrt2}>0,                       \tag{1}
\]
because \(r\ge1>1/\sqrt2\).
Thus moving the square center
**radially toward the disk origin**
strictly decreases the squared
distance of **every actual vertex**
for sufficiently small positive
translation length.

More explicitly, for
\(p_\epsilon=p-\epsilon p/r\),
the translated vertices are
\(z_\epsilon=z-\epsilon p/r\),
and
\[
|z_\epsilon|^2-|z|^2
=-2\epsilon\,\frac{p}{r}\cdot z+\epsilon^2
\le-2\epsilon(r-1/\sqrt2)+\epsilon^2<0
\]
whenever
\[
0<\epsilon<2(r-1/\sqrt2).                     \tag{2}
\]
All four true vertex squared norms
are strictly reduced.

There is one **center classification
boundary** to check:
if \(r=1\), the square is
already strictly circle-free.
Indeed every vertex has norm
at most
\[
|p|+1/\sqrt2=1+1/\sqrt2
<\sqrt2+1/2<R,
\]
where the strict comparison is
\(1/2<1/\sqrt2\).
So for r=1 we simply take the
zero translation \(\epsilon=0\).
No outer-to-inner class change occurs.

If \(r>1\) and T is already strictly
circle-free, again no motion is required.
Otherwise choose any sufficiently
small positive epsilon satisfying
both (2) and
\[
0<\epsilon<r-1.
\]
Then the new center norm
\(r-\epsilon>1\) remains outer.
All true vertices have strictly
smaller squared radius than before,
hence strictly less than R².
The *entire* square is strictly
inside the disk because every
point is a convex combination of
its four vertices and the disk is
convex (equivalently, the maximum
norm of the square is attained at
a vertex).

Because T was **actually isolated**,
the finitely many distances from
its closed square to all seven other
closed squares are strictly positive.
Choosing epsilon even smaller than
half their minimum keeps all these
pair separations positive. Every
square other than T remains fixed,
so every other actual contact
and true disk-vertex condition is
unchanged. The actual contact graph
is therefore identical.

The modified collection is a
valid eight-square packing in
the original disk \(D_R\).
Since R was **globally least**
for eight squares, the modified
configuration cannot fit in any
strictly smaller disk. Thus its
least containing radius is still
R (whether or not T itself now
supplies a disk circle vertex).
This proves items 1–5.

To handle multiple isolated outer
squares, apply the same argument
one at a time, choosing a positive
motion smaller than the current
minimum strict pairwise clearance.
Finiteness ensures all required
gaps remain positive at each stage.
Every square keeps its center norm
outer and becomes strictly
circle-free. QED.

## Structural use and exact limitation

This is a **representative selection** theorem:
it does **not** claim an arbitrary
given optimal packing has no
circle-contact isolated squares,
only that there is another optimal
packing with the **same contact
graph and radial center classes**
in which all isolated outer
squares have true disk slack.

In the pure C-two-contact positive
stress path case, the complete
actual contact graph has already
been proved to be exactly the
positive C-rooted cycle plus
isolates. The present normalization
therefore permits the **circle
boundary witnesses to be sought
entirely on the stressed core**,
without discarding the genuine
isolated spectator squares from
the packing inequalities.

This does not prove that the
spectators could be deleted
while preserving n=8
occupancy or that the true
sharp lower radius bound
\(R_8\ge\widehat R\) follows.
The existing S4/k7 full
contact-ring equality case is
not modified or excluded.
