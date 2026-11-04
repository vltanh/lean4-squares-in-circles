# Common-coordinate separation reduces to axis-aligned squares

**Theorem.** Suppose independently rotated unit squares lie in the disk of
radius R about the origin, and every pair has disjoint open projections on
at least one axis of a common orthogonal coordinate frame. There is a packing
of the same number of axis-aligned unit squares in the same disk.

The construction changes centres as well as frames. It preserves the given
coordinate separators. This is a reduction of the entire common-coordinate
class, not an assumption that its squares were parallel. It does not apply to
pairs separated only by oblique owner axes.

## The replacement square

For one original square let its centre be p=(x,y) and its orthonormal frame
be u=(c,s), v=(-s,c). Define

    h = (|c|+|s|)/2,          delta = h-1/2.

Its projection half-width on either common coordinate axis is h, with
1/2 <= h <= sqrt(2)/2 < 1. Define the clamped coordinate map

    f_h(t) = sign(t) max(|t|-delta,0),

where f_h(0)=0. Replace the original square by the axis-aligned unit square
centred at

    p' = (f_h(x), f_h(y)).

The two values of h used for different squares may differ.

## Every coordinate separator survives

For every real t,

    |f_h(t)-t| <= delta.

Consequently the new unit projection interval

    [f_h(t)-1/2, f_h(t)+1/2]

lies inside the original projection interval [t-h,t+h]. If two original
open projection intervals are disjoint, their contained replacement open
intervals are disjoint as well. Thus every selected x or y separator is
preserved. Shared projection endpoints cause no problem because square
interiors, rather than their boundaries, must be disjoint.

## The replacement stays in the disk

Put X=|x| and Y=|y|. The original farthest corner has squared norm

    F = X^2+Y^2+1/2+L,
    L = |p dot u|+|p dot v|.

The replacement farthest corner has squared norm

    F' = max(X+1-h,1/2)^2 + max(Y+1-h,1/2)^2.

We prove F'<=F. Two basic bounds are

    L >= sqrt(X^2+Y^2),
    L >= (X+Y)/(2h) >= 2(1-h)(X+Y).

The first is the usual comparison of the one-norm and two-norm in an
orthonormal frame. For the second, writing p=(p dot u)u+(p dot v)v gives
X+Y <= (|c|+|s|)L=2hL. The final comparison follows from

    1-4h(1-h) = (2h-1)^2 >= 0.

There are three cases.

**Both coordinates large:** X,Y>=delta. Then

    F' = X^2+Y^2+2(1-h)(X+Y)+2(1-h)^2
       <= X^2+Y^2+L+1/2 = F,

because 0<1-h<=1/2.

**Both coordinates small:** X,Y<=delta. Then F'=1/2<=F.

**Exactly one coordinate large:** by symmetry take X>=delta and Y<=delta.
Then

    F' = (X+1-h)^2+1/4
       <= X^2+X+1/2
       <= X^2+Y^2+L+1/2 = F.

The first inequality uses 2(1-h)<=1 and (1-h)^2<=1/4; the second uses
L>=sqrt(X^2+Y^2)>=X. These cases also cover equality at either clamp
threshold. Hence original containment F<=R^2 implies replacement containment
F'<=R^2.

Applying this replacement independently to every square proves the theorem.

## Consequences for the n=11 roadmap

For any specified upper bound U, exclusion of **axis-aligned** eleven-square
packings with q<=U excludes the entire common-coordinate-separable class with
q<=U. Conversely an axis-aligned packing already belongs to that class.
Therefore the two classes have the same minimum enclosing radius, although
their equality families need not be identified by this reduction alone.

This theorem supplies no numeric lower bound. In particular an exact rational
axis-aligned construction has q<491/100<5, so q>=5 must not be asserted for the
whole class. The two-disjoint-four-chain theorem still excludes its stated
subclass below q=5. The current unrestricted upper bound U=49013/10000 is
smaller than that construction. The six-case interval certificate now excludes
the entire axis-aligned class at U, and therefore excludes the entire common-
coordinate class there by this reduction.

The reduction has been independently checked by the root researcher against
the displayed interval and corner inequalities. No Lean has been written.
