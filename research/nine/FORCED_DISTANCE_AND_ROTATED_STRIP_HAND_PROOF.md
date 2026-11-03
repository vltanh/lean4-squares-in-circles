# Exact rotated capacity and forced coordinate-gap rows

These implications concern the same physical original unit squares and
their already proved original-center/frame intervals. They add no case
split and retain physical contact. Rational axes are common rotations of
coordinates; each original square keeps its own physical orientation.

## 1. Owner-free radius

The separately included `OWNER_FREE_RELATIVE_SUPPORT_HAND_PROOF.md`
proves that any two originals i,j with disjoint interiors satisfy

    ||center_j-center_i|| >= (1+c+|s|)/2 >= 1,

where c and s are the cosine and sine of their actual relative frame.
Every physical separating-axis alternative has this same threshold.
Original slope intervals give a rational lower radius r>=1: use r=1
when they overlap; otherwise minimize cosine-plus-absolute-sine at the
two angular-difference endpoints, enclosing each positive square-root
denominator upward by exact integer-square-root arithmetic. No proposed
numerical placement or independent pairwise frame is used.

On proved Cartesian difference intervals d_k in [l_k,u_k], square
secants give the affine consequence

    -sum_k (l_k+u_k)d_k <= -r^2-sum_k l_k u_k.

## 2. Arbitrary rational orthonormal frames

Let e=(a,b) be a rational unit vector and f=(-b,a). Then e and f are
orthonormal. For any actual center difference d, write transverse
coordinate x=e.d and longitudinal coordinate z=f.d. The identity

    x^2+z^2=||d||^2

is exact. A proved Cartesian difference box gives a proved projection
interval by linear optimization over its four vertices. This remains
valid for negative components, degenerate intervals and reversed pairs.

The independent replayer reconstructs the 26 fixed rational unit
directions from the six Pythagorean triples (3,4,5), (5,12,13), (8,15,17),
(7,24,25), (20,21,29), (9,40,41), with coordinate interchange and signed
second coordinate, together with the two Cartesian axes.

## 3. The guarded strip row in a rotated frame

The included three-original capacity theorem is invariant under a common
rotation. Suppose the entire preceding state proves transverse spread
at most W<=7/10 and ordered longitudinal coordinates for originals
L,M,U. Let Delta=e.(center_U-center_L) in [l,u], and
V=f.(center_U-center_L). Then

    V+(5/14)Delta^2 >= min(2,208/75-(29/15)W)=:C.

The interval secant Delta^2<=(l+u)Delta-lu yields

    -(f+(5/14)(l+u)e).(center_U-center_L)
       <= -C-(5/14)lu.

Every guard is derived from the same old-state pair boxes. The middle
original remains a premise even though the affine row contains only
endpoint coordinates. Order ties and W=7/10 are included.

## 4. Elimination of an impossible sign without splitting

Suppose the whole preceding state proves |x|<=w<r, where the original
pair has ||d||>=r. Set q=r^2-w^2>0 and compute an exact rational lower
square root L>=0 with L^2<=q. Consequently |z|>=L, so

    z<=-L or z>=L.

If a proved longitudinal interval is [a,b], either of the following
whole-parent implications is valid:

    a>-L  implies z>=L;
    b< L  implies z<=-L.

The comparisons are strict. At a=-L or b=L, the corresponding contact
alternative is retained and no sign is selected from that comparison.
Both rows may be emitted if both strict comparisons hold: that only
means the already derived interval cannot contain a physical pair.
If the lower square root rounds to zero, any emitted row is a harmless
zero bound; no positive lower gap is asserted without proof.

For a chosen sign sigma in {+1,-1}, the row is

    -sigma f.(center_j-center_i) <= -L.

Thus coefficients +sigma f at original i and -sigma f at original j
have the required signs. The row preserves the exact original pair and
uses no selected separating-axis owner.

## 5. Finite whole-parent induction

Every application uses intervals established before its deduction round.
All weighted deductions in one round use that same old row list; only
after their exact sums and residual payments are checked are the new
bounds installed together. Original unit-frame identities then supply
new slope and physical scalar intervals. An empty intersection at this
stage is an exact terminal contradiction, not an optimizer decision.

The independent implementation uses `Fraction`, integer square root,
box-vertex projections and the displayed formulas. It imports no v4
discovery source or row generator. Its damaged controls test changed
rows/guards/bounds, and separate exact boundary controls retain the
possible longitudinal contacts z=+1 and z=-1.
