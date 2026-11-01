# One exceptional pair: a physical span lemma and a sharp terminal

November 1, 2026. Complete hand lemmas and conditional callers. No scripts,
Lean, or CI. The full one-exception nine-square class remains unproved.

## 1. A universal physical pair-span inequality

Fix an **orthonormal** coordinate frame. Let two unit squares have disjoint
open interiors, centers `(x_1,y_1),(x_2,y_2)`, and equal x/y projection
halfwidths `h_1,h_2`. Each `h_i` belongs to `[1/2,1/sqrt(2)]`.

**Lemma.** Every such physical pair satisfies the stronger exact inequality

    max(|x_2-x_1|,|y_2-y_1|)+h_1+h_2
       >= 2 + (2h_1-1)^2/(4h_1) + (2h_2-1)^2/(4h_2)
       >= 2.

Equality in the final bound `D+h_1+h_2=2`, where `D` is the maximum
coordinate center gap, requires both squares to be aligned and `D=1`.
This holds regardless of
disk containment and does not assume coordinate projection separation.

*Proof.* A physical square of coordinate halfwidth `h` contains the
axis-aligned square with the same center and halfwidth

    g=1/(4h).

Indeed, if the physical side-axis absolute coordinates are `a,b`, then
`a+b=2h`. Any point of the aligned square has absolute coordinate at
most `g` on each common axis, so its absolute coordinate along either
physical side-axis is at most `(a+b)g=1/2`. Points in the aligned
square's open interior have both physical coordinates strictly less
than `1/2`, so its open interior lies in the physical square's open
interior.

The two inscribed aligned squares therefore have disjoint open interiors.
They must be separated horizontally or vertically, giving

    D=max(|x_2-x_1|,|y_2-y_1|) >= g_1+g_2.

Now use the exact identity

    h+1/(4h) = 1+(2h-1)^2/(4h).

Adding these two identities proves the quantitative inequality. Equality
in the final bound `D+h_1+h_2=2` forces `h_1=h_2=1/2`, hence alignment
of both physical squares, and then `D=1`. QED.

**Nearby-height corollary.** If `|y_2-y_1|<=1/2`, then

    |x_2-x_1|+h_1+h_2 >= 2,

with equality only for aligned squares and `|x_2-x_1|=1`. Indeed
`2-h_1-h_2>=2-sqrt(2)>1/2`, so the maximum gap in the lemma must be
the horizontal gap.

In this corollary the left side is the span between the leftmost point of the left-center
square and the rightmost point of the right-center square. It is a lower
bound for the full union's projection width even if one projected interval
contains the other; the proof does not assume an endpoint ordering.

## 2. Replacing an internal projection separation by this physical pair

Suppose four actual units have centers ordered in x as `L,A,B,R`, with
the two outside comparisons

    x_A-x_L >= h_A+h_L,
    x_R-x_B >= h_R+h_B.

The middle pair `A,B` may require an oblique separating axis. Assume only
`|y_B-y_A|<=1/2`. Section 1 gives

    x_B-x_A+h_A+h_B >= 2.

Adding the three inequalities yields the exact long-anchor span

    x_R-x_L >= 2+h_L+h_R.

Suppose two other actual endpoint squares `C,D` satisfy the short span

    x_D-x_C >= 1+h_C+h_D.

For example, this is supplied by a disjoint three-square projection chain.
Assume the four endpoints `L,R,C,D` are distinct physical squares and all
relevant units fit a disk of squared radius `q`.

**Sharp terminal.** These hypotheses imply `q>=Q=1105/256`.

This follows directly from the physical two-square cap theorem in
`PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`.
For clarity, its actual input is not a chain: for any physical pair `M,B`
in the disk at `q<=Q`, it bounds

    46[-x_M-h_M]+(27/2)[-x_B-h_B] <= 211/4,

strictly if `q<Q`. Apply it to `(L,C)` in the positive x direction and
to `(R,D)` in the negative x direction. Their sum is at least

    46*2+(27/2)*1 = 211/2,

by the two anchor spans, and at most `211/2` by the two cap inequalities.
Strict `q<Q` is therefore impossible.

At `q=Q`, both spans are sharp, so the Section 1 pair inequality and
the two exterior projection gaps are also sharp. Thus `A,B` are aligned,
their horizontal center gap is one, and they **are** separated by their
horizontal projections. Therefore if `A,B` are a genuine exceptional pair
with overlapping projections on both coordinate axes, this terminal
actually excludes the whole `q<=Q` domain, including equality.

## 3. Five-square antichains with one genuine exceptional pair

Suppose nine physical squares in `q<=Q` have a fixed orthonormal frame
which separates every pair except possibly one pair `A,B`. Suppose a
five-square subfamily has pairwise overlapping open x-projections.
It must contain `A,B`, since otherwise it would give a forbidden
five-square y-chain. If `A,B` were y-separated too, the same contradiction
would follow, so their y-projections overlap in their interiors.

The other three members have y-projections disjoint from one another
and from each of `A,B`. Since the two exceptional y-intervals overlap,
their union is an interval, and each of the other three intervals lies
wholly before or wholly after this union. Thus there are exactly four
ordered projection blocks: three single-square blocks and the exceptional
pair block.

The exceptional block cannot be at either end. For example, if it is
above three singles, each of the two exceptional centers lies at least
three units in y above the first single center, hence has `y>3-rho=59/40`,
where `rho=61/40` is the universal center-radius bound. Both exceptional
centers then lie in

    (-2/5,2/5) x (59/40,61/40).

The x bound follows from `(59/40)^2+(2/5)^2>rho^2`. This rectangle has
squared diameter `257/400<1`, contradicting the separation of their
inscribed open half-unit disks. Reflection handles the bottom end.

Moreover the total y-width of all four blocks is at least

    3+h_A+h_B+|y_A-y_B| >= 4+|y_A-y_B|.

Since all blocks lie in `[-R,R]`,

    |y_A-y_B| <= 2R-4 < 1/2.

The last strict bound follows from `R<=sqrt(1105)/16<9/4`. In fact the
orientation excesses are retained in the stronger inequality

    |y_A-y_B|+(h_A+h_B-1)
       + sum_(three singles)(2h_S-1) <= 2R-4.

Therefore the physical pair-span lemma always applies to the exceptional
pair in this five-antichain situation. The pair lies in one of the two
internal blocks and has horizontal span reserve at least two, strictly
greater than two for a genuine coordinate-exceptional pair.

## 4. Routing the four squares outside a five-antichain

Reflect the y coordinate if necessary so the four ordered y-blocks of
Section 3 are `D,C,{A,B},U`. Both `D,C,A,U` and `D,C,B,U` are genuine
four-square y-projection chains. The unit-width lower bound and center
radius `rho=61/40` force

    -61/40<y_D<-59/40,
    -21/40<y_C<-19/40,
     19/40<y_A,y_B<21/40,
     59/40<y_U<61/40.

For example, `y_U-y_D>=3`, and each consecutive center gap is at least
one; each displayed interval follows by propagating these inequalities
from `-rho<y_D` and `y_U<rho`.

Every other physical square F has `|y_F|<59/40`. A center with
`y_F>=59/40` would lie in the same small cap rectangle as U, giving
center distance squared less than `257/400<1`; the negative cap and D
are identical by reflection.

Since the only exceptional pair is A/B, any horizontal projection
overlap between F and a main square forces their vertical projection
separation. In particular:

- If F overlaps C horizontally, the order below C would require
  `y_F<=y_C-h_C-h_F<-59/40`, impossible. Thus

      y_F>=y_C+h_C+h_F>19/40.

- If F overlaps A or B horizontally, the order above that square would
  require `y_F>59/40`, impossible. Thus

      y_F< -19/40.

Consequently F cannot horizontally overlap C and either A or B.

The five pairwise-overlapping open horizontal intervals have a nonempty
common open intersection I: their maximum left endpoint is strictly
less than their minimum right endpoint, by pairwise overlap. If F's
horizontal interval intersected I in its interior, it would overlap C
and both A,B, a contradiction. Hence the horizontal interval of every
one of the four remaining squares lies wholly to the left or wholly
to the right of I, with contact at an endpoint allowed.

This derives a two-side routing of the four remaining squares. It does
not yet force two squares on each side, or prove the projection spans
needed by Section 2.

## 5. Remaining caller

These results do not prove that every nine-square one-exception packing
contains the outside L/R projections and the disjoint short span needed
in Section 2. They provide that terminal with exact, hand-checkable
hypotheses and reduce the five-antichain branch to two internal block
positions. The arrangement of the four squares outside the antichain
must still be used to obtain a complete contradiction or a valid terminal.
No canonical positional-root exclusion or global A.2 closure is claimed.
