# Independent review: every diagonal channel has an empty exterior pocket

Date: October 26, 2026.

Reviewer: global_closure, independent of the source author and root reviewer.

**Verdict: ACCEPT the complete whole-channel theorem and its stated original
four-load C6 consequences. No mathematical correction is required.**

## 1. Exact reviewed sources and scope

The principal source is
`FOUR_C6_DIAGONAL_CHANNEL_CAP_EMPTY.md`, SHA-256
`dba7941f48fb1693518603e96751b78e1e2c3feb9c7d6135d1cdc4d1422efc4c`.
I read its entire proof, including all closed orientation endpoints and
its final application to both original four-load C6 orbits.

I separately read all Sections 1--7 of the imported balanced-family proof
`SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md`, SHA-256
`c5dec5c8cb78f83715624b59a1401748f07616acf44f9c567ab88da778c3ebbe`,
and the original-domain and height derivations in Sections 1--2 of
`DIAGONAL_CHANNEL_EXTERIOR_CAPACITY_ONE.md`, SHA-256
`46f8be67b5c447a78f12cefb3f96474973ead5d48d4e65b346a1c77bdd8fee02`.

The theorem concerns an original simple positive cycle with at least
three loaded bodies and one genuine unloaded degree-two diagonal
transmitter. All original endpoint loads, physical circle masks,
side-interior means, and other channels are retained. It applies on the
whole radius interval 2 <= R <= sqrt(1105/256). The proof's SAT axes are
geometric separators for a putative extra; they are never substituted
for selected certificate normals.

The original channel-cap theorem supplies whole-square pocket inclusion,
not only a restriction on the extra's center. The horizontal slab follows
from the actual crosscut and positive-height upper circle arc. This is
the same original pocket used in the accepted capacity theorem.

## 2. The balanced proof extends directly to radial physical endpoints

The imported geometric proof uses a>b and c>d, the two strict side-mean
intervals, the two proper-concurrence height inequalities, the actual
pocket inclusions, and circle containment. It does not use a third load,
an alternating-cycle turn, or an additional force equation after those
conditions have been obtained.

For a physical radial endpoint, the vertical height is 1/2. Its claimed
height inequality follows from h>43/100 and the elementary upper bound
41/162 on the corresponding right-hand side. This argument does not put
a radial concurrence inside its body. Unique endpoints use their actual
proper concurrence, as before.

I checked every subsequent place in the imported proof where strict
height above 1/2 could matter:

- Its bounds 10/7<a,c<2 and h>2/5 still hold. The possible equality in
  the lower radius comparison when a height is 1/2 does not affect the
  contradiction proving a,c<2.
- The owner comparisons and positive closest-point coefficients require
  only the resulting horizontal bounds and weak b>=1/2. The angular
  inequalities remain strict where the proof needs them.
- All four exact polynomial identities are stated on complete closed
  height rectangles whose lower endpoint is 1/2. Their positive tables
  therefore already include the radial endpoint.
- The identity T-a=(b^2-1/4)/(T+a) explicitly allows T-a=0. No division
  by b^2-1/4 occurs.
- The actual cap proof still has h<b strictly, even for b=1/2.
- In the auxiliary pi/4 construction, R>=2 gives
  M/sqrt(2)-1/2>1/2. The comparison tuple retains a'>b', c'>d', and all
  hypotheses of the scalar inequality. That scalar lemma does not
  require the auxiliary height to satisfy an actual mean interval.

This is a direct extension of inequalities on the unchanged physical
domain. No motion, artificial unique mask, or limit of modified stresses
is needed. The complementary tall-endpoint family includes equality
a=b or c=d, so the two main families exhaust every endpoint configuration.

## 3. Complete separating-axis cover and asymmetric northeast cases

The original slab and y>=h inclusions exclude every W-to-E separator
with nonpositive vertical component: a sloping such separator would
force an axis-aligned unit into the width-one endpoint slab and then
outside the disk. A purely upward separator violates the universal
center bound. Reflection leaves a strictly northwest separator, owned
either by W or by E.

For X/E separation, the northwest alternative implies the vertical
row, the southeast alternative implies the horizontal row, and the
southwest alternative is impossible. This leaves precisely the three
listed nonexclusive rows. All side-axis endpoints are included.

The horizontal row is excluded for both W and E owners by the actual
top vertex. I independently derived the expression
h+v+[1+s(mu-v)]/u in the E-owned case. Its lower bound h+s+1 holds on
both angular sectors, with no missing division at an allowed endpoint:
the E-owned northwest case has u,v>0, while the W-owned case includes
the closed endpoints separately.

For the tall northeast row, both own-coordinate lower bounds are
positive. Expanding their squared sum yields the stated constant and
linear coefficient, and the rounded quadratic coefficient is in the
correct direction. The other angular sector has the claimed uniform
norm reserve. The W-to-E owner comparison is exact, including u=v and
the side joins. In its remaining sector, the positive combination of
the two top-vertex inequalities gives (15) directly; the two bounds on
w and t then exhaust the whole interval.

For the short northeast row, the B-only case is disposed of before a
possibly negative A lower bound is squared. On the remaining physical
domain the A lower bound is positive. The auxiliary squared-sum
polynomial may safely be analyzed on the larger full angular interval:
its use as a geometric lower bound is restricted to the valid part.

I recomputed the concavity coefficients. The negative u-linear second
derivative, the quadratic term, and the bounded positive contribution
from the negative uv coefficient give a second derivative strictly less
than -2. In the opposite sector the positive v-linear term contributes
a nonpositive derivative; together with the stated u-linear and uv
signs this makes the derivative strictly negative. Both sectors join at
the same diagonal endpoint and retain the two radius ranges.

For the W-owned remaining sector, both closest-point coefficients are
strictly positive. I checked their signs from the original a,b,h bounds,
including the possibility that one lower projection already exceeds R.
The displayed intersection has negative x and positive y throughout
the comparison domain, so lowering a and h lowers its norm. After the
small-t projection exclusion, its coordinate sum is positive, making
the subsequent lowering of b valid. The final derivative is strictly
negative on the whole closed interval [1/4,1], and its endpoint norm is
strictly above Q.

## 4. Asymmetric vertical row: full continuous scalar inequality

The radical X0 is real throughout the entire asymmetric domain and
obeys X0>7/8. In the fixed-R comparison, increasing a from the symmetric
tall endpoint to its actual value decreases b. Thus the whole comparison
interval retains b>=1/2, not just the actual endpoint; its lower a bound
also retains b<3/4. The c and d bounds used in differentiating G hold
throughout that interval. I independently derived

    G_a = 1+c/d+(a/b)(1-Y/X0)

and its strict positive reserve 277/2240. The adverse comparison is
therefore the stated c=d endpoint.

At that endpoint, squaring X0<3s-Y is legitimate because both sides
are positive. Expanding gives exactly F(t)>0. Differentiating its two
radicals gives exactly the stated F''; the elementary lower bound is
strictly above 100. The interval between any actual t and t0=47/32
retains the needed T and b0 bounds. In particular, the actual fixed-R
comparison has already established b0>=1/2, and the explicit enclosure
at t0 places it in the same domain.

The rational enclosures at t0 are valid by squaring positive quantities.
Their lower and upper derivative substitutions have the correct signs.
The strong-convexity estimate and completion of the square therefore
prove a uniform positive margin for every actual radius; this is not
a numerical check at the comparison point alone.

## 5. Whole center-cap support and final completion join

The inequalities for u0,v0 put the left center-cap endpoint either inside
W or at distance strictly less than 1/2 from W's upper vertex or its
upper-left edge. The support conclusion also holds when v0<0. The
nearest-edge cases retain both projection endpoints through the two
strict difference inequalities. Thus every northwest support test at
that cap endpoint has strict excess below 1/2.

I checked the extension to the entire center cap. For theta>=theta0 its
support is attained at the already treated endpoint. For theta<=theta0
it equals M; the support difference is concave on both sides of pi/4
because the sine and cosine coefficients are positive. The possible
pi/4 endpoint is handled in both radius ranges. In the upper range the
condition Y<=M/sqrt(2) gives the stated small b bound, then d-c>1/40;
the strict radius margin is sufficient. This proves the claimed strict
support inequality for every northwest unit normal, which is
incompatible with any separating axis of a unit extra whose halfwidth
is at least 1/2.

Consequently the entire original diagonal pocket is empty. The original
four-load joins then use central capacity one, side-pocket capacity one,
and this diagonal-pocket capacity zero. Three actual extras cannot fit
when either transmitter is diagonal. Both cyclic orders in the source
are included, with all side/diagonal, diagonal/side, and
diagonal/diagonal patterns. The original both-side allocation (1,1,1)
remains open; no whole four-load parent or coarse C6 cell is closed by
this source alone.

## 6. Independent exact arithmetic record

I independently reconstructed 51 exact rational equalities and strict
reserve checks with Python integer fractions. All passed. They include:
the short horizontal radical margin; both delta bounds; all northeast
norm margins and concavity coefficients; both diagonal endpoint
reserves; the closest-point endpoint reserve; the X0 and G_a reserves;
the strong-convexity lower bound; all six fine radical enclosure sides;
the exact F(t0) and F'(t0) rational bounds; the completed-square margin;
and both final pi/4 center-cap reserves.

These computations checked explicit fixed arithmetic already present
in the hand proof. No parameter sample, finite pose search, Lean
compilation, CI, remote write, or shared ledger change is part of this
review.
