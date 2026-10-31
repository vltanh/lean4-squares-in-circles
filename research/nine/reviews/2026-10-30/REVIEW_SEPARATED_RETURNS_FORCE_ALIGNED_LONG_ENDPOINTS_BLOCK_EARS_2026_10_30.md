# Full independent review: separated return neighbors force aligned long endpoints

**Date:** October 30, 2026 UTC. **Reviewer:** block-ears agent.
**Result:** PASS for the full frozen source. No repair requested.

The source reviewed in full is
`SEPARATED_BOUNDARY_RETURN_NEIGHBORS_FORCE_ALIGNED_LONG_ENDPOINTS_2026_10_30.md`,
16,456 bytes, SHA256
`9c7f47ce87b5a7d548ec76c33f5912adae870211770ea578f15621a78104ca06`.

I independently reconstructed every geometric estimate, full-force and
moment elimination, interval maximum, rational comparison and literal
caller. I first read and fully reviewed the entire frozen input
`LONG_ENDPOINT_RETURN_CONTACT_LOCUS_FORCE_LINE_SIGN_AND_TILTED_VERTEX_REDUCTION_2026_10_30.md`
(SHA256 `cf942c1069e451ad043c80c8075fd67c85d2b71faa05c29b9baa3dae32f66fe3`)
in the separately saved
`REVIEW_LONG_ENDPOINT_RETURN_LOCUS_AND_TILTED_VERTEX_REDUCTION_BLOCK_EARS_2026_10_30.md`.
I also previously independently reviewed the expanded endpoint cover and
the complete return-side localization. I authored the contact-lens input;
this provenance does not replace the new coupling proof reviewed here.

## 1. Complete local hypothesis join

The local theorem retains a genuine common-normal long channel with two
unloaded bodies of true full positive degree two, and keeps their actual
angular equations. Both endpoints A,B themselves have true positive
degree two. Their other positive neighbors D,C are actual boundary units
wholly above the long-normal x-axis, with actual set distance at least one.
The full degrees of C,D are arbitrary. Every physical square and every
original mean, normal, circle atom and force is retained.

The frozen input supplies the actual long means `(s-1,t),(s,t),(s+1,t)`,
`|s|<1/60`, `|t|<=9/16` and the coupled endpoint height bound. In any
branch with at least one tilted endpoint it supplies `t<-1/2`, negative
center heights at both ends, and upper-inner vertex means with the
complete strict inward/upward own-normal cones. The possibly aligned
other endpoint is covered by the input's separate aligned-axis exclusion.
Thus the assembly does not assume a two-edge equation at a larger-degree
endpoint or replace an original common normal by a convenient separator.

## 2. Tilted normal slope with every circle mask retained

For the right tilted endpoint, the full equations are

    2m-mu*e_x+nu*n=0,
    mu*t+nu*(p_B cross n)=0.

The return normal has positive global y-component. Its line meets y=t
at `(x0,t)`. Substituting
`p_B cross n=n_y*x0-t*n_x` and then the complete force equations gives
`m_x*t-m_y*x0=0`, exactly the asserted formula
`x0=t*m_x/m_y`.

The total circle vector has positive x and negative y. Each physical
circle corner has positive x; hence the resultant slope is a convex
combination of the actual corner slopes with weights `lambda*z_x`.
The upper possible corner has strictly larger slope than the lower
one: its cross-multiplied slope difference has numerator
`a*x+1-b*t>0`. Therefore the lower-corner slope is a valid lower bound
for every original two-corner weight split, including zero individual
weights. Dividing by the negative slope and using t<0 gives the stated
lower bound on x0 with the correct inequality direction.

The resulting slope estimate is

    -n_x/n_y >= [tau*(a-b)-b*(x+b)]/[a*(tau+b)].

Its numerator is strictly positive on the displayed full parameter box.
Replacing a by one in the denominator is therefore legitimate. The
resulting quotient is increasing in tau, with derivative
`b*(a+x)/(tau+b)^2>0`. The bounds
`a-b>37/40`, `b<17/240`, `a>199/200`, and `x<61/60` yield
`H>7401/10960>2/3`. The first squared comparison has reserve
`19/2880`, and the final slope reserve is `283/32880`.

Normalizing the original vector gives
`alpha>2/sqrt(13)>11/20`, with the latter squared reserve `27/5200`.
Thus its global inward x-component is proved, not inferred from an
own-frame sign. Reflection supplies the exact left-endpoint statement.

## 3. Whole-interval maximum on the two facing normal arcs

For fixed A>0 and B<=0, differentiation of
`(A-cos(theta))^2+(B+sin(theta))^2` gives
`2(A sin(theta)+B cos(theta))`. On the interval in the source, cos is
positive, and the sign is that of the increasing function
`A tan(theta)+B`. An interior critical point is a minimum. Therefore
the maximum is at an endpoint, including B=0.

Applying this independently in each angular variable proves that the
two-normal squared distance attains its maximum at a corner of the
closed product interval. Its mixed-corner value is
`1+k^2-(11/10)k`, with `k=L-1`. Its differences from the two equal-angle
corner values are exactly
`2(1-c0)(L-1)` and `2(1-c0)(1+2c0-L)`, respectively. Both are positive
on `2<=L<21/10`. No angular sample, actual-pose optimizer or unproved
convexity assertion is needed.

## 4. Doubly tilted branch

The actual endpoint center separation is `2+h_A+h_B`. The center bound
therefore gives
`(a_A+b_A)+(a_B+b_B)<31/15`. With both a-values greater than `199/200`,
this yields `b_A+b_B<23/300`, `L<623/300` and
`|a_B-a_A|<1/200`. This is a coupled endpoint estimate; the two tilts
have not been set equal.

Ignoring only the displayed vertical offset for the intermediate
estimate, the normal-arc maximum is at most `87739/90000`. Its distance
is strictly less than `199/200`, since the exact squared reserve is
`5453/360000`. Restoring the actual height difference by the triangle
inequality adds strictly less than `1/200`, leaving a distance strictly
below one.

Both compared points are actual occupied points: `p_A+n_A` belongs to
D and `p_B+n_B` belongs to C by the full supporting-face unit chord.
Their distance below one contradicts `dist(C,D)>=1`. The support means
are unchanged, both endpoint circle masks remain, and independent
internal center heights are immaterial.

## 5. Exact correlation at the aligned endpoint of a mixed branch

After a single reflection take A aligned and B tilted. The original
long mean lies on A's inward side. With `tau=-t>1/2` and `Y=-y_A`, this
gives `Y>0` and the complete constraints
`e=Y+1/2-tau in [0,1/8)`, `H=1-e`, and `tau+e<=5/8`.
The actual upper-inner return mean is `(-x,t+H)`.
Because Y is strictly positive, the lower outer corner is genuinely
the unique physical circle corner; this is derived from the pose rather
than assumed as a load mask.

I independently eliminated the two contact magnitudes from the full
aligned endpoint equations. They give exactly

    alpha_A/beta_A=(tau-x*e)/[(tau+e)(1-e)].

The ratio is nondecreasing in tau and nonincreasing in x. After setting
tau to `1/2`, its e-derivative has the negative numerator displayed in
the source. The enlarged closed parameter box therefore gives
`h_A>=358/525>2/3`. At e=0 the tau/x monotonicities are non-strict,
which is harmless for this lower-bound use.

Rewriting the same exact quotient and using `x+1>119/60` and
`tau+e<=5/8` proves `h_A<=1-2e`. The final comparison reduces to
`(13/75)e+2e^2>=0`, so the allowed endpoint e=0 is included. This
yields the lower bound on beta correlated with e. The product
`(2/3+e)^2*(2-4e+4e^2)` has derivative

    (4/3)*(2/3+e)*(1-5e+12e^2)>0

on the full closed interval, and its upper endpoint value is
`9025/9216<1`. Positive squaring gives `beta_A>2/3+e`, hence
`H+beta_A>5/3`. The accompanying bound
`alpha_A>11/20`, `beta_A<sqrt(279)/20<21/25` also follows.
This correlation is essential; the proof retains it through the final
mixed comparison instead of taking incompatible independent extrema.

## 6. Both mixed-case extrema are strictly below one

The actual squared distance of the two normal-chord points has the form

    (L-alpha_A-cos(theta))^2
      +(a-H-beta_A+sin(theta))^2.

The first base coordinate is positive and the second is strictly
negative because `H+beta_A>5/3>=a+2/3`. Thus the same endpoint-maximum
lemma applies on the whole enlarged normal interval.

At theta=0 the positive horizontal difference is below `25/48`.
The negative vertical difference has magnitude below `169/200`.
Their squared sum is `1418821/1440000`, below one by
`21179/1440000`.

At theta=Theta the positive horizontal difference is below `233/240`.
The vertical difference lies strictly between `-9/200` and `13/75`,
so its magnitude is below `13/75`. The resulting squared bound is
`1400489/1440000`, below one by `39511/1440000`.

These checks include both signs of the second vertical difference.
They bound the actual normal by an enlarged interval; they do not
assert that either endpoint direction itself is an admissible packing.
Every original normal therefore gives occupied points at distance below
one, contradicting the same true set gap. This excludes the entire mixed
branch and completes the local theorem.

## 7. Full seven-cycle caller and exact residual

In the displayed opposite long/short C7, the return-side theorem applies
in the stated compatible embedding with physical boundary marks and
places whole C,D above the axis after one common reflection. The actual
one-internal run C--W--D has a common signed normal by W's genuine full
two-force equation and hence actual endpoint set gap at least one.
The original A/B full degree-two equations and both U/V full equations
supply every remaining premise of the local theorem. Extra contacts at
C,D do not enter a shortened equation and are permitted.

The full tilted-long-endpoint branch is therefore excluded uniformly.
Both long endpoints must align with the long normal. The proof does
not align the return squares or W, force vertical joins, identify the
internal centers with their means, or create a solid row. All physical
units outside the displayed seven bodies remain. The aligned sharp
remainder and the original target lower bound are not claimed closed.

The entire frozen source passes at these exact scopes. No repair,
source mutation, new ledger credit or automated formal-proof claim is
part of this review.

