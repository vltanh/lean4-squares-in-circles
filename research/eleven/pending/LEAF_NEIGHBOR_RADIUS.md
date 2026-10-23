# Leaf neighbors lie in the radius-6/5 center disk

Use the hypotheses and owner cases of `LEAF_NEIGHBOR_UNLOADED.md`, with
`9/2<q<=U=49013/10000`. Every neighbor of a positive stress-graph leaf has
center norm strictly less than `6/5`. Two of the owner cases have stronger
localization bounds. These are bounds on leaf neighbors, not on all
circle-unloaded squares.

Write `C=sqrt(q-1/4)-1/2`. Direct squaring gives

    C < 83/50,

because `U-1/4< (54/25)^2`.

If the leaf is parallel and the neighbor owns the axis, the centers are
`p_N=(1-C)n+t Jn` with `|t|<=1`. Since C>1,

    ||p_N||^2 <= (C-1)^2+1
               < (33/50)^2+1 = 3589/2500
               < 36/25.

If the parallel leaf owns the axis, the preceding lemma supplies the actual
radial shared point `P=-r n`, where `r=C-1/2`. The neighbor center has the
form `p_N=P+w_bar`, with w_bar a convex combination of its centered support
corners in direction n. Every such point satisfies
`||w_bar||^2<=1/2` and `n dot w_bar>=1/2`. Hence

    ||p_N||^2 <= r^2-r+1/2.

Here `1<r<29/25`, and this quadratic is increasing. Thus

    ||p_N||^2 < 857/1250 < 25/36,

so in this owner case the center norm is strictly less than `5/6`.

Finally, for a diagonal leaf, its neighbor owns the normal and is parallel.
The unique shared point is `P=-r n`, with `r=sqrt(q)-sqrt(2)`. Its membership
in the neighbor's near face gives

    p_N=(1/2-r)n+t Jn,       |t|<=1/2.

Since `sqrt(q)<111/50` and `sqrt(2)>7/5`, we have `1/2<r<41/50`.
Consequently

    ||p_N||^2 <= (r-1/2)^2+1/4
               < (8/25)^2+1/4 = 881/2500 < 9/25.

The center norm in this case is strictly less than `3/5`.

Any independently established cap on the number of packing centers in the
radius-6/5 disk now caps the number of **distinct** neighbors of stress
leaves. Several leaves can share one neighbor, so this does not by itself
give the same cap on the number of leaves.
