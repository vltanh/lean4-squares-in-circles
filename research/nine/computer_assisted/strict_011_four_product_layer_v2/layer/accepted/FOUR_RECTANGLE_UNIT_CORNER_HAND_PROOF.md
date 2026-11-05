# Four independent rectangle planes for the same original unit-frame corner

Fix one of the unchanged original squares, with center (x,y), physical unit
side (alpha,beta), and quarter-turn side (-beta,alpha). For epsilon,tau in
{-1,1}, its original corner has squared norm

    x²+y²+1/2+epsilon alpha x+tau alpha y
                      +epsilon beta y−tau beta x.

The identity uses alpha²+beta²=1 before any relaxation. Containment of this
same corner in the closed disk therefore gives

    x²+y² + f_0 g_0 + f_1 g_1 + f_2 g_2 + f_3 g_3 <= 977/256,

where the four products are

    (alpha,epsilon x), (alpha,tau y),
    (beta,epsilon y),  (beta,−tau x).

For each product f_j g_j independently, choose either both lower interval
endpoints (a_j,b_j) or both upper interval endpoints. The intervals must
be proved for the current unchanged original caller. Then

    f_j g_j >= a_j g_j+b_j f_j−a_j b_j

because (f_j−a_j)(g_j−b_j)>=0. Repeated appearances of alpha, beta, x or y
do not require choosing the same endpoint: each of these four inequalities
holds for the same actual value, and their sum is valid. Negative signed
coordinates and negative beta are included by taking the extrema of the
corresponding signed interval.

For any rational p_x,p_y, also use

    x²+y² >= 2p_x x+2p_y y−p_x²−p_y².

Thus the new affine left side is

    L=2p_x x+2p_y y+sum_j (a_j g_j+b_j f_j),

and the necessary row is

    L <= 977/256+p_x²+p_y²+sum_j a_j b_j.

The complete exact residual identity is

    x²+y²+sum_j f_j g_j − (L−p_x²−p_y²−sum_j a_j b_j)
      = (x−p_x)²+(y−p_y)²+sum_j (f_j−a_j)(g_j−b_j) >= 0.

This proves the continuous implication for every one of the 16 endpoint
choice patterns. They are alternative valid inequalities, not branches
that require a domain cover. All four signed corners of all nine originals
are eligible. The row uses four of the existing 54 original variables and
introduces no auxiliary or selected physical separator.

## Relation to the accepted two-rectangle corner family

When the two alpha products choose the same side, the sum of their signed
coordinate endpoints is the corresponding Cartesian endpoint of
epsilon x+tau y. When the two beta products choose the same side, the same
statement holds for epsilon y−tau x. Therefore choices (a,a,b,b) reproduce
the accepted two-rectangle row exactly, with the same center tangent.
The present family contains all four accepted planes and permits the
additional independent choices. Its optimal affine envelope can only be
stronger for fixed original intervals and a fixed tangent.

The independent checker does not import the producer. It separately
enumerates the four signed coordinate intervals, expands each product
plane and the two center terms, and checks the exact constant 977/256.
Numeric points only select rational tangents and endpoint choices; every
literal used by a certificate is rebuilt on independently propagated
current caller intervals. Reusing a saved parameter tuple on another
caller requires rebuilding the row there. No original cell or mask is
excluded without its surrounding complete exact proof.
