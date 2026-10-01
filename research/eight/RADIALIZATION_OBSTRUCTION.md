# Negative result: independent outward radialization is not safe

A tempting way to reduce the global problem is to increase each exterior square's primary local coordinate until a far corner reaches the circle, holding its orientation and transverse coordinate fixed. The following exact pair shows that this operation need not preserve disjointness, even after the radius-1/12 central-core and near-heptagonal pair restrictions.

This is a two-square obstruction, NOT an eight-square counterexample. It does not exclude a more elaborate simultaneous deformation with a separate proof.

## Exact data

Let the circle be centered at zero. The first square S has center (99/100,4/5), with horizontal/vertical sides. The second square T has local center (a,9/16) and orthonormal frame

    e=(33/65,56/65),  f=(-56/65,33/65).

Initially a=9/16. Its world center is (-207/1040,801/1040). The common separating-axis threshold for these two orientations is

    W=(1+33/65+56/65)/2=77/65.

The horizontal center separation minus W is exactly

    23/5200 > 0.

Thus the original pair has disjoint interiors with a strict separator.

Their farthest-corner squared distances are

    S: 39101/10000,
    T: 289/128.

Both are strictly below q*=3.9155341375... (the first is 3.9101). Both closed squares avoid the closed disk of radius 1/12: for T the nearest squared distance is 2*(1/16)^2=1/128>1/144; S is much farther away.

## An outward translation creates overlap

Increase only T's primary local coordinate from 9/16 to 1. Its new world center is (3/130,1193/1040). It is still inside the same disk: its farthest-corner squared distance is 865/256, and it still avoids the central core.

For the four axes of the two frames, the absolute projected center differences minus W are respectively

    -283/1300,  -67/80,  -6453/6500,  -4559/26000.

All four are strictly negative. The separating-axis criterion therefore proves that the two open squares overlap. This is an exact rational calculation, not failure of a numerical optimizer.

## The initial pair also has the current ring gap

For the label ell=min(11u/10,5/9+3u/5-17a/50,157/200), both transverse signs are positive and

    ell_S=31453/45000,    ell_T=99/160.

The relative frame angle is d=2 arctan(4/7). The marker gap is d+ell_T-ell_S. The alternating arctangent bounds through degrees seven and nine give

    7/8 < d+ell_T-ell_S < 29/28.

For orientation only, the resulting rational enclosure is approximately (0.95694,0.95839). Its exact inequalities follow by substituting 4/7 in

    2(x-x^3/3+x^5/5-x^7/7)
      < 2 arctan(x)
      < 2(x-x^3/3+x^5/5-x^7/7+x^9/9).

Thus the current pair gap and central-core necessary conditions do not license this radialization step.

## Consequence for the research strategy

Circle contact of every orbital square cannot be assumed by independently moving each square along its primary frame direction. A valid reduction must retain interior states, or prove a coupled deformation that accounts for changing separators. The five-corner construction theorem does not supply such a deformation.

All projected margins, containment values, core margins, and rational arctangent comparisons above were evaluated exactly with fractions.Fraction. No Lean formalization is involved.
