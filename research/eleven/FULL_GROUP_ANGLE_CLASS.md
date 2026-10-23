# Closing both angle orders in the fourteen-separator class

Status: both complete finite covers passed direct exact replay. The ordered
branch has 242 closed rectangles and the reverse branch has 265.

Keep exactly the physical labels, three orientation groups and fourteen
signed owner halfspaces stated in `ORDERED_GROUP_ANGLE_CLASS.md`. The two
group angles are now allowed to vary independently throughout the full closed
square

```
0 <= alpha <= pi/2,  0 <= beta <= pi/2.
```

**Theorem.** The centers remain arbitrary and `q>=qc`, with equality
among actual packings exactly the established slider family. This removes
the angle-order hypothesis of the previous contact-class terminal. It still
does not capture arbitrary independently rotated packings into the class.

Split the closed angle square into the two closed triangles `ta<=tb` and
`ta>=tb`. Their common equal-angle edge belongs to both; there is no tie
removal. The first triangle is handled by the existing ordered-angle theorem.
For the second, use the identical nonsingular nonnegative dual profiles from
`angle_tile_dual.py`, changing only the signed mixed support to

```
kd_reverse = (1 + cos(beta-alpha) - sin(beta-alpha))/2.
```

For `beta<=alpha`, this equals the physical support
`(1+cos(beta-alpha)+|sin(beta-alpha)|)/2`. For any rectangle straddling the
diagonal, it is still a lower bound for physical support, so nonnegative
weights preserve the weak-dual inequality. All other widths, force formulas,
zero-total-weight conditions, and rational Taylor bounds remain identical.
In particular endpoint orientations and the singular-looking `cos(delta)=0`
case remain covered without division by a trigonometric quantity.

`REVERSE_ANGLE_TILES.json` contains a closed rational rectangle cover of the
unit square. Each rectangle either lies strictly outside the reverse triangle
(`tb_lower>ta_upper`) or has a rational dual lower bound strictly above
`Q=4.901206414>qc`. The same exact sweep-line checker verifies a gapless cover
including every rectangle edge and vertex. There is no retained candidate
box in this branch because the candidate has strict angle order `ta*<tb*`.

Exact replay gives the strictly stronger bound
`q>Q` throughout `0<=tb<=ta<=1`. Consequently equality in the full angle square
can occur only in the previously solved ordered branch, and its equality
classification gives the exact candidate slider family.

The reverse certificate has 141 dual rectangles and 124 rectangles strictly
outside its triangle. Its least checked dual margin above Q is greater than
`37288361/10^12`. The two certificates together use 507 closed rectangles,
including 355 dual rectangles, 151 discarded unordered rectangles, and the
one quantitatively solved candidate rectangle. Every angle point belongs to
a solved branch; no small-angle, generic-position or positive-cosine exception
remains.

Reproduction:

```
python research/eleven/check_angle_tiles.py
python research/eleven/check_reverse_angle_tiles.py
```

Both checkers use only standard-library exact rational arithmetic. The
optional `generate_reverse_angle_tiles.py` is numerical discovery provenance;
its proposals are checked independently and its optimizer statuses and
floating outputs are never accepted as proof evidence.
