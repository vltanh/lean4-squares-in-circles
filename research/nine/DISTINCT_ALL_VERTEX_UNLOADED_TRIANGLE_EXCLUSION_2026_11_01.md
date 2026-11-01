# Distinct-contact unloaded triangle: complete exclusion when all three originals are vertices of both incident squares

November 1, 2026. Continuation of PR #11 from `ad00eaa16a27e5e1000d1a9dc7be0c4421c54b91`.

**Evidence at construction:** H. The root supplied the force-weighted support estimate and the geometry agent independently reconstructed it; both contributed to the finite contact-triangle classification. A noncontributor review remains requested. No numerical search, mathematical script, Lean or CI is needed for this theorem.

## 1. Exact original scope

Keep the same actual nine interior-disjoint unit squares in a disk with center O and radius R, together with one unchanged original selected physical contact-force-and-torque certificate. Three actual squares A,B,C are entirely selected-circle-unloaded. Their original positive graph has internal triangle AB,BC,CA, and each has full positive degree exactly three: its two internal edges and exactly one original positive outside exit. The actual outside terminals may repeat and have arbitrary frames, degrees, loads and other contacts. All six other actual squares remain in the original packing.

Assume the actual core squares have no common physical point. Assume further that the **original application on each of AB, BC, CA is a vertex of both incident actual squares**. Denote these unchanged applications by p_AB,p_BC,p_CA. No application, force normal, mean or outside terminal is reselected.

Then

    R > 9/4,

so in particular this complete feature is impossible at R^2<=1105/256. The assumption is stronger than saying each contact has a vertex owner on one side: genuine vertex-to-side-interior contacts are not covered by this theorem.

The case where there is a common physical point is separately and completely excluded by [COMPLETE_COMMON_JUNCTION_UNLOADED_TRIANGLE_EXCLUSION_2026_11_01.md](COMPLETE_COMMON_JUNCTION_UNLOADED_TRIANGLE_EXCLUSION_2026_11_01.md), including its original shared-side means.

## 2. A finite geometric classification forces the outward equilateral arrangement

The three original applications are distinct. Equality of any two would put the same physical point in all three squares, contrary to the stated premise.

Each core square contains two of these applications as distinct vertices. Their distance is therefore either 1 (adjacent vertices) or sqrt(2) (opposite vertices). Thus the three applications form a nondegenerate triangle T: the largest possible side is sqrt(2)<2, the smallest possible sum of the other two sides.

Call a side of T diagonal when its length is sqrt(2). At an endpoint of a diagonal, the corresponding actual square has an inward quadrant whose bisector points along that diagonal toward the other endpoint. Its angular half-width is pi/4.

**At least two diagonals are impossible.** Choose their common endpoint. Their lengths are both sqrt(2), while the opposite side is at most sqrt(2). The angle between them is therefore at most pi/3, hence strictly less than pi/2. The interiors of the two pi/2 tangent quadrants centered along these two directions overlap. The actual square interiors then overlap in a neighborhood of that endpoint, contradicting the packing condition.

**Exactly one diagonal is impossible without a common point.** The other two sides both have length 1. T is consequently a right isosceles triangle whose hypotenuse is the diagonal of one core square. The third contact point is precisely one of that square's other two vertices. It already belongs to the other two core squares by definition, so all three actual squares contain it. This contradicts the no-common-point premise.

Thus all three sides have length 1 and T is equilateral. Every actual core square is based on its corresponding side. It must extend outward from T: if it extended toward the third contact vertex, that vertex would lie in the square's interior, since its base coordinate is 1/2 and altitude sqrt(3)/2 is strictly between zero and one. The interior of either other square near that vertex would then overlap it.

We have proved the entire contact geometry, rather than assuming a symmetric force pattern. In particular the pair intersections are point-only vertices and the original strict singleton-normal convention applies to both incident squares at every internal edge. The original positive magnitudes and directions need not be symmetric.

## 3. Torque bounds every original exit to a closed pi/2 cone

Consider one core square, and use a rigid coordinate chart in which its actual base side of T is

    p_L=(-1/2,0),     p_R=(1/2,0),

the actual square is [-1/2,1/2] x [0,1], and T lies below it. The common centroid H of T is

    H=(0,-sqrt(3)/6).

The original internal forces at p_R and p_L have forms

    f_R=(r,-a),     f_L=(-s,-b),
    r,s,a,b>0.

These strict signs follow from their unchanged strict normals exposing the actual bottom-right and bottom-left vertices of this square. They are the full force vectors, including their positive magnitudes.

The complete unloaded translation makes the sole original outside force

    E=(s-r,a+b)=(T_0,V),     V=a+b>0.

The original outside application q maximizes E on the actual core square. Its vertical coordinate is therefore 1.

If T_0>0, q=(1/2,1). The complete torque equation about the base midpoint is

    -a/2+b/2 + V/2 - T_0 = 0,

which gives T_0=b<V. If T_0<0, q=(-1/2,1), and the original torque equation becomes

    -a/2+b/2 - V/2 - T_0 = 0,

which gives T_0=-a and |T_0|=a<V. If T_0=0, q may retain any original top-side mean; its horizontal coordinate will not affect the support calculation below.

In every case the outside unit normal e=E/|E| makes an angle delta with the outward vertical satisfying

    |delta| < pi/4.

Using the larger closed interval |delta|<=pi/4 in the subsequent estimate only weakens the bound. This includes the limiting force and normal directions without replacing any positive force by zero.

## 4. An actual outside point has support greater than 9/4 about the same H

At its unchanged outside neighbor, q is a minimum support point in direction e. The elementary actual-unit-step lemma therefore gives an actual point of that neighbor,

    w=q+e.

For completeness, in the neighbor's own unit side coordinates, adding a nonzero component of e moves inward from the minimizing endpoint by at most one; a zero component leaves the original coordinate unchanged. Hence w belongs to the unchanged outside square, for arbitrary outside frame and every original support mean.

Put

    d=1+sqrt(3)/6,     t=|delta|.

The actual support of q about H is exactly

    e dot (q-H) = d cos(t) + (1/2) sin(t).

This formula also holds at t=0 regardless of the original top-side mean. Consequently

    e dot (w-H) = 1 + d cos(t) + (1/2) sin(t),
    0<=t<=pi/4.

The function f(t)=d cos(t)+(1/2)sin(t) has f''(t)=-f(t)<0 throughout this interval. Its minimum on the interval is therefore attained at an endpoint. Both endpoint values are strictly greater than 5/4:

    f(0)=1+sqrt(3)/6 > 5/4,
    f(pi/4)=(3/2+sqrt(3)/6)/sqrt(2) > 5/4.

The first inequality is equivalent to sqrt(3)>3/2. For the second, multiply by 12sqrt(2) to obtain the equivalent positive-side comparison

    18+2sqrt(3) > 15sqrt(2).

Squaring reduces it to sqrt(3)>19/12, which follows from 3>361/144. All comparisons are exact. It follows that every one of the three original exits supplies an actual disk point satisfying

    e_i dot (w_i-H) > 9/4.                         (1)

The same centroid H is used for all three squares; their own coordinates merely rotate the calculation.

## 5. Full-force averaging contradicts the original disk radius

Let z_i>0 be the three unchanged original outside magnitudes. Adding the complete unloaded core translations cancels all three internal original forces, and therefore

    sum_i z_i e_i = 0.

Every actual w_i lies in the same original disk. Since e_i is a unit vector,

    e_i dot (w_i-O) <= |w_i-O| <= R.

Multiply by z_i and sum. The displayed force cancellation removes the common translation H-O, giving

    R sum_i z_i
      >= sum_i z_i e_i dot (w_i-O)
       = sum_i z_i e_i dot (w_i-H)
       > (9/4) sum_i z_i.

The sum of the original exit magnitudes is positive, so R>9/4, as claimed. In particular

    R^2 > 81/16 = 1296/256 > 1105/256.

No outside equations were shortened or imposed; no outside terminal was assumed distinct. The argument uses all three full original translations and each original torque equation at exactly its stated application points.

## 6. Exact coverage and surviving physical features

| All-both-vertex contact-triangle type | Complete physical conclusion |
| --- | --- |
| At least two length-sqrt(2) sides | Two actual inward vertex quadrants overlap |
| Exactly one length-sqrt(2) side | The third contact is a common physical point of all three cores |
| Three length-1 sides with a core toward T | That core contains the third contact in its interior, causing overlap |
| Three length-1 sides, all cores outward | Full torque and the original force-weighted disk-point estimate give R>9/4 |

This exhausts the stated all-both-vertex feature. It recovers, with a complete argument and exact normal/torque treatment, the previously exploratory all-vertex exclusion claim. The surviving no-common-junction direct triangle must have at least one original pair application that is **not** a vertex of both incident squares: a genuine vertex-to-side-interior feature or an original shared-side mean remains to be treated.

This is a whole geometric feature closure only. The complete direct-triangle family and original coarse parents are not declared closed, and the canonical counts remain 41/58 coarse, 2,373/2,513 fine and 18/38 nested exterior unless another full original-domain theorem is separately joined.
