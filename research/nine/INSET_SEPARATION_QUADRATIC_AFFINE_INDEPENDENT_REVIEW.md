# Independent review: original-inset quadratic family and affine rows

November 3, 2026. This review establishes the continuous implication and
row algebra. It closes no original cell or whole mask. No Lean, Lake or CI.

## Physical implication and exact scope

Let two unchanged physical originals contain concentric axis-aligned open
square insets of halfwidths g_i,g_j>0. Write x=x_j-x_i, y=y_j-y_i and
g=g_i+g_j. Disjoint original interiors imply max(|x|,|y|)>=g.
For every real t with -1<=t<=1,

    q_t(x,y)=x^2+y^2-2txy >= (1-t^2)g^2.

If |x|>=g, subtracting the right side leaves
(y-tx)^2+(1-t^2)(x^2-g^2)>=0. If |y|>=g use the symmetric identity.
The common and contact faces are included.

Conversely, when |x|<g and |y|<g, t_0=xy/g^2 lies strictly between -1
and 1, and the difference equals

    -(g^2-x^2)(g^2-y^2)/g^2 < 0.

Continuity supplies a rational t with the same strict negative value.
Thus the family for every rational t in [-1,1] is equivalent to the full
closed inset-separation union. Any fixed finite parameter list supplies
necessary implications only. This equivalence does not identify a
pseudo-moment vector with a physical packing.

## Reviewed affine generator

Reviewed source:
`/workspace/scratch/2281714110bb/root_macro/inset_quadratic_rows.py`.
All input intervals must have been proved for the same original parent.
Set x in [xl,xu], y in [yl,yu], and r=1-t^2>=0.

For the rotated upper bound, put u=x+y and v=x-y. Their intervals are
[ul,uu]=[xl+yl,xu+yu] and [vl,vu]=[xl-yu,xu-yl]. With
A=(1-t)/2>=0 and B=(1+t)/2>=0,

    q_t=A u^2+B v^2.

The bound s^2<=(lo+hi)s-lo*hi gives q_t<=Ux*x+Uy*y+C with exactly the
coefficients printed by the generator. Its nonnegative error is

    A(uu-u)(u-ul)+B(vu-v)(v-vl).

For the direct upper bounds, the x^2 and y^2 secant errors are
(xu-x)(x-xl) and (yu-y)(y-yl). When t>=0, the code correctly chooses the
lower xy planes yl*x+xl*y-xl*yl and yu*x+xu*y-xu*yu, since their multiplier
-2t is nonpositive. Their xy errors are (x-xl)(y-yl) and
(xu-x)(yu-y). When t<0, it correctly chooses the upper planes
 yl*x+xu*y-xu*yl and yu*x+xl*y-xl*yu; their errors are
(xu-x)(y-yl) and (x-xl)(yu-y). Thus both printed direct bounds are valid.

For every real tangent parameter c, g^2>=2cg-c^2. Hence the physical
quadratic implication and any upper bound q_t<=Ux*x+Uy*y+C give

    -Ux*x-Uy*y+2rc(g_i+g_j) <= rc^2+C.

This is precisely the generated row, including its signs and right side.
The choice c=1 remains valid if 1 lies outside the current g interval.
The scalar indexing is correct: scalar[27+i] is original g_i, whose
full variable index is 45+i. The center coefficients correctly expand
the differences x_j-x_i and y_j-y_i. Every arithmetic operation in the
reviewed generator uses Fraction.

For a direct identity showing the row slack, it equals

    (Ux*x+Uy*y+C-q_t) + (q_t-rg^2) + r(g-c)^2,

and each term is nonnegative under the proved physical and interval
hypotheses. This also checks the zero parameters t=0 and t=+-1.

## Diamond extension

In the canonical original frame alpha_i>=|beta_i| and alpha_i^2+beta_i^2=1,
the original square contains the diamond |x|+|y|<=k_i=1/(2alpha_i).
The vertices satisfy both original side-coordinate inequalities; convexity
proves containment. Disjoint original interiors therefore imply
|x|+|y|>=k_i+k_j.

Apply the preceding quadratic family to X=x+y and Y=y-x, whose maximum
absolute value is |x|+|y|. This proves

    2(1+t)x^2+2(1-t)y^2 >= (1-t^2)(k_i+k_j)^2.

For every positive rational c,

    k_i >= 1/c-alpha_i/(2c^2),

because the difference is (alpha_i-c)^2/(2 alpha_i c^2)>=0.
For c in {3/4,7/8,1} this affine expression stays strictly positive
on alpha_i in [1/sqrt(2),1]. Consequently the sum of any two such affine
lower bounds may be squared on the right, giving a necessary quadratic
row in the same original alpha variables. All signs and frames remain.

## Acceptance boundary

A full original-cell closure additionally needs its unchanged path,
proved center/difference/frame intervals, exact source-bound nonnegative
row sum, positive reserve after paying every residual coefficient, and
complete parent coverage. No closure is inferred from this review, from
a feasible LP/moment vector, or from a partial numerical cut sequence.
The static batch's interval provenance must be retained with any later
candidate. Unchanged accepted prefix certificates may be reused with
byte identity distinguished from a new arithmetic replay.
