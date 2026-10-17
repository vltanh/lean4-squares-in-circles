# Radial ends and small positive-stress trees

Status: analytic consequences of the physical contact equilibrium in
`HUMAN_CONTACT_EQUILIBRIUM.md`. Under the explicit hypothesis

    R > sqrt(2)+1/2,

every nontrivial tree component of that positive-stress graph has at least
four vertices. This is a restriction on a stress at a radius minimizer,
not a new unrestricted lower bound for eight squares.

The proof also gives a complete list of possible radii for a three-vertex
positive-stress tree when `R>sqrt(2)`. It does not require that the minimizer
have the fewest actual contacts. Actual contacts of weight zero remain
allowed throughout.

## 1. Notation and previously proved equilibrium facts

Assume `R>sqrt(2)` and use a physical contact stress supplied by
`HUMAN_CONTACT_EQUILIBRIUM.md`. Its graph has an edge for each pair with
positive total contact weight. Each edge has a unit separator n, chosen
from the signed side normals of at least one of its endpoint squares.
Combining its endpoint coefficients gives one effective contact point in
the actual common contact set.

We use three established facts:

* If a square has nonzero resultant force F, its center is the unique
  maximizer of `F dot p` over its exact fixed-frame admissible center
  region K_R. The support centers are calculated in
  `BALANCED_SEPARATOR_REDUCTION.md`, section 2.
* Every positive-stress bridge has its effective contact point on the
  radial line in its separator direction. This is the bridge theorem in
  `HUMAN_CONTACT_EQUILIBRIUM.md`, section 5.
* Every nontrivial positive-stress tree component contains a square
  containing zero as a point of its closed square. This is the tree
  corollary in that note, section 6.

Put

    rho = sqrt(R^2-1/4),
    a   = R-sqrt(2),
    b   = rho-1.

Both a and b are strictly positive under our radius hypothesis.

## 2. A positive-stress leaf has one of two radial forms

**Stress-leaf theorem.** Let S have degree one in the positive-stress
graph, and let n point from its unique stress neighbor toward S. Then
exactly one of the following descriptions applies:

1. **Side normal.** The vector n is a side normal of S,

       center(S) = (rho-1/2)n,
       effective contact point = b n.

2. **Diagonal.** The vector n is a diagonal direction of S,

       center(S) = (R-1/sqrt(2))n,
       effective contact point = a n.

   In this case the selected separator must be a side normal of S's
   neighbor, since it is not a side normal of S.

Every positive-stress leaf avoids zero even as a point of its closed
square. This theorem concerns degree in the positive-stress graph; S may
have additional actual contacts with zero chosen stress.

### Proof

The force on S is `lambda n` for some `lambda>0`. Its center therefore
maximizes support in direction n. The sole stress edge is a bridge, so
its effective contact point z is radial and lies on the inward supporting
face of S in direction n.

Choose signed and ordered axes `(e,f)` of S such that

    n = c e+s f,      c >= s >= 0,      c^2+s^2=1.

This is merely a choice of coordinates for the same square. The exact
support-center formula has two branches.

If `c>=2 rho s`, the maximizing center has coordinates

    p = (rho-1/2)e.

If `s>0`, its inward supporting face for n is the single vertex

    z = b e-f/2.

This vector cannot be parallel to n: its e coordinate is positive and its
f coordinate is negative, while both coordinates of n are positive. Thus
this branch permits only `s=0`. Then `n=e`, the inward face is the edge
with e coordinate b, and its only point on the radial line is `z=b n`.
This is the first stated form.

If `c<=2 rho s`, then `s>0`, and the maximizing center is

    p = R n-(e+f)/2.

Its inward supporting face is the single vertex

    z = R n-(e+f).

For z to be parallel to n, the vector `e+f` must be parallel to n.
Hence `c=s=1/sqrt(2)`, which gives the second stated form.
The formulas coincide at the support-branch boundary, so no boundary
case has been omitted.

In the first case all points of S have `n dot x>=b>0`; in the second
case all have `n dot x>=a>0`. Neither leaf contains zero. Finally the
chosen edge separator is a side normal of at least one endpoint square.
In the diagonal case it cannot be a side normal of S, so it must belong
to its neighbor. This proves every assertion.

The diagonal alternative cannot be removed merely by angular
stationarity. An actual leaf in a minimum-contact minimizer was shown to
have only the side-normal form in `HUMAN_STRESS_GRAPH.md`, but that proof
uses a finite motion which additional zero-stress actual contacts could
block.

## 3. Two vertices cannot form a positive-stress component

Under `R>sqrt(2)`, there is no positive-stress component consisting of
exactly two vertices and their edge. It would be a nontrivial tree whose
two vertices were both leaves. Section 2 says neither leaf contains zero,
contradicting the tree-origin corollary recalled in section 1.

An isolated vertex is not excluded; it carries no incident positive
stress. Nor does this assertion exclude two squares from belonging to a
larger positive-stress component.

## 4. Exact classification of a three-vertex positive-stress tree

**Three-vertex theorem.** If `R>sqrt(2)` and a positive-stress component
is a tree on three vertices, then R belongs to the following four-element
set:

    sqrt(5/2),
    sqrt(7/4+sqrt(2)),
    (18+7sqrt(2))/16,
    sqrt(2)+1/2.                                       (4.1)

This is a list of necessary possibilities; it does not assert that each
can occur as a component of a larger radius-minimizing packing.

### 4.1. Its middle square is force-free and the two normals are opposite

Write the component as `A--B--C`. The endpoints are positive-stress
leaves and avoid zero by section 2. The tree-origin corollary therefore
places zero in the closed square B.

Every point of a unit square containing zero has norm at most `sqrt(2)`,
its diameter. Since `R>sqrt(2)`, B is strictly inside the disk. All its
circle coefficients vanish. Force balance then gives `F_B=0`.

Let `n_A,n_C` point from B toward its two neighbors, with positive edge
weights `lambda_A,lambda_C`. The force equation is

    lambda_A n_A + lambda_C n_C = 0.

Taking norms gives equality of the two weights and
`n_C=-n_A`. Write `n=n_A`. The radial contact points are consequently

    z_A = d_A n,       z_C = -d_C n,
    d_A,d_C in {a,b}.                                   (4.2)

These are points of the two opposite support faces of B. Their normal
separation is `d_A+d_C`, exactly B's width in direction n.

### 4.2. The middle square is parallel or diagonal to the common normal

If n is a side normal of B, that width is one.

If n is not a side normal, each of B's opposite support faces is a
single vertex. They are opposite vertices of the square. By (4.2) their
difference is parallel to n, so a diagonal of B is parallel to n. The
width in that direction is therefore `sqrt(2)`.

Moreover, if either endpoint has the diagonal form in section 2, the
selected separator of its edge must be a side normal of B. In that case
only the width-one alternative is possible.

### 4.3. The four scalar possibilities

The preceding alternatives leave exactly these equations:

| Leaf A | Leaf C | Direction n in B | Equation |
| --- | --- | --- | --- |
| Side normal | Side normal | Side normal | `2b=1` |
| Side normal | Side normal | Diagonal | `2b=sqrt(2)` |
| Side normal | Diagonal | Side normal | `a+b=1` |
| Diagonal | Diagonal | Side normal | `2a=1` |

The mixed case includes exchanging A and C. Substitution of
`b=sqrt(R^2-1/4)-1` and `a=R-sqrt(2)` gives respectively

    R = sqrt(5/2),
    R = sqrt(7/4+sqrt(2)),
    R = (18+7sqrt(2))/16,
    R = sqrt(2)+1/2.

For the mixed case, the equation is

    rho+R = 2+sqrt(2).

Using `R^2-rho^2=1/4` and solving for R gives the displayed exact value.
All steps preserve the signs `R,rho>0`, so no extraneous root is used.
This proves the three-vertex theorem.

## 5. Consequence and its precise radius dependence

All four radii in (4.1) are at most `sqrt(2)+1/2`. For the second one,
the squares of the radii differ by exactly `1/2`. The first inequality
is immediate after squaring. For the mixed case,

    (18+7sqrt(2))/16 < sqrt(2)+1/2

is equivalent to `10<9sqrt(2)`, which follows from `100<162`.

Combining sections 3 and 4 proves:

> If `R>sqrt(2)+1/2`, every nontrivial tree component of the physical
> positive-stress graph has at least four vertices and contains a square
> through the disk center.

This conclusion is entirely analytic under its stated radius hypothesis.
Applying that hypothesis to the unknown eight-square minimum via the
existing bound `R_8^2>19/5` would use the earlier computational certificate.
Indeed `19/5>(sqrt(2)+1/2)^2=9/4+sqrt(2)`, but this comparison does not turn
the certificate-based lower bound into an analytic theorem.

The later nonradial-component theorem in
`HUMAN_CONTACT_EQUILIBRIUM.md`, section 8, strengthens this conclusion when
`sqrt(2)+1/2<R<2`: every nontrivial positive-stress component has a nonzero
contact-moment circulation and hence a cycle, so trees of every order are
excluded in that interval. Its proof uses the radial forms from section 2
above and treats squares with zero on their boundary as well as in their
interior.

The remaining unrestricted graph problem is to make such a cycle force
the twin interior degree-two vertices and the known four-square parallel
scaffold, or an equally strong projected obstruction. Neither the exact
small-tree classification here nor that stronger cycle theorem alone
identifies the sharp eight-square radius.
