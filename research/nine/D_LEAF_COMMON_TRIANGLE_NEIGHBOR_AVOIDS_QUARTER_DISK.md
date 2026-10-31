# A common triangle neighbor of a D root avoids the closed quarter disk

Date: October 28, 2026. Author: six_body.

**Status: new complete uniform local hand proof, submitted for independent
review. No original fine or coarse closure is asserted.**

## 1. Exact uniform statement

Keep all nine original interior-disjoint unit squares, their unchanged
circle and the common compatible selected certificate in

    79/40 <= R <= sqrt(1105)/16.

Let L be a genuine D leaf at H. Suppose H's other positive neighbors
are exactly one actual unit K and m actual physical-boundary units
A_1,...,A_m, where m>=1. Require that every A_i actually touches K.
These contacts may have zero stress. K and the A_i retain arbitrary
other true degrees, positive forces, circle masks and zero weights.
All the displayed units are distinct, and every original H force and
application is retained.

**Theorem.** The actual closed unit K avoids the closed disk of radius
1/4 centered at the original circle origin.

Thus the true root degree is m+2, without an upper-degree reduction.
No equation at K or any A_i is used. The theorem assumes no owner,
concurrence or fixed-point normal selection at those units.

Retain the existing same-nine R>2 theorem and its declared analytic
prerequisites for the earlier radius interval. The new argument below
works on the full R>2 domain, including the original upper endpoint.

## 2. Physical coordinate span at any original support feature

If P minimizes n=(-c,t) on a unit W, where c,t>0 and c^2+t^2=1,
then

    min_W y >= P_y-c.                                  (1)

For a minimum-support vertex use orthonormal inward axes u,v with
n.u,n.v>=0. Any axis with negative y component must have negative
x component as well. Write it (-p,-q), p,q>0. The support inequality
cp>=tq and p^2+q^2=1 give q<=c. There cannot be two downward axes,
since two southwest axes cannot be orthogonal. Thus the whole
downward extension is at most c. This includes a vertex endpoint of
an owned side, where one support inequality may be equality.

For a minimum-support side, the inward n direction has positive y
component; its whole length-one tangent interval has vertical span c.
The same bound follows at every actual position of P on that side.

Vertical reflection gives the companion fact: if Q minimizes
(-u,-v), with u,v>0 and u^2+v^2=1, then

    max_W y <= Q_y+u.                                  (2)

The proof permits arbitrary strict vertex normals, side normals and
original mean endpoints. It does not assume that W owns the normal.

## 3. A hypothetical near K fixes the actual shallow root chart

Suppose some actual z in K satisfies |z|<=1/4. Rotate the unchanged
genuine D-leaf chart so the actual radial leaf is east:

    r=R-sqrt(2), s=1-r,
    H=[-s,r] x [-b,a], a,b>0, a+b=1,
    p_HL=(r,0), n_HL=East.

The standard complete D-root margins at R>2 give

    r>1/2, s>1/3, r^2-s^2>1/16.                       (3)

If both a,b>1/4, the closed quarter disk lies in int H. Then the
actual z of the closed unit K lies in int H, forcing an overlap of
the two open interiors. Thus, reflecting every actual unit and force
vertically when necessary, the full remaining domain is

    0<a<=1/4, b=1-a>=3/4.                              (4)

Let n be the unchanged H-to-K unit normal. Since z lies beyond its
actual H support,

    h_H(n)<=n.z<=1/4.                                  (5)

If n_y<=0, the exact root support is at least
min(r,s,b)(|n_x|+|n_y|)>1/4, contradicting (3)--(5).
Consequently n_y>0.

The whole force-free shallow-D theorem applies to each physical
triple H,L,A_i at its original application and normal m_i. It gives

    (m_i)_y<=0 for every i.                             (6)

It permits arbitrary A_i degrees, physical circle masks, zero weights
and every shared-side or vertex contact feature.

## 4. The complete triangle cover forces Northwest and West/Southwest

If n is North, the actual physical triangle H,K,A_i and its owned-axis
normal theorem force (m_i)_y>=0. By (6) each is horizontal. The full H
vertical force sum would be strictly positive from its actual HK force,
with every other term zero. This is impossible.

If n is strict Northeast, the owned-axis triangle theorem excludes
West and South m_i, and the physical opposite-vertex triangle theorem
excludes strict Southwest m_i. With (6), the only remaining normals
are East and strict Southeast. The full original H horizontal force
would then be strictly positive, including its real East leaf. This
is impossible too.

The only surviving HK feature is therefore

    n=(-c,t), c,t>0, c^2+t^2=1,
    P=p_HK=(-s,a).                                    (7)

The same complete physical triangle cover and (6) now leave, for each
actual A_i, exactly West or strict Southwest. East and South fail the
owned-axis dot-product condition; strict Southeast is the opposite
root vertex; upward directions were excluded in (6).

For a West page its actual point is (-s,y_i), with -b<=y_i<=a.
Every point of a physical-boundary unit has norm at least
R-sqrt(2)=r. Thus (3)--(4) imply

    s^2+y_i^2>=r^2, |y_i|>1/4, y_i<-1/4.             (8)

Its unchanged origin moment is exactly y_i<0.

For each Southwest page, write its original normal as

    m_i=(-u_i,-v_i), u_i,v_i>0, u_i^2+v_i^2=1,
    Q_i=(-s,-b).                                     (9)

All initial axis and side-mean cases were included in the cover before
the strict vertices (7),(9) were obtained. No normal has been changed.

## 5. Full force and torque select an actual page with a small upward span

Let alpha>0 be the leaf magnitude, gamma>0 the HK magnitude and beta_i>0
the unchanged HA_i magnitudes. Write W,S for the West and Southwest
index sets. H's complete equations are

    alpha East+gamma n+sum_i beta_i m_i=0,
    gamma*(-s*t+a*c)
      +sum_(i in S) beta_i*(s*v_i-b*u_i)
      +sum_(i in W) beta_i*y_i=0.                   (10)

The leaf's zero origin moment explains its absence from the second
line. No other root force is dropped or replaced.

The y component and then cancellation of the s terms give

    gamma*t=sum_(i in S) beta_i*v_i>0,
    b*sum_(i in S) beta_i*u_i
      =gamma*a*c+sum_(i in W) beta_i*y_i
      <=gamma*a*c.                                 (11)

In particular S is nonempty. Taking the weighted average with actual
positive weights beta_i*v_i supplies an actual j in S such that

    u_j/v_j<=a*c/(b*t), and hence u_j<=4*a*c/(3*t). (12)

This does not change a magnitude, select a new contact or discard a
West moment. The negative West moments only strengthen the estimate.

From (5),(7),

    s*c+a*t<=1/4,
    0<c<3/4, a*t<1/4-c/3.                          (13)

Combining (12)--(13),

    c+u_j < c+c*(3-4*c)/(9*(1-c^2)).               (14)

The right side is less than one throughout 0<=c<=3/4. Its deficit
has positive denominator9(1-c^2) and numerator

    F(c)=9-12*c-5*c^2+9*c^3.

On this full interval,

    F'(c)=27*c^2-10*c-12
          <=(41/4)*c-12<=-69/16<0,
    F(3/4)=63/64>0.

Therefore

    c+u_j<1.                                        (15)

The strict inequalities cover the original upper radius, an actual
quarter-disk tangent point, and the a=1/4 shallow endpoint.

## 6. The actual K and selected A_j cannot touch

Apply the physical support bounds (1),(2) to the very points and
normals in (7),(9). They give

    min_K y>=a-c,
    max_(A_j) y<=-b+u_j=a-1+u_j.

By (15) the first bound is strictly larger. The two actual closed
units therefore have a positive vertical gap, contradicting the
assumed physical K--A_j contact. This proves the whole theorem.

## 7. Original caller maps and retained limits

The complete theorem supplies the following original necessary
conditions, all with the genuine D alternative retained:

| Original family | H | K | Complete boundary page list |
| --- | --- | --- | --- |
| House roof AC and ABC | T | D | A |
| Fan leaf at endpoint1, loads234 | 1 | fan hub | 2 |
| Fan leaf at inner vertex2, loads134 | 2 | fan hub | 1,3 |

The actual H degrees in these rows are3,3,4 respectively, including
the original genuine leaf. Every listed page physically touches K
through an original positive edge. All other true stars, including
the fan hub's fourth force and its loaded middle path vertices, remain.
The proof does not assign a degree-three equation to the inner fan
root or delete one of its two actual boundary pages.

The direct earlier inputs are RADIAL_BRIDGE_AND_LEAF_REDUCTION.md,
the complete force-free D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md,
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, and only the physical
opposite-vertex fact in END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md
Section2. NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md supplies the
earlier radius interval with its explicit inherited prerequisites.
Every new geometric and algebraic estimate is proved above.

The conclusion is a uniform quarter-disk avoidance statement for the
one actual common neighbor. It does not yet restrict all arbitrary
completion squares enough to close a whole original fine family or
coarse cell. A neighbor's zero multiplier alone is not a physical
clearance assertion. No source, original application, force, normal,
circle mask, shared ledger, remote repository, Lean file, build or CI
state was modified to obtain this theorem.
