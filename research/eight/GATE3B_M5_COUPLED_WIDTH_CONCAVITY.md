# Gate 3B.2 / M5: exact coupled orientation costs from eight cuts

2026-10-13. This is a full-domain analytic result for BOTH M5 folded types.
It eliminates continuous orientation optimization from a specified class
of positive pair-width expressions. It does NOT minimize the packing
radius, move square centers, freeze rotating SAT normals, or pass Gate 3B.2.

The input is the exhaustive angular-order cover in
`GATE3B_M5_TWO_FOLDED_TYPES.md`. Unlike the one-square, fixed-normal lemma
in `HUMAN_FINITE_ORIENTATION_DUAL.md`, the result below treats all eight
orientations together and includes their PAIRWISE interactions.

## 1. Folded coordinates and actual pair widths

Let h=pi/4. Use either word

    I:  L H L H L H L L,
    II: L H L L H H L L.

Index its positions by 0,...,7. Let s_i=0 for L and 1 for H, and put

    0=x_0<=x_1<=...<=x_7<=h,
    theta_i=x_i+h*s_i   modulo pi/2.

For i<j let d_ij=x_j-x_i in [0,h]. The true support sum of two unit
squares, along ANY of their eight signed actual side axes, is

    w_ij=(1+|cos(theta_j-theta_i)|+|sin(theta_j-theta_i)|)/2.

It has the following exact two forms:

    same letter:       f(d)=(1+cos d+sin d)/2,
    different letters: g(d)=(1+sqrt(2)*cos d)/2.             (1)

For the mixed case the relative angle is d+h or d-h. In either case
|cos|+|sin|=sqrt(2)cos d on the CLOSED interval 0<=d<=h.
This also handles quarter-turn and 45-degree boundary duplicates.

The separating-axis condition implies |p_j-p_i|>=w_ij for every actual
disjoint pair, but (1) keeps the actual support width rather than replacing
all such widths by the orientation-independent lower bound one.

## 2. Coupled concavity, including squared widths

On [0,h],

    f''(d)=-(cos d+sin d)/2 <= -1/2,
    g''(d)=-sqrt(2)cos d/2 <= -1/2.                       (2)

The squared functions are

    f(d)^2=1/2+(cos d+sin d)/2+sin(2d)/4,
    g(d)^2=1/2+sqrt(2)cos d/2+cos(2d)/4.

Consequently

    (f^2)''=-(cos d+sin d)/2-sin(2d) <= -1/2,
    (g^2)''=-sqrt(2)cos d/2-cos(2d) <= -1/2.             (3)

Here sin(2d),cos(2d)>=0. For any FIXED nonnegative pair weights
lambda_ij, each of

    sum lambda_ij*w_ij,       sum lambda_ij*w_ij^2         (4)

is therefore a concave function of the ENTIRE folded vector x: each
summand is a concave scalar function of the affine difference x_j-x_i.
The orientations cannot be minimized independently; their ordering and
all pair labels remain coupled throughout this argument.

## 3. Exact minimization by eight cut configurations

For k=1,...,8 let v^(k) be the folded vector whose entries before k are
zero and whose entries from k onward are h. In particular v^(8)=0.
These are exactly the eight vertices of the closed ordered simplex.

At v^(k), the actual frames are either 0 or h modulo pi/2. Define the
corresponding two-color assignment by

    b_i^(k) = s_i                     if i<k,
              1-s_i                  if i>=k.

Let C_k be the set of pairs whose two b labels differ, and put

    w_star=(1+sqrt(2))/2,
    kappa=w_star-1=(sqrt(2)-1)/2,
    kappa2=w_star^2-1=(2sqrt(2)-1)/4.

### Theorem 1: weighted eight-cut formula

For either folded word and every nonnegative weight array,

    min_x sum lambda_ij*w_ij
       = sum lambda_ij + kappa * min_(k=1,...,8) sum_(ij in C_k) lambda_ij,

    min_x sum lambda_ij*w_ij^2
       = sum lambda_ij + kappa2 * min_(k=1,...,8) sum_(ij in C_k) lambda_ij. (5)

The minimum is over the CLOSED folded region. The cuts C_k are the eight
specific cuts just defined, NOT all arbitrary bipartitions of the labels.

Proof. A concave function on a finite simplex is at least the convex
combination of its vertex values and hence at least their minimum.
Every vertex belongs to the domain. At a vertex a within-color pair has
width one and a cross-color pair has width w_star. Substitute these exact
values into (4). This proves both equality formulas. QED.

No angle grid, numerical minimizer, interval subdivision, or assumed
packing deformation is involved in (5).

## 4. A quantitative certificate away from the cut configurations

Define barycentric coefficients

    beta_k=(x_k-x_(k-1))/h for k=1,...,7,
    beta_8=(h-x_7)/h.

They are nonnegative, sum to one, and x=sum beta_k*v^(k).
For every pair, the vertex differences are either zero or h, with mean
 d_ij and variance d_ij(h-d_ij).

If F''<=-1/2 on [0,h], then F(t)+t^2/4 is concave, so

    F(d)>=(1-d/h)F(0)+(d/h)F(h)+d(h-d)/4.                (6)

Apply (6) to f,g,f^2,g^2 and sum with the fixed nonnegative weights.
For either cost in (4),

    cost(x) >= sum_k beta_k*cost(v^(k))
                  + (1/4) sum_(i<j) lambda_ij*d_ij*(h-d_ij).             (7)

In particular (5)'s minimum remains a lower bound after adding the
nonnegative displayed correction. Formula (7) is sharper because it
retains the actual barycentric average of the eight different cut costs.

## 5. Uniform weights: sharp global M5 dispersion bounds

For BOTH words, the number of zero-phase frames at v^(k), k=1,...,8, is

    I:  (4,3,4,3,4,3,4,5),
    II: (4,3,4,5,4,3,4,5).

Thus |C_k|=16 for odd k and 15 for even k. Let

    A(x)=[(x_1-x_0)+(x_3-x_2)+(x_5-x_4)+(x_7-x_6)]/h,
    V(x)=sum_(i<j) d_ij*(h-d_ij).

Then 0<=A<=1 and V>=0. Formula (7) gives the exact inequalities

    sum_(i<j) w_ij
      >= (41+15sqrt(2))/2 + kappa*A(x) + V(x)/4,

    sum_(i<j) w_ij^2
      >= (97+30sqrt(2))/4 + kappa2*A(x) + V(x)/4.         (8)

In particular their infima over M5 are respectively

    (41+15sqrt(2))/2 = 31.1066017...,
    (97+30sqrt(2))/4 = 34.8566017....

For an ACTUAL maximum-five frame multiset both inequalities without the
A,V correction are strict. Indeed V=0 forces every x_i to be zero or h
(use the pairs (0,i)); these give only two phase values 0,h, all of which
fit in one closed h-window, so their maximum count is eight, not five.

The constants are nevertheless sharp infima for M5 orientations. For
word I take x_i=i*epsilon for i=0,...,3, and
x_i=h-(8-i)*epsilon for i=4,...,7, with 0<epsilon<h/8.
These are strict folded orders of type I, hence generic maximum-five
frames. As epsilon tends to zero they approach v^(4), with phase counts
3 and 5. The costs converge to the constants in (8).
This statement is about orientations, not existence of a disk packing
with those orientations or attainment of a packing radius.

The same concavity proof applied to
sin(2d) for same letters and cos(2d) for different letters also gives

    sum_(i<j) |sin(2(theta_j-theta_i))| >= 15.            (9)

## 6. What this does and does not allow in the geometric gate

Theorem 1 is useful when a necessary inequality or dual bound contains
fixed NONNEGATIVE coefficients multiplying actual w_ij or w_ij^2. Its
entire M5 orientation cost can then be replaced by eight explicit cuts,
or bounded more sharply by (7). This is a complete angular subproblem,
not a collection of isolated orientation boxes.

It is NOT valid to conclude that the packing radius is minimized at
these cuts. In an actual SAT fiber the chosen normals move with their
owner frames; in a center-eliminated dual the force penalties also vary.
Those extra terms do not inherit (2)--(3). Likewise the square's disk
vertices vary with the frame. Keep all of them in any sharp argument.

Theorem 1 does not say that an actual M5 packing can be replaced by a
3+5 two-frame packing at no radius cost. No such geometric deformation
has been proved. It also does not exclude all M5-I or M5-II arrangements.
The joint center/owner Gate 3B.2 remains open.
