# Same-original quadratic moment rows and rational square cuts

## Scope and notation

Fix any one of the unchanged original parents. Retain its original path, actual
CD bit, all cone assumptions, all nine centers, and all nine canonical physical
frames. The following construction neither selects a new geometric branch nor
replaces an original square by a separately chosen relaxation frame.

For original square i write its center as c_i=(x_i,y_i), and its canonical unit
side vectors as u_i=(alpha_i,beta_i), v_i=(-beta_i,alpha_i). Let
z_i=|beta_i|, g_i=1/[2(alpha_i+z_i)], and
h_i=(alpha_i+z_i)/2. Therefore

    alpha_i^2+beta_i^2=1,
    z_i^2=beta_i^2,
    2g_i alpha_i+2g_i z_i=1.

The canonical slope interval [l_i,u_i] is an already certified interval for
beta_i/alpha_i, with alpha_i>0. Hence

    beta_i^2-(l_i+u_i)alpha_i beta_i+l_i u_i alpha_i^2 <= 0.

Use the existing 54 scalar coordinates in their original ordering. Introduce a
formal coordinate X_ab for every unordered product of two original coordinates.
There are 1,485 such coordinates, giving 1,539 coordinates in total. Every
physical configuration embeds by X_ab=w_a w_b. The LP does not assert that an
arbitrary feasible formal X has this form. We use only the implication from a
physical configuration to a feasible lifted point.

## Exact physical quadratics

For each original i, containment of its four actual corners in the closed disk
with Q=1105/256 gives, for s,t in {-1,1},

    x_i^2+y_i^2+s(x_i alpha_i+y_i beta_i)
       +t(y_i alpha_i-x_i beta_i) <= Q-1/2.

These are exact expanded corner inequalities. The constant 1/2 uses the same
original frame identity alpha_i^2+beta_i^2=1. Proving exclusion even for the
closed disk is sufficient for the original strict problem.

For any physical pair put d=c_j-c_i. Disjoint open square interiors imply their
open radius-1/2 incircles are disjoint, so |d|^2>=1.

For an original square boundary point (s u_i+t v_i)/2, where max(|s|,|t|)=1,
that point cannot lie in the other square's open incircle. Otherwise nearby
interior points of the first square would also lie in the second square's
interior. Expanding its distance from the other center gives

    -|d|^2+alpha_i(s d_x+t d_y)+beta_i(s d_y-t d_x)
        <= (s^2+t^2-1)/4.

Central symmetry supplies this family for either owner using the same d. The
finite implementation uses all 16 rational boundary points whose coordinates
have denominator 2. Each is an actual point of that same original square.

The centered Cartesian square with half-side g_i lies in square i. Thus the two
inset squares are disjoint in open interiors and
max(|d_x|,|d_y|)>=g_i+g_j. For every rational |v|<1,

    d_x^2+d_y^2-2v d_x d_y >= (1-v^2)(g_i+g_j)^2.

If |d_x|>=g_i+g_j, complete the square as
(d_y-v d_x)^2+(1-v^2)d_x^2; the other alternative is symmetric.
This proof covers every signed alternative without adding a case to the parent.

The accepted same-original support-height lemma gives
|d|>=1+|h_i-h_j|. Therefore, for either sign sigma,

    -|d|^2+(h_i-h_j)^2+2sigma(h_i-h_j) <= -1.

The lemma and its physical proof are recorded in the repository's
`ORIGINAL_SUPPORT_HEIGHT_PAIR_HAND_PROOF.md`; the moment lift uses the exact
quadratic consequence rather than an independent secant per occurrence.

One additional degree-two consequence follows directly from physical separating
axes. Set

    c=alpha_i alpha_j+beta_i beta_j,
    s=alpha_i beta_j-beta_i alpha_j.

The canonical angles have difference in [-pi/2,pi/2], so c>=0. Whichever of the
two originals and two axes separates the square interiors, the corresponding
center projection has absolute value at least R=(1+c+|s|)/2. Consequently
|d|>=R. For any positive rational t and either sign sigma, the square
(R-t)^2>=0 gives

    -|d|^2+t c+t sigma s <= t^2-t.

All products here are products of the same original variables. No relative-frame
variable is chosen independently.

Finally, if an already proved canonical center difference or diagonal expression
L(w) belongs to [a,b], its quadratic secant is

    L(w)^2-(a+b)L(w) <= -ab.

The previous complete bound replay establishes each such interval before any
moment row is installed.

## Bound products and RLT products

For original bounds l_i<=w_i<=u_i, all four products of the corresponding
nonnegative bound slacks are nonnegative. Expanding them gives the standard four
McCormick inequalities for X_ij. The diagonal cases include the secant and the
two endpoint tangent bounds; additional midpoint tangents and X_ii>=0 are also
valid squares.

For any previously certified affine row A w<=b and any original variable k,
multiply its nonnegative slack by w_k-l_k and by u_k-w_k. The resulting necessary
quadratic inequalities are

    (A w)w_k-l_k A w-b w_k <= -b l_k,
    -(A w)w_k+u_k A w+b w_k <= b u_k.

The implementation selects a bounded finite family of existing affine rows and
forms these products with each of the 54 original variable intervals. Every
source row comes from the same unchanged original parent. No learned moment
row is multiplied, so the construction introduces no circular inference.

## Rational square cuts

For any rational vector q=(q_0,q_1,...,q_54), every physical configuration obeys

    -(q_0+sum q_(i+1) w_i)^2 <= 0.

After expansion and lifting this becomes

    -2q_0 sum q_(i+1)w_i
      -sum q_(i+1)^2 X_ii
      -2sum_(i<j) q_(i+1)q_(j+1)X_ij <= q_0^2.

A floating point eigensolver may propose q. It has no proof authority: q is
rounded to explicit rationals and the row is then reconstructed from the exact
displayed square identity. Every rational q gives a valid row regardless of the
eigensolver result. The finite pilot imposes a maximum number of rounds and
squares, and adds no geometric descendants.

## Terminal certificate and limits

Let M_i bound |w_i|. Then the physical product coordinate obeys
|X_ij|<=M_i M_j. If nonnegative rational weights combine finitely many necessary
lifted rows to A W<=b, the strictly positive rational reserve

    -b-sum B_k |A_k| > 0

contradicts all physical bounds |W_k|<=B_k, including product bounds. This exact
sum can prove the entire original parent. Numerical positive LP margins alone,
indefinite or positive semidefinite relaxed matrices, and exhausted square-cut
budgets grant no exclusion credit.

An independent replay must reconstruct every used source row and square, verify
every prior interval and original path, check all dual weights are nonnegative,
and reproduce the positive exact reserve. No Lean, Lake, or CI execution is
claimed by this discovery mechanism.
