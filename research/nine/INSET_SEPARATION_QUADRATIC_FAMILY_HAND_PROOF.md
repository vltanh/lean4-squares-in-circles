# One quadratic family retains every original inset-separation alternative

November 3, 2026. Complete hand proof, independently checked. This is a
shared physical consequence for any pair of original squares. A finite
selection of its rows is used inside the whole-original induction; no
finite selection is claimed to be an exact substitute for physical
nonoverlap. No Lean, Lake, or CI.

## 1. Original physical variables and the entire alternative

For original square i write its canonical side frame as

    u_i=(alpha_i,beta_i), v_i=(-beta_i,alpha_i),
    alpha_i>=|beta_i|, alpha_i^2+beta_i^2=1.

Set h_i=(alpha_i+|beta_i|)/2 and g_i=1/(4h_i). The same original
square contains the centered aligned square with halfwidth g_i.
For distinct physical originals i,j put

    x=x_j-x_i, y=y_j-y_i, g=g_i+g_j>0.

Disjoint original interiors imply disjoint interiors of those contained
insets, hence

    max(|x|,|y|)>=g.                                      (1)

This single disjunction retains all four signed coordinate alternatives,
including contact and ties. It does not require selecting an owner or
changing either original frame.

## 2. A quadratic inequality for every rational parameter

For every real t with -1<=t<=1, (1) implies

    x^2+y^2-2txy >= (1-t^2)g^2.                           (2)

Indeed, if |x|>=g, the difference between the two sides is

    (y-tx)^2+(1-t^2)(x^2-g^2)>=0.

If |y|>=g, interchange x and y in that identity. Both cases retain
equality, t=1 and t=-1. The parameter may be any fixed rational number;
it is not an original angle or a new geometric premise.

Conversely, the family (2) for all rational t in [-1,1] implies (1).
If |x|<g and |y|<g, the real parameter t_0=xy/g^2 lies in (-1,1) and
gives the exact negative difference

    -(g^2-x^2)(g^2-y^2)/g^2<0.

Continuity gives a rational parameter sufficiently close to t_0 with
the same strict violation. Thus the complete rational family is
equivalent to the closed original-inset separation disjunction.
Only the forward implication is needed for a certificate using finitely
many displayed rational parameters. Such a finite table remains a
necessary relaxation; feasibility of that relaxation is not a packing.

## 3. Exact affine rows on previously proved difference intervals

Suppose the entire caller has proved x in [l_x,u_x], y in [l_y,u_y].
For any interval [l,u] containing z,

    z^2 <= (l+u)z-lu,

because (z-l)(z-u)<=0. An affine upper bound

    q_t:=x^2+y^2-2txy <= U_x x+U_y y+C                  (3)

can be obtained in either of two ways.

First, use the nonnegative decomposition

    q_t=(1-t)(x+y)^2/2+(1+t)(x-y)^2/2,

and apply the square secant to both proved sum/difference intervals.
Second, use individual square secants and either applicable product
envelope. For t>=0, the two lower product planes

    xy>=l_y x+l_x y-l_x l_y,
    xy>=u_y x+u_x y-u_x u_y

give upper bounds after multiplication by -2t. For t<=0, use the two
upper planes

    xy<=l_y x+u_x y-u_x l_y,
    xy<=u_y x+l_x y-l_x u_y.

Each plane is just a product of two nonnegative interval distances.
It remains valid for signed intervals and degenerate endpoints.

For any rational c, the square identity gives g^2>=2cg-c^2. Combining
(2) and (3), with 1-t^2>=0, therefore yields the necessary affine row

    -U_x x-U_y y+2(1-t^2)c(g_i+g_j)
        <= (1-t^2)c^2+C.                              (4)

Its slack is exactly the sum of the following three nonnegative terms:

    (U_x x+U_y y+C-q_t)
    +(q_t-(1-t^2)g^2)
    +(1-t^2)(g-c)^2.

This identity independently checks the signs and the right-hand side.
No condition that c belong to a current g interval is needed.

The standalone generator `computer_assisted/inset_quadratic_rows.py`
uses exact fractions, the same original coordinate and inset variables,
and both constructions of (3). Every supplied difference and scalar
interval must itself have a proof on the complete caller. New bounds
are installed only after their nonnegative rational sums are checked;
the next round's stronger rows then follow by ordinary finite induction.

## 4. A complementary diamond family

The same canonical original square contains the diamond

    |X|+|Y|<=k_i, k_i=1/(2alpha_i).

Its four axis vertices satisfy the original square's two side
inequalities because |beta_i|<=alpha_i. Convexity supplies the entire
diamond. Thus disjoint original interiors imply

    |x|+|y|>=k_i+k_j=:K.

Apply Section 2 to X=x+y, Y=y-x and use
max(|X|,|Y|)=|x|+|y|. For every -1<=t<=1 this gives

    2(1+t)x^2+2(1-t)y^2 >= (1-t^2)K^2.                 (5)

For a positive rational c one also has

    k_i >= 1/c-alpha_i/(2c^2),

with exact difference (alpha_i-c)^2/(2alpha_i c^2). The lower
expressions are positive for c in {3/4,7/8,1} throughout the canonical
range 1/sqrt(2)<=alpha_i<=1. Their positive sum may therefore replace
K before squaring in (5). This supplies quadratic rows on the shared
original-frame variables without adding a new physical hypothesis.
The diamond extension is valid mathematics; its use or non-use in an
individual delivered certificate is determined by that certificate's
explicit row inventory.

## 5. Scope of the shared rule

All arguments keep both original squares, their shared frames and the
closed contact faces. The result holds independently of the disk radius
or marked mask. It can therefore be reused across the 32 masks without
transferring any mask-specific height or weak-link claim.

The rule alone declares no cell or mask closed. A complete exclusion
requires its original caller, proved interval/guard provenance, a full
acyclic deduction chain and a final exact contradiction. A feasible
linear or second-moment relaxation does not negate this theorem and
does not establish a physical counterexample. The independent hand
review is `INSET_SEPARATION_QUADRATIC_AFFINE_INDEPENDENT_REVIEW.md`.
