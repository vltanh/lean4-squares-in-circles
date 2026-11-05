# Owner-free distance bounds from the same original square frames

This note gives necessary constraints for every one of the 36 pairs of nine
independently oriented physical unit squares. No separating-axis owner or
axis is chosen. It is a new invariant, not a claim that any original cell or
whole mask has closed. All variables retain their original-square identities.

## 1. All eight physical SAT alternatives share one support threshold

Write the original orthonormal frame of square `i` as

\[
u_i=(\alpha_i,\beta_i),\qquad v_i=(-\beta_i,\alpha_i),
\quad \alpha_i^2+\beta_i^2=1.
\]

The canonical slope range `[-1,1]` gives `alpha_i>=|beta_i|>=0`. For a pair
`i,j`, put

\[
c=\alpha_i\alpha_j+\beta_i\beta_j,\qquad
s=\alpha_i\beta_j-\beta_i\alpha_j.
\]

Then `c^2+s^2=1` and `c>=0`: even when the beta signs oppose,
`alpha_i alpha_j >= |beta_i beta_j|`. This includes the endpoint `c=0`.

For any of the four unit directions `u_i,v_i,u_j,v_j`, the owner square has
support halfwidth `1/2`. The other square has support halfwidth
`(|c|+|s|)/2=(c+|s|)/2`. For example,
`u_i.u_j=c`, `u_i.v_j=-s`, `v_i.u_j=s`, and `v_i.v_j=c`.
Swapping owners transposes this dot-product table and negates `s`; it does
not change the sum of absolute values. Negating a direction also preserves
both halfwidths because the squares are centrally symmetric.

Consequently every one of the eight signed, owned SAT possibilities has
the same threshold

\[
h=\frac{1+c+|s|}{2}.
\]

Disjoint open square interiors imply at least one such closed separating
inequality `n.(center_j-center_i)>=h`. Cauchy--Schwarz with `||n||=1` gives

\[
\boxed{\ \|center_j-center_i\|\geq h\ }.
\]

Both contact and all orientation endpoints are retained. No positive pair
separation margin is assumed.

## 2. Folded original frames give a second valid threshold

Put `a_i=|beta_i|` and define

\[
c_f=\alpha_i\alpha_j+a_i a_j,\qquad
s_f=\alpha_i a_j-a_i\alpha_j.
\]

The same folded variables satisfy `c_f^2+s_f^2=1`. Moreover,

\[
c+|s|\geq c_f+|s_f|.
\]

When the original beta signs agree, this is equality. When they oppose,
set `X=alpha_i a_j`, `Y=a_i alpha_j`, and `Z=a_i a_j`. Subtracting the
right side from the left gives

\[
X+Y-2Z-|X-Y|=2(\min(X,Y)-Z)\geq0,
\]

because each alpha is at least its own absolute beta. This proof also covers
zero betas. Therefore the same physical pair satisfies the weaker but useful
folded threshold `(1+c_f+|s_f|)/2`. It requires no chirality guard. It couples
the original absolute-beta variables even when a convex relaxation permits
the signed beta to have an inconsistent smaller magnitude.

## 3. Exact polynomial and affine consequences

Let `(C,S)` denote either `(c,s)` or `(c_f,s_f)`. For any rational `tau>=0`,
the square identity `(h-tau)^2>=0` and `||d||>=h` give

\[
\boxed{\ \|d\|^2\geq \tau(1+C+\varepsilon S)-\tau^2
\quad(\varepsilon\in\{-1,1\})\ }.
\]

For the folded case, use its own smaller threshold in this identity. The
restriction `tau>=0` ensures `|S|>=epsilon*S` is used in the correct direction.
At `tau=1` the row is simply `||d||^2>=C+epsilon*S`. The deterministic
discovery family uses `tau` in `{1,9/8,6/5}`; every member is independently valid.

Suppose a physical pair's coordinate differences have already proved
intervals `l_k<=d_k<=u_k`. Then

\[
d_k^2\leq(l_k+u_k)d_k-l_k u_k.
\]

For each bilinear frame product `xy` in `C+epsilon*S`, use either exact
McCormick lower plane

\[
x_Ly+y_Lx-x_Ly_L,\qquad x_Uy+y_Ux-x_Uy_U.
\]

For `-xy`, negate either upper plane, giving

\[
-x_Uy-y_Lx+x_Uy_L,\qquad -x_Ly-y_Ux+x_Ly_U.
\]

Each plane follows directly from a product of two nonnegative interval
distances. Thus any combination of the four lower planes sums to an affine
function `L(z)+K <= C+epsilon*S`. With
`P=sum(l_k*u_k)` and `T(d)=sum((l_k+u_k)*d_k)`, the exact necessary linear row is

\[
\boxed{\ \tau L(z)-T(d)\leq \tau^2-\tau-\tau K-P\ }.
\]

The coefficient variables are the same original centers and frames. There
are no auxiliary products, replacements of frames, or choices of separator.
All 16 combinations of four two-plane products may be retained. Signed and
folded versions are both valid and may coexist.

The source `owner_free_relative_support.py` generates these rows using only
exact `Fraction` arithmetic. Its optional difference intervals must themselves
be proved from the same original caller; the default uses interval subtraction
of proved original-center bounds.

## 4. Exact interval radius and complete octagon scaling

Let original slope intervals be `T=[t_L,t_U]` and `U=[u_L,u_U]`. If they
overlap, the universal exact bound is `h>=1`. Otherwise the angular difference
has fixed sign. On the interval `[0,pi/2]`, `cos(v)+sin(v)` is concave, so its
minimum over a closed interval occurs at an endpoint. The two endpoint values
are obtained from `(t,u)=(t_L,u_U)` and `(t_U,u_L)`:

\[
\cos(\theta_j-\theta_i)+|\sin(\theta_j-\theta_i)|
=\frac{1+tu+|t-u|}{\sqrt{(1+t^2)(1+u^2)}}.
\]

Replace each denominator by an exact rational upper enclosure of its positive
square root. Half of one plus the smaller resulting value, also bounded below
by one, is a proved rational radius `r<=h`. The source computes those root
enclosures by integer square root with 48 binary fractional bits. No decimal
angle or numerical trigonometric evaluation is trusted.

The physical pair therefore satisfies `||d||>=r`. Scaling the already proved
eight-case rational octagon cover gives closed alternatives

\[
\pm d_x\geq\frac{12r}{13},\quad
\pm d_y\geq\frac{12r}{13},\quad
\pm d_x\pm d_y\geq\frac{17r}{13}.
\]

Exactly one of the eight signed expressions is required in each child; they
must not all be conjoined. All eight children together cover the whole parent,
including every equality face. Rational rotations and ordered closed
predecessor complements remain valid by the same argument as the radius-one
octagon. The radius is computed from inherited physical angle intervals,
not from a proposed LP point.

## Acceptance limit

These constraints are necessary physical consequences. A feasible relaxation
still need not describe a packing, and a violated saved LP point alone does
not close a cell. A new whole-parent closure would require an independently
checked exact weighted contradiction and complete original-parent coverage.
