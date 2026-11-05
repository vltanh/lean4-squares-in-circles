# Shared original-frame identities and directional support bounds

> Retained mathematical source. Reproduction commands, checker reports and implementation notes below refer to the [archived version](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/ORIGINAL_FRAME_PERSPECTIVE_AND_DIRECTIONAL_SUPPORT_HAND_PROOF.md); the current task is the [pen-and-paper roadmap](../PROOF_PLAN.md).

These are universal necessary consequences for independently oriented physical unit squares. They introduce no partition, orientation agreement, extra separator, or containment-radius hypothesis. Applying them closes no original parent unless that parent's complete exact contradiction is supplied.

## 1. Exact perspective of one original inset

Represent the same original square by `alpha>0`, `z=|beta|`, `0<=z<=alpha`, and `alpha^2+z^2=1`. Its aligned inset halfwidth is `g=1/(2(alpha+z))`. Put `t=z/alpha` in `[0,1]`. Then

    2g/alpha = r(t) = (1+t^2)/(1+t) = t-1+2/(1+t).

The unit-frame equation is essential to this identity. For any rational `a>=0`, direct subtraction gives

    r(t)-r(a)-r'(a)(t-a) = 2(t-a)^2/((1+a)^2(1+t)) >= 0,
    r'(a)=1-2/(1+a)^2.

Writing `p=r(a)-a*r'(a)` and `q=r'(a)` and multiplying by the positive original alpha gives the rational linear necessary row

    p*alpha + q*z <= 2g.

For proved original slope bounds `0<=m<=t<=M<=1`, let `L` be the chord of `r` at `m,M`. If `m<M`,

    L(t)-r(t) = 2(t-m)(M-t)/((1+m)(1+M)(1+t)) >= 0.

Thus `2g<=alpha*L(z/alpha)`, another rational linear row in the same original alpha, z and g. The degenerate `m=M` case is equality. In particular, the full `[0,1]` chord gives the simple universal inequality

    2g <= alpha.

Equivalently its reserve is `alpha-2g=z(alpha-z)/(alpha+z)>=0`; both aligned and diagonal endpoint frames retain equality. A proved scalar box `alpha in[al,au]`, `z in[zl,zu]` yields `t>=zl/au` and `t<=zu/al`, so these bounds may sharpen the inherited folded original slope interval before constructing the chord. No signed-beta branch is needed.

The companion generator also adds two elementary convex-hull consequences already implied by the same original geometry. First, for proved `s=alpha+z in[sl,su]`, convexity of `1/(2s)` gives

    alpha+z + 2*sl*su*g <= sl+su,
    g >= 1/a - (alpha+z)/(2a^2)       (a>0).

Second, `alpha=sqrt(1-z^2)` is concave on `[0,1]`, so every chord joining lower rational endpoint enclosures of this function lies below the full original folded arc. Integer square root supplies the outward rational enclosures. The bound `s<=99/70` is justified by `99^2=9801>2*70^2=9800`; it is an upper enclosure, not an exact square root.

## 2. Directional support variation controls physical pair distance

Let two original centered unit squares have independent side frames and relative orientation delta. Choose quarter-turn-equivalent frames so `c=cos(delta)>=0`, and put `s=sin(delta)`. Then `c^2+s^2=1`. Define

    rho=(c+|s|-1)/2 >= 0.

In the first original's frame, every vertex of the second has coordinate magnitudes `(c+|s|)/2` and `|c-|s||/2` in one order. The smaller coordinate is at most `1/2`; the larger exceeds `1/2` by exactly rho. Its distance to the first centered unit square is therefore rho. Because a square plus a closed disk is convex, containment of all four vertices gives

    S_j subset S_i + B_rho.

The same argument with the originals interchanged gives the reverse inclusion. Consequently their support halfwidths in **every** unit direction n satisfy

    |h_i(n)-h_j(n)| <= rho.

The physical separating-axis theorem for two original unit squares gives a separating axis belonging to one of the originals. Every such signed axis has the same sum of support halfwidths

    (1+c+|s|)/2 = 1+rho.

Cauchy--Schwarz then gives `|c_j-c_i|>=1+rho`, and hence the universal inequality

    |c_j-c_i| >= 1+|h_i(n)-h_j(n)|.

Both arbitrary tilt signs and all physical contact faces are included. Choosing the coordinate direction recovers the simpler `1+|h_i-h_j|` bound; allowing other common directions preserves information about opposite tilt signs that is lost when original frames are folded separately.

## 3. Exact affine consequences without frame products

For a fixed rational unit direction `n=(p,q)`, the original support is

    h_i(n)=(|p*alpha_i+q*beta_i|+|q*alpha_i-p*beta_i|)/2.

Each of the four choices of two signs gives an affine lower bound. Proved scalar intervals give affine upper bounds by the exact chord of the absolute-value function; if its argument has fixed sign, this chord is the function itself. Denote one such lower and upper bound by `l_i` and `u_j`. Then

    w=h_i(n)-h_j(n) >= l_i-u_j.

For every rational `k>=-1`, the physical pair inequality implies

    |d|^2 >= 1+2|w|+w^2
            >=1+2(1+k)w-k^2
            >=1+2(1+k)(l_i-u_j)-k^2.

The second step uses `|w|>=w` and `(w-k)^2>=0`; the last uses the nonnegative multiplier `2(1+k)`. Both ordered choices of the two originals are valid.

For proved displacement intervals `dx in[a,b]`, `dy in[c,e]`, use

    |d|^2 <= (a+b)dx+(c+e)dy-ab-ce.

If `l_i=L_i` is a homogeneous signed-corner linear form and `u_j=U_j+C_j`, the resulting standard `left<=right` row is

    2(1+k)(L_i-U_j) - (a+b)dx - (c+e)dy
      <= k^2-1-ab-ce+2(1+k)C_j.

This is exactly the formula in `directional_support_rows.py`. It uses the same original center and signed-frame variables and no auxiliary frame product. The fixed rational directions only select valid necessary inequalities; they are not a geometric case partition. Corners whose maximum over the proved box is at most one half are omitted as an efficiency choice; every emitted row remains individually valid.

## 4. Acceptance scope

`frame_perspective_rows.py` and `directional_support_rows.py` are exact Fraction row generators. Their prerequisites are already proved original parent intervals. Numerical use of these rows, feasible relaxations, or incomplete bound induction does not establish a cell or mask closure. A claimed full parent must retain all original conditions and supply independent exact row reconstruction, rational sums, acyclic simultaneous bound updates, and an actual terminal contradiction. No Lean, Lake or CI is used here.
