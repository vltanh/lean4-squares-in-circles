# Global nine-original central-capacity rows

## Scope and source

Let nine actual unit squares have pairwise disjoint open interiors and all
corners in the closed disk of squared radius `1105/256`, with the same origin
as the A2 contract. Their centers and their independent actual own frames are
`c_i`, `u_i`, `v_i`. No chain, mask, contact, root, load, or orientation-sign
assumption is required.

The source is the complete geometric arc theorem in
`SMALLER_CENTRAL_DISKS_NINE_UNIT_CAPACITY.md`, Sections 1–4,
and its independently accepted review
`research/nine/reviews/2026-10-27/REVIEW_SMALLER_CENTRAL_DISKS_AND_C5_S124_DOMAIN_TRIANGLE_BRIDGES_2026_10_27.md`.
I reread the entire proof, including the weak-clearance endpoint where an
interior-circle arc is punctured at one tangent point. The theorem concerns
angular measure, so that endpoint changes no capacity calculation.

Put `h=23/100`, `r=1/2-h=27/100`, and `rho=123/100`.
The source proves that any actual square with distance from the origin at
least `h` occupies strictly more than `pi/4` angular measure of the circle
of radius `rho` through its open interior.

## Two unconditional consequences using all nine originals

1. **At least two distinct originals meet the open disk of radius h.**
   Otherwise eight actual squares have clearance at least h. Their eight
   disjoint open-interior circle subsets would have total angular measure
   strictly greater than `8(pi/4)=2pi`.
2. **Every original satisfies**
   `max(|c_i·u_i|,|c_i·v_i|)>r`.
   If both own projections were at most r in absolute value, that square
   would contain the closed disk of radius h. Its eight companions would
   then have clearance at least h, giving the same contradiction.

Both conclusions include closed containing-circle equality and all contacts.
In particular every center satisfies `||c_i||>r`. These are valid across
all 32 masks, with all nine original labels retained.

## Unconditional radial rows

For the already certified coordinate box
`x_i in [a,b]`, `y_i in [c,d]`, square secants give

`x_i^2+y_i^2 <= (a+b)x_i+(c+d)y_i-ab-cd`.

The strict center exclusion therefore implies the weak necessary row

`-(a+b)x_i-(c+d)y_i <= -r^2-ab-cd`.

There is a stronger exact one-axis inference. If

`delta = r^2-max(a^2,b^2)>0`,

then `y_i^2>delta`. If the certified lower y bound is nonnegative or its
square is strictly less than delta, the negative component is impossible,
so `y_i>sqrt(delta)`. The code installs any exact rational square-root lower
bound as a weak lower bound. The symmetric upper case and x/y interchange
are identical. No coordinate interval is split.

## Forced own-axis escape rows

Use the existing original variables

`u_i=(alpha_i,beta_i)`, `v_i=(-beta_i,alpha_i)`.

The complete disjunction is

- `alpha_i*x_i+beta_i*y_i>r`,
- `-alpha_i*x_i-beta_i*y_i>r`,
- `alpha_i*y_i-beta_i*x_i>r`,
- `-alpha_i*y_i+beta_i*x_i>r`.

An alternative whose exact product-interval upper bound is at most r is
impossible. All remaining alternatives must be retained. Only when exactly
one remains may its rows be installed unconditionally on the original
parent. If none remains, the original parent is contradictory by the global
nine-square theorem.

For a product `a*b` on `[aL,aU] times [bL,bU]`, its two upper affine planes are

`aU*b+bL*a-aU*bL`, and `aL*b+bU*a-aL*bU`.

The two upper planes for `-a*b` are the negatives of its lower McCormick
planes. Add either upper plane for each of the two signed products in a
remaining expression. If the expression is `>r`, each of the resulting four
upper affine expressions must also be `>r`. Weakening to `>=r` gives four
rational linear rows. Both products always use the same original frame.

This avoids replacing an original unit by independently rotating pieces.
It also avoids selecting a favorable disjunct from a relaxed point.

### Concrete existing A-parent guard

Using the current certified-state output
`a_family/continued/positive-2d5aba857f2f7602.json`, original F has only the
positive-v escape alternative remaining. The exact excluded-case upper
bounds are printed in `generator_screen.json`. In particular:

- positive-u upper is `279357095867/1099511627776 < 27/100`;
- negative-u upper is `9171958861624140645/147573952589676412928 < 27/100`;
- negative-v upper is `18151986923/549755813888 < 27/100`.

Thus all four positive-v affine rows are unconditional on this whole
unchanged parent. This is a statement conditional on independently replaying
that inherited state, not a new cell closure. The simpler radial inference
already gives `y_F >= 65835579004991/281474976710656` (about 0.233895).

## Near-original support rows and complete pair cover

If original i meets the open h disk, then for every unit direction e,

`|e·c_i| < h + (|e·u_i|+|e·v_i|)/2`.

Proof: choose an actual point `p=c_i+s*u_i+t*v_i`, with `|s|,|t|<=1/2`,
and `||p||<h`. Project this identity and apply the triangle inequality.

For coordinate directions this yields the exact same-frame weak rows

`+/-x_i-(alpha_i+absbeta_i)/2 <= h`,

`+/-y_i-(alpha_i+absbeta_i)/2 <= h`.

For other fixed rational unit directions `(p,q)`, the exact support is

`(|p*alpha_i+q*beta_i|+|q*alpha_i-p*beta_i|)/2`.

On each certified affine-expression interval, absolute value is bounded
above by its convex chord. Substitution yields further rational necessary
rows. The code uses both coordinate directions and fixed Pythagorean
rational directions; no directional grid completeness claim is needed,
because every individual row is globally valid under the near condition.

Also, a near-original center has

`||c_i|| < h+1/sqrt(2)`.

Since `sqrt(2)<99/70`, its squared norm is strictly below the rational number

`U = 1/2+h^2+(99/70)*h`.

If a current center box has minimum squared norm at least U, that original
cannot be near. Remove only these rigorously excluded labels. Every
unordered pair among the remaining labels forms one necessary branch of a
complete finite cover, since at least two originals are near. Each branch
contains both originals' support rows. The branch conditions are necessary,
so the union may be larger than the physical set; that is safe.

If exactly two labels remain, their near rows are unconditional. If fewer
than two labels remain, the whole parent is contradictory. Otherwise the
module emits the complete pair list separately, for exact support maxima
or complete unions. It does not silently install any chosen pair.

## Interface and acceptance

`central_nine_rows.py` is standard-library-only and uses exact `Fraction`
arithmetic and exact integer-square-root lower bounds.

- `generate_rows(positions, scalar) -> (rows, guards)` emits only rows valid
  on the entire current original parent.
- `own_escape_cases(i, positions, scalar)` returns every remaining own-axis
  alternative and exact exclusions. Each retained alternative has four
  necessary affine rows.
- `central_pair_cases(positions, scalar)` returns every remaining unordered
  near-original pair and exact radial exclusions.
- `near_support_rows(i, scalar)` is conditional on original i being near;
  do not install it globally unless that premise has been established.

The existing 54-variable indexing is preserved: centers 0–17, alpha 18–26,
beta 27–35, absolute beta 36–44, inset half-side 45–53.

No cell or mask is marked closed by this note. A closure still needs exact
full-prefix arithmetic, full-domain physical row reconstruction, and a
terminal contradiction or complete original-center cover under the fixed
231-cell contract. No Lean, Lake, CI, or solver result is a premise.
