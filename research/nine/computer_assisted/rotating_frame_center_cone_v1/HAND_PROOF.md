# Original-square center support in its physical frame

This is a universal necessary row at squared circle radius `Q = 1105/256` for each of the nine original unit squares. It requires no SAT witness, marked edge, endpoint sign, or extra square. It is valid on every closed face retained by the search. Numerical search proposes parameters; the independent checker verifies each printed row against its reconstructed physical interval state.

## Physical implication

Let `u=(alpha,beta)`, `v=(-beta,alpha)` be the actual orthonormal square frame and `p=(x,y)` its original center. Put `a=p dot u`, `b=p dot v`, `s=abs(a)`, `t=abs(b)`. The four original corner inequalities give

`s^2+t^2+s+t <= Q-1/2 = 977/256`.

For the rational parameter `r=91/60`, the identity

`s^2+t^2+s+t - ((2*r+1)*s+t-r^2) = (s-r)^2+t^2 >= 0`

gives `s+k*t <= cap`, and exchanging `s,t` gives `t+k*s <= cap`, where

- `k = 30/121`;
- `cap = 352321/232320`.

Here `r` is merely a chosen rational tangent parameter. No premise that the center has norm at most `r` is used.

Fix a nonzero rational world direction `n=(nx,ny)`. Suppose an interval guard proves, for one sign `sigma in {-1,1}`,

`m = sigma*(n dot u) > 0` and `abs(n dot v) <= k*m`.

Then

`n dot p <= abs(n dot u)*s + abs(n dot v)*t <= m*(s+k*t) <= cap*m`.

Thus the following necessary row is linear in the original variables:

`nx*x + ny*y - cap*sigma*nx*alpha - cap*sigma*ny*beta <= 0`.

The `v`-major version is obtained by exchanging `u,v` in the argument and uses `m=sigma*(n dot v)`. Both versions are implemented.

## Exact interval guard

Canonical square frames have `alpha>0`; their certified slope is `z=beta/alpha` in `[L,U]`. In the `u`-major case, the guard after division by `alpha` is

`sigma*(nx+ny*z)>0` and `abs(ny-nx*z) <= (30/121)*sigma*(nx+ny*z)`.

The absolute-value condition is two affine inequalities. Checking them, and positivity of the affine major component, at both rational endpoints proves the guard throughout the full closed interval. The `v`-major case uses `sigma*(ny-nx*z)` for the major component and `nx+ny*z` for the minor component. No interval is split or removed to introduce a row.

## Implementation and certificate scope

`physical_center_cone_rows.py` generates rows. `independent_center_cone_rows.py` reconstructs them separately from exact rational data. `verify_packet.py` checks both frame axes, both signs, tilted directions, equality at the closed guard endpoints, damaged literals, failed interval guards, and an exact weighted excerpt from an actual Cb882 bound record.

The row family is universally necessary for each original square at Q. The weighted excerpt verifies exact dual arithmetic conditional on its other printed, previously accepted rows. It does not by itself verify the provenance of those older row families or the original-cell ancestry. The complete bound record and its independent local replay result are included for integration with the existing original-cell verifier. No original-cell or mask closure is claimed by this packet.
