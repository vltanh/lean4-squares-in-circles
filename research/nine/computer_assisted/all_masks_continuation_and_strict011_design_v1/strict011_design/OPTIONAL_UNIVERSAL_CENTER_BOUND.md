# Optional universal center box for a later root revision

This derivation is separate from the frozen prepared root, which still uses
[-2,2]. No code, row or state has been changed by this note. The bound uses
one physical unit square and closed disk containment only; it has no mask,
chain, endpoint-angle, large-gap or label-order premise.

Let c be its center, let u,v be an orthonormal side frame and set
r = norm(c). The four corners are c + (epsilon u + tau v)/2. Expanding
their squared norms and maximizing independently over epsilon,tau gives

    max corner_norm_squared
      = r^2 + 1/2 + abs(c dot u) + abs(c dot v).

Orthonormality gives (c dot u)^2 + (c dot v)^2 = r^2. Consequently
abs(c dot u)+abs(c dot v) >= r: square both nonnegative sides and use
the nonnegative cross term. Containment therefore implies

    r^2 + r + 1/2 <= Q = 1105/256.

At rho = 91/60, exact rational arithmetic gives

    rho^2 + rho + 1/2 - Q = 31/57600 > 0.

The polynomial r^2+r+1/2 increases on r >= 0. Hence r < rho, even
under closed-Q containment. In particular every original x and y lies
in the closed interval [-91/60,91/60]. This holds separately for all nine
original squares in every mask. A later independently checked root may
use those enclosures and their implied difference/product bounds, after
binding this derivation and its exact arithmetic; it may not inherit the
other location bounds of the old 001 geometry stack.
