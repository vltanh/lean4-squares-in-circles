# Original disk-corner rows using the exact unit frame

Fix one retained original with center c=(x,y), unit side u=(alpha,beta),
and positive quarter turn v=(-beta,alpha). For epsilon,tau in {-1,1},
the squared norm of its actual corner c+(epsilon u+tau v)/2 is exactly

```
x²+y²+1/2+alpha r+beta s,
r=epsilon x+tau y,   s=epsilon y-tau x.
```

This uses the original orthogonal unit-frame identities before relaxation.
The original disk predicate therefore implies
`x²+y²+alpha r+beta s <= Q-1/2 = 977/256`.

Let the unchanged caller have already proved closed intervals for
x,y,alpha,beta. Cartesian extrema give proved intervals for r and s.
Select matching lower endpoints (a0,r0) or matching upper endpoints of
the alpha/r rectangle. Then `alpha r >= a0 r+r0 alpha-a0 r0`, because
`(alpha-a0)(r-r0)>=0`. Independently select matching lower or upper
endpoints (b0,s0) of the beta/s rectangle. Negative beta and negative
projections are allowed.

For arbitrary rational px,py, the squared distance gives
`x²+y² >= 2px x+2py y-px²-py²`. Adding the three lower bounds gives

```
(2px+epsilon a0-tau b0)x + (2py+tau a0+epsilon b0)y
+ r0 alpha+s0 beta
<= 977/256+px²+py²+a0 r0+b0 s0.
```

The complete exact residual identity is

```
(x²+y²+alpha r+beta s) - (affine left side - px²-py²-a0 r0-b0 s0)
= (x-px)²+(y-py)²+(alpha-a0)(r-r0)+(beta-b0)(s-s0) >= 0.
```

Only four existing original variables occur. No new product variable,
normal, SAT owner or physical restriction is introduced. Every interval
endpoint and zero-width interval is retained. The independent checker
computes projection extrema from all four Cartesian endpoints and
expands the rectangle and squared-distance terms separately. It imports
no producer. Its intervals must come from the independently reconstructed
caller. A child row cannot be moved to a wider parent without rebuilding
it from intervals already proved for that parent.

Numerical points suggest px,py and plane choices. Every rational choice
is valid, so floating-point feasibility and optimality play no proof role.
All original frames, corners, pairs, cones and exact marked bits remain
in the enclosing all-nine caller. These conditional rows earn zero
original-cell and mask credit without a complete independently checked
original cover.
