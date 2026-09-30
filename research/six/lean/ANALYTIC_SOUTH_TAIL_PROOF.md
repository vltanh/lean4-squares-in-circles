# The final south upper tail: an analytical proof

This companion proves the last independent reduction bound, `s < 11/25`,
when the south square is canonically OWN. It uses the actual candidate W/D
and D/S separators, already obtained by the analytical missing-wing exclusions.
No finite classification, interval subdivision, sampled minimum, or external
program result is a mathematical premise.

The corresponding Lean declarations are in
`SquaresInCircles/Six/Analytic/SouthOuterTail/`. Their compilation and kernel
acceptance have not been executed in this continuation. Rational cross-checks
of the displayed algebra are development checks, not additional hypotheses.

## 1. Constants and actual geometric input

Write

```
Q0 = 142559/50000,
R0 = sqrt(Q0),
rho0 = sqrt(Q0-1/4)-1/2,
c0 = rho0-1.

Rbar = 8443/5000,
rhobar = 55641/50000,
cbar = 5641/50000,
A = 1/2-cbar = 19359/50000,
B = 1/2+cbar = 30641/50000.
```

Squaring positive quantities proves `R0 <= Rbar`, `rho0 <= rhobar` and
`c0 <= cbar`. The central center `(cx,cy)` satisfies
`0 <= cx,cy <= c0`.

In the unchanged normalized frame let

```
v = -w,       s = the south helper angle,       d = the diagonal angle,
q = d+v,     r = d-s,
T(t) = 1/2+(|cos t|+|sin t|)/2.
```

The exterior squares have signed local center coordinates
`(aw,bw)`, `(aS,bS)`, `(aD,bD)`. Each satisfies

```
(a+1/2)^2+(|b|+1/2)^2 <= Q0,    a >= 1/2.
```

The earlier high-diagonal argument also gives

```
aD <= rho0 < 1113/1000,    |bD| < 23/100.
```

Suppose, for a contradiction, that the OWN south angle has `s >= 11/25`.
Normalization and the analytical west-tail theorem then give the domains

```
11/25 <= s <= 2/3,        1/2 <= d <= 11/14;
OWN W:       0 <= v <= 11/25;
cardinal W: -2/5 <= v <= 2/5.
```

The rational upper endpoint `11/14` only enlarges `d <= pi/4`. The west-tail
input is not circular: it was proved from the candidate D edges and the older
shared-center wing budget, before invoking this south-tail theorem.

The four genuine separating inequalities are

```
CW, OWN W:     T(v) <= aw + cx cos v - cy sin v;
CW, cardinal:  T(v) <= aw cos v + bw sin v + cx;
CS, OWN S:     T(s) <= aS - cx sin s + cy cos s;
WD, W source:  T(q) <= aD sin q + bD cos q - bw;
DS, S source:  T(r) <= bS + aD cos r - bD sin r.
```

Only the appropriate CW line is used in a case. The WD and DS lines come
from the analytical candidate-edge theorem, not from a chosen source index
or an assumed equality case.

## 2. Elementary support bounds

The far-corner disk and Cauchy--Schwarz give, for any real `U,V`,

```
U a+V b <= R0 sqrt(U^2+V^2)-(|U|+|V|)/2.
```

Replacing the absolute values by `U,V` gives a weaker bound valid without
any sign assumption. A second consequence of the same disk is

```
a+(31/100)(|b|+b^2) <= rho0.                         (2.1)
```

Indeed, subtract the far-corner inequality from
`rho0^2+rho0+1/2=Q0` to obtain

```
|b|+b^2 <= (rho0-a)(rho0+a+1).
```

Here `a <= rho0`, and `(31/100)(rho0+a+1) <= 1`, so (2.1) follows.
All these statements concern the actual signed center; no cap-support branch
is assumed.

Set `mu=2/5` and `nu=3/10`. The two diagonal edges have resultant

```
U = mu sin q + nu cos r,
V = mu cos q - nu sin r,
U^2+V^2 = 1/4+(6/25)sin(v+s).
```

For `-1 <= z <= 1`,

```
sqrt(1/4+(6/25)z) <= 61/120+z/5,                    (2.2)
```

because the right side is positive and its squared excess is exactly
`(z/5-11/120)^2`. The south resultant `(1,nu)` has length at most
`Sbar=1044031/1000000`, again by squaring.

For the center work, keep the two forces together. If its y force is
nonnegative, its maximum over the central box has `cy=cbar`; its x force
selects one of `X=0,cbar`. Proving both x-face estimates therefore bounds
the actual center work. This is a linear-support argument, not an extra
packing assumption.

## 3. Cardinal W: one polynomial root and two sign intervals

Use weights

```
CW: 3/5,    CS: 1,    WD: 2/5,    DS: 3/10.
```

Write `v=sigma*x`, where `sigma` is `+1` or `-1` and `0 <= x <= 2/5`.
The west resultant is

```
((3/5)cos v, (3/5)sin v-2/5),
```

whose squared length is `13/25-(12/25)sin v`.

### A root bound on the entire argument interval

Let

```
a0=18/25,  e(t)=1/625-(12/25)t,
P(t)=a0+e(t)/(2a0)-e(t)^2/(8a0^3)+e(t)^3/(16a0^5).
```

For `|t| <= 2/5`, `|e(t)| <= 1/5`, `P(t) >= 1/2`, and direct expansion gives

```
P(t)^2-(13/25-(12/25)t)
 = e(t)^4*((e(t)-2a0^2)^2+16a0^4)/(256a0^10) >= 0.
```

Thus this single polynomial majorizes the root on the whole interval. Its
explicit derivatives also satisfy

```
-21/50 <= P'(t) <= 0,       P''(t) >= -1/4.
```

These follow by substituting `|e|<=1/5` into the displayed polynomial
expressions; in particular P is decreasing. The proof does not appeal to a
numerically fitted root curve.

### The scalar lower bound

The central work is `(3/5-sin s)cx+cos s*cy`. Since `cos s>=7/9`, its y
force is positive. Apply the face argument and the three disk supports.
The weighted threshold minus the support upper bounds is at least

```
H(sigma,X,x,s,d) = 2-(3/5)X-Rbar*(Sbar+61/120)
 + (3/5)cos x + [sigma=-1]*(3/5)sin x
 - Rbar*P(sigma*sin x)
 + A cos s + (1/2+X)sin s
 + mu*(cos(d+sigma*x)+sin(d+sigma*x))
 + nu*cos(d-s) - (Rbar/5)*sin(sigma*x+s).             (3.1)
```

Here `[sigma=-1]` is 1 on the negative sign case and 0 otherwise. It arises
from the exact absolute value in the CW width; the sign is not discarded.
Every actual packing would require (3.1) to be nonpositive for its selected
central face.

### Whole-interval concavity

For fixed other coordinates the d and s slices of H are a constant plus a
positive linear combination of sine and cosine. For example the d coefficients
are

```
mu*(cos x+sigma sin x)+nu cos s,
mu*(cos x-sigma sin x)+nu sin s,
```

which are nonnegative throughout the rectangle. The analogous s coefficients
are also nonnegative using `cos x>=9/10`, `sin x<=11/25`, `cos d>=69/100`
and `sin d>=23/48`.

The x slice has the form

```
K+alpha cos x+beta sin x-Rbar P(sigma sin x),
alpha >= 21/25;
beta >= -7/20 when sigma=+1, and beta >= 0 when sigma=-1.
```

Its second derivative is

```
-alpha cos x-beta sin x
 +Rbar*(P'(sigma sin x)*sigma sin x-P''(sigma sin x)*cos^2 x).
```

Use `cos x>=23/25`, `0<=sin x<=2/5`, and the derivative bounds for P.
For sigma=+1 an upper bound is

```
-(21/25)(23/25)+(7/20)(2/5)+Rbar/4 < 0;
```

for sigma=-1 an upper bound is

```
-(21/25)(23/25)+Rbar*((21/50)(2/5)+1/4) < 0.
```

Thus all three coordinate reductions are justified on their entire intervals.
Only the physical endpoints remain:

```
x in {0,2/5},    s in {11/25,2/3},    d in {1/2,11/14},
sigma in {+1,-1},    X in {0,cbar}.
```

### Exact endpoint comparisons

For nonnegative x use

```
C6(x)=1-x^2/2+x^4/24-x^6/720 <= cos x,
cos x <= C4(x)=1-x^2/2+x^4/24,
S7(x)=x-x^3/6+x^5/120-x^7/5040 <= sin x,
sin x <= S5(x)=x-x^3/6+x^5/120.
```

Use evenness for cosine and oddness for sine when an argument is negative.
For the root term, P is decreasing, so replace its argument by `S7(x)` on
the positive branch and `-S5(x)` on the negative branch. Both arguments stay
inside `[-2/5,2/5]` at the two x endpoints. Substitute lower bounds in positive
terms of (3.1) and upper bounds in negative terms.

Each of the 32 resulting rational expressions exceeds `1/400`. Their smallest
one, at `(sigma,X,x,s,d)=(-1,0,2/5,2/3,1/2)`, is exactly

```
6021891444902537143 / 2152828125000000000000 > 1/400.
```

This is arithmetic at endpoints forced by the preceding concavity proof,
not a tested cover of angle boxes. Consequently H is positive everywhere,
contradicting the four separators in the cardinal-W case.

## 4. OWN W: retain the diagonal center before reducing angles

The original proposal to use the same far-vertex profile for OWN W had a
negative endpoint. It is not used to prove this case. Instead, change only
the CW weight to `b0=5/8`, and keep the actual `(aD,bD)` until the two wing
angles have been reduced.

The west support now uses

```
sqrt((5/8)^2+(2/5)^2) <= Wbar=371021/500000.
K=93/40-Rbar*(Wbar+Sbar).
```

The central y force `cos s-b0 sin v` is positive. For either x face X, the
raw weighted threshold minus the W, S and center support bounds is at least

```
F_X(v,s,d,a,b) = K+b0(1/2-X)cos v+b0 B sin v
 +A cos s+(1/2+X)sin s
 +mu*((1/2-b)cos(d+v)+(1/2-a)sin(d+v))
 +nu*((1/2-a)cos(d-s)+(1/2+b)sin(d-s)).             (4.1)
```

At the actual diagonal center `(a,b)=(aD,bD)`, the four separating
inequalities require (4.1) to be nonpositive.

### Two angle reductions with the same actual center

Throughout `1/2<=a<=1113/1000`, `|b|<=23/100`, the v slice of F has coefficients

```
a_v=b0(1/2-X)+mu*((1/2-b)cos d+(1/2-a)sin d),
b_v=b0 B+mu*(-(1/2-b)sin d+(1/2-a)cos d);
```

the s slice has coefficients

```
a_s=A+nu*((1/2-a)cos d+(1/2+b)sin d),
b_s=1/2+X+nu*((1/2-a)sin d-(1/2+b)cos d).
```

All four are positive. One useful uniform estimate is

```
(73/100)x+(613/1000)y <= 191/200   when x^2+y^2=1.
```

It follows by adding the square of the orthogonal linear combination and
using `(73/100)^2+(613/1000)^2 < (191/200)^2`. In particular

```
b_v >= (5/8)B-(2/5)(191/200) = 81/80000 > 0.
```

The other coefficients follow from the same estimate, `cos d>=69/100`,
and the coordinate bounds. Therefore concavity leaves exactly four wing
corners, with the *same* actual a,b and the full d interval retained:

```
(v,s) = (0,11/25), (0,2/3), (11/25,2/3), (11/25,11/25).
```

### Three corners: ordinary vertex support

At the first three corners, apply the weak far-vertex support to the diagonal
resultant and use (2.2). This gives the lower bound

```
J_X(v,s,d) = K-Rbar*(61/120)
 +b0(1/2-X)cos v+b0 B sin v+A cos s+(1/2+X)sin s
 +mu*(cos(d+v)+sin(d+v))+nu*cos(d-s)
 -(Rbar/5)*sin(v+s).
```

Its d slice is a positive first harmonic, so d reduces to `1/2` or `11/14`.
The same Taylor polynomials give 12 rational expressions, each greater than
`1/500`. Their minimum is

```
29454897611279137 / 12304687500000000000 > 1/500.
```

Thus (4.1) is positive at these three wing corners for every allowable d and
every contained actual diagonal center.

### The exceptional corner: prove its radial-support cone

Let `t=11/25`, so v=s=t. Write

```
U(d)=mu sin(d+t)+nu cos(d-t),
V(d)=mu cos(d+t)-nu sin(d-t).
```

The exact rotation identities are

```
U=alpha cos d+beta2 sin d,    V=beta2 cos d-alpha sin d,
alpha=mu sin t+nu cos t,     beta2=mu cos t+nu sin t.
```

Taylor bounds at t give

```
11/25 <= alpha <= 443/1000,
489/1000 <= beta2 <= 49/100.
```

On the whole diagonal interval,

```
69/100 <= cos d <= 879/1000,
23/48 <= sin d <= 71/100,
cos d+sin d > 4/3.
```

The last inequality follows by concavity and the two Taylor endpoint values.
Substitution into the rotation identities yields

```
3/5 <= U <= 7/10,      0 <= V <= (2/5)U.            (4.2)
```

For example, the lower U bound uses
`U >= (11/25)(cos d+sin d)+(49/1000)sin d > 3/5`.
For the upper V/U bound use

```
(2/5)U-V >= -(157/500)cos d+(1589/2500)sin d > 0.
```

Thus (4.2) is derived, not assumed as a support-branch choice.

### A completed square replaces the overlarge vertex bound

For any contained center and force satisfying (4.2), (2.1) implies

```
Ua+Vb <= rho0 U+(7/100)V^2 <= rho0 U+1/160.         (4.3)
```

To verify the first inequality, put x=|b|, y=|V|. From `U>=3/5` and
`y<=(2/5)U`, the loss in (2.1) controls `(31/40)xy+(93/500)x^2`.
The remaining quadratic is nonnegative by the exact identity

```
(93/500)x^2-(9/40)xy+(7/100)y^2
 = (93/500)(x-(75/124)y)^2+(97/49600)y^2.
```

For the second inequality, `|V|<=7/25`, so `(7/100)V^2<1/160`.
This proves the support estimate throughout the entire d interval.

### The remaining diagonal expression is decreasing

After (4.3), and weakening rho0 to rhobar, the d-dependent part of the
lower bound for (4.1) is

```
G(d)=(mu/2)cos(d+t)-mu B sin(d+t)
     -nu B cos(d-t)+(nu/2)sin(d-t).
```

Its derivative is

```
G'(d)=-mu*(B cos(d+t)+(1/2)sin(d+t))
      +nu*((1/2)cos(d-t)+B sin(d-t)).
```

On `47/50<=d+t<=429/350`, the first bracket exceeds `2/3` by concavity and
two Taylor endpoint inequalities. On `0<=d-t<=121/350`, the second bracket
is at most `1/2+B*(121/350)`. Consequently

```
G'(d) <= -(2/5)(2/3)+(3/10)*(1/2+B*(121/350)) < 0.
```

It suffices to evaluate at `d=11/14`. With the same Taylor bounds, the lower
rational expressions for the two central faces exceed

| Central x face | Lower bound, after the full `1/160` support allowance |
| --- | --- |
| X=0 | 13/500 |
| X=cbar | 1/100 |

Both are positive. This handles the fourth wing corner. Notice the order of
the proof: first reduce v,s while retaining a,b, then use (4.3) only at the
corner where its cone was proved. It would be invalid to apply (4.3) to the
whole original rectangle without proving that cone there.

All four raw corners are positive, hence (4.1) is positive throughout the
OWN-W rectangle. This contradicts the actual four separators.

## 5. Conclusion and formal interfaces

Both choices of the west central separator are impossible when an OWN south
square has `s>=11/25`. Therefore

```
P.ownBits 4=true  ==>  P.helperAngle 4 < 11/25.
```

The source theorem is `SouthOuterTail.normalized_own_south_upper_tail`.
`Analytic.FixedPair.complete_south_outer_bound` weakens it to the non-strict
interface. Together with `candidate_diagonal_separators`,
`reduction_iff_edges_and_south_tail` constructs `complete_reduction` for every
normalized packing. The unrestricted lower-bound and uniqueness modules use
that theorem directly.

### Source map

| Source under `SouthOuterTail/` | Mathematical role |
| --- | --- |
| `Root.lean`, `RootConcavity.lean`, `Profile.lean`, `CardinalEndpoints.lean` | The polynomial-root cardinal proof and its full-interval reductions |
| `NarrowSupport.lean` | The completed-square radial support estimate |
| `OwnRaw.lean` | The two wing reductions with the actual D coordinates retained |
| `OwnDiagonal.lean` | The derived exceptional cone and monotone d expression |
| `OwnEndpoints.lean` | The three ordinary corners and the exceptional radial corner |
| `Support.lean`, `ScalarGeometry.lean` | Disk bounds and the weighted sum of actual separators |
| `Geometry.lean` | The normalized-packing theorem, with all hypotheses derived |

The unused kind-0 scalar profile in `Profile.lean` is not a proof of the OWN
case. The complete argument for that case is the raw-center proof above.
