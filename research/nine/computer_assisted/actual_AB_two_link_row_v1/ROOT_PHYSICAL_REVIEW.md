# Root acceptance of the actual-AB two-link row theorem

4 November 2026. **Accepted as a conditional physical theorem.** The root
review checked the original-pair cap reduction, both owned axes, the exact
scalar target, the closed polynomial cover and the equality blocker. A
separate physical review and independent fresh scalar replay agree. This
packet adds zero original-cell and zero mask closures.

## Physical lifting

The retained originals are A,B,I,D,E,F,G, with all their independent frames,
original corners and physical pair separations. AB,EF,FG are actual
horizontal projection links. The required geometric guards are

```
theta_D >= 0,  y_G-y_D >= 0,  |x_G-x_D| < 1,
x_B <= x_I <= x_D,
|y_I-y_B|+|y_D-y_I| <= 3/5.
```

The strict horizontal guard and weak vertical sign force every original
D/G separating normal to have positive vertical component: a nonpositive
vertical component would give projection below one, smaller than the
original owned support sum. Rotation by pi reverses this separator while
preserving the canonical orientation of the square modulo pi/2. It gives
the accepted good D cap. The A/E cap is unrestricted and has nonnegative
toll at least `2|beta_A|/23`. The actual EFG chain supplies the remaining
unit of width. Adding the caps yields exactly

```
x_D-x_A-h_A-h_D+T_good(D)+T_universal(A) <= 2,
```

strictly below Q=1105/256. No common-side hypothesis for the entire EFG
row, replacement frame, or new cone comparison is inserted.

For each non-actual row pair D/I and I/B, its horizontal difference d is
nonnegative. Unit center separation and `|v|<=3/5` imply
`d>=4/5>|v|`. Backwards or vertical normals cannot separate because their
projection is below one. Both forward owned axes have projection at most
`alpha_owner*d+|beta_owner|*|v|`; the steep-axis estimate follows from
`(alpha_owner-|beta_owner|)*(d-|v|)>=0`. Thus the original pair obeys

```
d >= (1+cos(delta)+|sin(delta)|)/(2 alpha_owner)
        - |tan(theta_owner)| |v|.
```

All four owner patterns remain covered. AB contributes its actual
halfwidth sum directly and has no vertical-error term.

## Scalar target and exact finite proof

Number D,I,B by 0,1,2. I checked that the scalar quantity to bound is

```
C = R01/alpha_owner0 + R12/alpha_owner1 + h2-h0+T_good(0)-2.
```

The certificate proves `C >= (601/1000)|tan(theta_k)|` for every distinct
selected owner k, strictly unless all three original frames align. In
half-angle coordinates the good-endpoint expression has numerator
`-368+529x0-1536x0^2` over `736(1+x0^2)`. The independent checker derives
the relative cosine from original frame dot products and the relative
sine from determinants. Multiplication by
`736000 product(1-x_i^4)` is strictly positive on the enlarged rational
box `[0,5/12]^3`. The slope penalty and both denominator cancellations
have the claimed coefficients.

The two integer witness weights in [-8,8] minorize the two absolute sine
polynomials. The rational degree-four Bernstein transformation is checked
independently of the discovery transformation. All 28 sign/owner domains
have a complete binary cover, with both closed children at every split.
The fresh root replay checks **103 leaves and 12,875 coefficients**, with
no frontier. On an origin leaf only its origin coefficient is zero;
every other coefficient is positive. This proves strictness at every
nonzero point, including all closed faces and tilted unselected frames.

Writing M for the largest selected-owner absolute slope, the physical
row lower bound is at least
`2+(601/1000-3/5)M+T_universal(A)`, plus the scalar strict surplus away
from the origin. It contradicts the strict cap below Q. At equality the
scalar strictness aligns D,I,B, and the universal toll aligns A. The two
aligned non-actual pairs must separate horizontally since their vertical
gaps are below one. AB is actual, so the span is exactly three.

## Closed-Q application and guard scope

The unchanged original-nine 001/00 caller retains original C and H,
actual AB and BC, the CD center cone, and strictly weak CD. At equality
the original inset separation gives

```
3 >= h_A+2h_B+h_C+g_C+g_D = 1+2h_B+h_C+g_C >= 3.
```

Using `h+1/(4h)-1=(2h-1)^2/(4h)` forces C aligned and the CD horizontal
gap equal to `h_C+h_D`, contradicting its strict weak bit. This is the
necessary closed-Q blocker for this original labeling.

The exact guard and its independent reconstruction have passed a fresh
root replay of ten boundary/damage controls and five hundred closed-cover
identities. The reduced five-domain complement is valid only after the
parent proves the D/G guards and I strictly left of D. It consists of
`x_I-x_B<=0` and the four signed height expressions at least 3/5.
The identity `|u|+|v|=max(u+v,u-v,-u+v,-u-v)` proves exhaustiveness;
all equalities are deliberately retained in overlapping closed domains.

The supplied D821 declaration is a source-bound research attachment, not
a whole-original proof. Every quantitative bound needs complete original
ancestry, and all five complementary domains must be closed before that
parent can earn credit. Other relabelings require their own physical
caller, sign and equality attachments. The current fixed ledgers remain
unchanged by this conditional theorem. No Lean, Lake or CI was run.
