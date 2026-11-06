# Crossed signs cannot complete to nine in the two-direction equality class

November 1, 2026. Hand derivation, no scripts/Lean/CI. This is an addendum
to [TWO_DIRECTION_SEPARABLE_NINE_HAND_PROOF_2026_11_01.md](TWO_DIRECTION_SEPARABLE_NINE_HAND_PROOF_2026_11_01.md).

## Statement

In the equality normal form of that theorem, the signs must agree:
`sigma_L=sigma_R`. Up to vertical reflection they are both positive.

It suffices to exclude `sigma_L=+1,sigma_R=-1`, since reflection in the
horizontal coordinate exchanges the other crossed choice with this one.
The seven aligned anchor centers then are

    M_L=(-3/2,1/16), M_2=(-1/2,alpha),
    M_3=(1/2,beta), M_R=(3/2,-1/16),
    B_L=(-1,-15/16), B_2=(0,gamma), B_R=(1,15/16).

Containment and the anchor pair inequalities imply

    1/16<=alpha<=U_M<4/3,
    -4/3<-U_M<=beta<=-1/16,
    |gamma-alpha|>=1, |gamma-beta|>=1,

where `U_M=sqrt(849)/16-1/2`. The first two inequalities follow because
the opposite alternatives `alpha<=-31/16` and `beta>=31/16` exceed the
containment range. We retain `|c|<rho=61/40` for every center. The exact
comparison `U_M<4/3` follows from `849<(88/3)^2`.

Every pair is separated along the horizontal or vertical axis, by the
equality theorem's forced perpendicular cover.

## 1. A corner obstruction used repeatedly

If a unit square has coordinate halfwidth `h` and center `(X,Y)` satisfying

    -X >= h+1/2,   Y >= h+9/16,

then its containing disk has

    q >= (3/2)^2+(25/16)^2 = 1201/256 > Q.

Indeed choose `P=(-3/2,25/16)`. The center inequalities give

    P.c >= 3/4+225/256+(49/16)h.

The square-orientation inequality

    (A+p)h+H_S((+/-A,+/-p)) >= A+p,  0<=p<=A,

with `(A,p)=(25/16,3/2)`, gives `P.c+H_S(P)>=1201/256`.
The tangent bound `P.c+H_S(P)<=(q+|P|^2)/2` proves the result.
For reference, the orientation inequality follows by putting
`a>=b>=0`, `a^2+b^2=1`, `t=p/A`: the smaller possible total divided
by `A` is `(1+t)a+t b` for `t>=b/a`, and `a+(1+t)b` for `t<=b/a`.
After subtracting `1+t`, each branch is minimized at `t=b/a`, where
the value is `(1-a)(1-b)/a>=0`. The other tilt sign has larger support.

The reflected corner obstruction holds on the lower-right side.

## 2. Every extra square is left, right, or central

Let an additional square have center `(X,Y)` and coordinate halfwidth
`h>=1/2`. Comparing it with `B_L` gives

    if X<h-1/2, then Y>=h-7/16.

The alternative horizontal separation to the far left and the alternative
vertical separation below `B_L` put the center outside `|c|<61/40`.
Similarly comparison with `B_R` gives

    if X>1/2-h, then Y<=7/16-h.

The two conclusions are incompatible whenever both antecedents hold.
Assign `h=1/2,X=0` to category C first. For all other squares, the
following list is exhaustive:

- **L:** `X<=1/2-h`, `Y>=h-7/16>=1/16`.
- **R:** `X>=h-1/2`, `Y<=7/16-h<=-1/16`.
- **C:** `h=1/2`, `X=0`.

For `h=1/2`, a nonzero negative or positive `X` belongs respectively to
L or R, and `X=0` belongs to C. For `h>1/2`, the left and right regions
are disjoint and the open interval between them is forbidden.
A C square is axis-aligned because its projection width equals one.

## 3. At most one left and at most one right square

For a left square, comparison with `M_L` shows

    X<h-1  implies  Y>=h+9/16.

The downward vertical alternative contradicts `Y>=1/16`.
Also the left square's horizontal projection must overlap `M_2`.
The only possible horizontal separation would be `X<=-h-1` (separation
to the right is incompatible with `X<=1/2-h`). But then `X<h-1`,
so `Y>=h+9/16`; the corner obstruction applies. Thus

    either U: Y>=alpha+h+1/2,
    or     D: Y<=alpha-h-1/2.

In case U, `alpha<rho-1=21/40` and `Y>=h+9/16>=17/16`.
In case D, `alpha>=17/16` and

    h-1<=X<=1/2-h,  1/16<=Y<1/3.

The lower bound on `X` follows from the `M_L` comparison: otherwise
`Y>=17/16`, contradicting the displayed upper bound. Consequently a
D square's center lies in `[-1/2,0] x [1/16,1/3)`.

Two D squares cannot separate along either coordinate, since both
coordinate center differences are less than one. A U and D square
cannot coexist: their vertical center difference would be at least
`h_U+h_D+1>=2`, but every L center has height in `[1/16,rho)`.

Two U squares have vertical center difference less than
`rho-17/16=37/80<1`, so they would have to separate horizontally.
Let the leftmost be `S` and the other `T`. Then

    X_S <= X_T-h_S-h_T <= 1/2-h_S-2h_T <= -h_S-1/2,
    Y_S >= h_S+9/16.

This is the corner obstruction. Hence at most one L square exists.
Central reflection `(X,Y)->(-X,-Y)` interchanges the complete anchor
configuration with the same form with `alpha,beta` replaced by
`-beta,-alpha`; it proves the corresponding statement for R squares.

For R it is useful to record the two cases explicitly:

    lower: Y<=beta-h-1/2, forcing beta>-21/40;
    upper: Y>=beta+h+1/2, forcing beta<=-17/16.

An upper R square has center in `[0,1/2] x (-1/3,-1/16]`.

## 4. A high central square excludes an upper L square

Suppose an axis-aligned central square has center `(0,z)` with
`z>=alpha+1`, and there is an L square of type U. Both centers have
heights in `[17/16,rho)`, whose length is less than one. Thus they
cannot separate vertically. Horizontal separation forces
`-X_L>=h_L+1/2`, while U gives `Y_L>=h_L+9/16`. The corner
obstruction is a contradiction.

By central reflection, a central square with `z<=beta-1` excludes
an R square of the lower type.

## 5. A left and a right extra square cannot coexist

Use the central anchor `B_2=(0,gamma)`, which satisfies distance at
least one in height from both `alpha` and `beta`.

- **L upper, R lower:** `alpha<21/40`, `beta>-21/40`, so
  `alpha-beta<2`. Therefore `gamma>=alpha+1` or `gamma<=beta-1`.
  Section 4 contradicts respectively the L or R square.

- **L upper, R upper:** here `alpha<21/40` and `beta<=-17/16`.
  Still `alpha-beta<21/40+4/3=223/120<2`, so there is no middle
  interval for `gamma`. The lower possibility `gamma<=beta-1`
  is outside the center disk. Hence `gamma>=alpha+1`, contradicting
  the L square by Section 4.

- **L lower, R lower:** the reflected preceding argument applies.

- **L lower, R upper:** `alpha>=17/16` and `beta<=-17/16`.
  The upper and lower possibilities for `gamma` are outside the
  center disk, so

      beta+1<=gamma<=alpha-1,  hence -1/3<gamma<1/3.

  The L center is in `[-1/2,0] x [1/16,1/3)`. Its center-coordinate
  differences from `(0,gamma)` are less than one in both coordinates,
  so L cannot be coordinate-separated from `B_2`. Contradiction.

These four cases are exhaustive.

## 6. Central extras cannot supply the missing two squares

All C squares, together with the already present `B_2`, are aligned and
have horizontal center coordinate zero. Their heights must be pairwise
separated by at least one, and every such height `z` must satisfy

    |z-alpha|>=1, |z-beta|>=1, -rho<z<rho.

Since `alpha>beta`, the allowed set consists of the following possible
intervals:

    low:    (-rho,beta-1],
    middle: [beta+1,alpha-1]   if alpha-beta>=2,
    high:   [alpha+1,rho).

Each low/high interval has length at most `rho-17/16=37/80<1`.
The middle interval has length less than `2*(4/3)-2=2/3<1`.
If the middle interval exists, then

    alpha>2/3>rho-1, beta<-2/3<1-rho,

so the low and high intervals are empty. Thus at most two such central
square heights exist in total, and if there are two, one is high and
one low. This also forces `alpha<21/40` and `beta>-21/40`.

Therefore two extra C squares are impossible because `B_2` is already
central. If one extra C square exists, the two central units occupy
both high and low intervals. Any L square must then be of type U
(type D would force `alpha>=17/16`), and Section 4 excludes it using
the high central unit. Similarly any R square must be of the lower
type and is excluded using the low central unit.

There can consequently be at most one extra square of all types
combined: two on the same side are excluded by Section 3, one on each
side by Section 5, and all combinations involving C by Section 6.
Seven crossed-sign anchors cannot be completed to nine. QED.

## Integration

The complete two-direction equality domain may restrict to
`sigma_L=sigma_R`, and after one reflection to `sigma_L=sigma_R=+1`.
It retains the exact slider inequalities and the fifteen coordinate
disjunctions for the two extra squares. This addendum does not impose
horizontal stratification and does not extend the result to equality
packings lacking a two-direction cover.
