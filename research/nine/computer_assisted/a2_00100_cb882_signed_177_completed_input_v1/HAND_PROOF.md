# A signed ABID terminal for the entire Cb882 domain 177

This is a conditional physical lemma for the unchanged nine original unit
squares in mask `001/00`, at strict squared radius `q < Q = 1105/256`.
It is intended to discharge the entire already saved domain 177. The scalar
candidate has 32 complete domains, 36 tree nodes, 34 terminal boxes, and no
frontier. Independent scalar replay, physical review, and the original
complete-cover attachment remain separate acceptance gates.

## 1. Original premises and the exact caller

Keep the same nine distinct squares A,B,C,D,E,F,G,H,I, all 36 corner
inequalities, all 36 physical nonintersection disjunctions, all five marked
cones, actual AB/BC/EF/FG and strictly weak CD. The proof uses the row
A,B,I,D; original H is retained with every original predicate.

Write `dXY = xY-xX`, `vXY = yY-yX`. The additional guards are

* the certified B slope interval lies in `[-2/23,2/23]`;
* D has canonical slope at most zero;
* `dBI >= 0`, `dID >= 0`;
* `|vBI| <= 1/16` and `1/16 <= vID <= 1/4`.

Actual AB already gives `dAB >= hA+hB`, where h denotes horizontal
projection halfwidth. No bound on vAB is needed by this new lemma.

In the frozen `cb882_abid_138/MANIFEST.json`, pending domain 177 has

```
|tan(thetaB)| <= 46798823265/549755813888 < 2/23,
thetaD in [-pi/4,0],
dBI >= 855653/1048576 > 0,
dID >= 434432029724121/5000000000000000 > 0,
vBI in [-1/16,1/16],
vID in [1/16,261293/1048576] subset [1/16,1/4].
```

These are bounds on the actual unchanged original centers and frames. The
whole-original checker must obtain this state by replaying its full ancestry;
the displayed intervals are not replacement premises supplied by discovery.

## 2. Frame notation and the physical BI reduction

For each canonical angle write `alpha = cos(theta) > 0`,
`beta = |sin(theta)|`, `s = sign(theta)`, and `h=(alpha+beta)/2`.
At theta=0 either sign representation is included. In the physical canonical
range `alpha >= beta`. The support sum on an axis owned by either square of
the pair XY is

```
RXY = (1 + cos(thetaX-thetaY) + |sin(thetaX-thetaY)|)/2 >= 1.
```

The value is unchanged when the owned axis is rotated through a quarter turn.
This is the literal unit-square support formula, not a chosen replacement
separating frame.

For BI, disjoint open unit incircles give `dBI^2+vBI^2 >= 1`.
Since `|vBI| <= 1/16` and `dBI >= 0`, this implies `dBI > |vBI|`.
A physical separating normal oriented toward I cannot have nonpositive
horizontal component: its center projection would then be at most
`|vBI| < 1 <= RBI`. If o is its actual owner, either its shallow or its
steep forward axis has center projection at most

```
alpha_o*dBI + beta_o*|vBI|.
```

For the steep axis this follows from
`beta_o*dBI+alpha_o*|vBI| <= alpha_o*dBI+beta_o*|vBI|`.
Consequently, for that same actual owner `o in {B,I}`,

```
dBI >= RBI/alpha_o - beta_o/(16*alpha_o).                 (1)
```

This is exactly the unsigned owner reduction in the accepted
`opposite_boundary/HAND_PROOF.md`, section 2, equation (6), specialized to
`1/16`. Both physical BI axes, all contacts, and both signed height gaps are
included. It is not a signed shallow-axis assumption.

## 3. All four signed ID axes

Here `dID >= 0` and `1/16 <= vID <= 1/4`. Again a separating normal oriented
toward D must have positive horizontal component, because a nonpositive one
would have projection at most `1/4 < 1 <= RID`.

For owner `p in {I,D}` its forward normals are

```
shallow: n=(alpha_p, s_p*beta_p),
steep:   n=(beta_p, -s_p*alpha_p).
```

For either actual choice, let `v*=1/4` if `n_y >= 0`, and `v*=1/16`
if `n_y < 0`. Its literal separator inequality gives

```
dID >= (RID - n_y*v*)/n_x.                              (2)
```

If the steep normal has `n_x=beta_p=0`, it is vertical. Its center projection
is at most `1/4`, so this actual separator is impossible. This zero-angle face
is handled explicitly; it is not removed by division. Every other normal in
(2) has a strictly positive denominator.

## 4. The exact finite scalar statement

The accepted normalized endpoint toll is

```
T(theta)=max(2*beta/23, (9*beta-41*(1-alpha))/32) >= 0.
```

Let LBI be the right side of (1), for each of the two possible actual owners,
and LID the right side of (2), for each of the four possible actual ID axes.
The finite scalar statement is

```
hB - hD + T(thetaD) - 2 + LBI + LID >= 0.                (3)
```

It covers both signs of B and I, D nonpositive, and all eight combinations
of BI owner and ID owner/axis: 32 domains in total.

Put `z_j=s_j*x_j=tan(theta_j/2)`, for j=B,I,D. The rational roots are

```
0 <= xB <= 1/23,    0 <= xI,xD <= 5/12.
```

The exact B transport follows from `x=t/(sqrt(1+t^2)+1) <= t/2` for t>=0;
the caller's strict slope bound below 2/23 therefore suffices, including t=0.
The other roots contain every physical canonical half-angle because
`sqrt(2)-1 < 5/12`. Enlarging the roots imposes a stronger scalar obligation;
the geometric deductions above still use the physical canonical range.

The rational formulas are

```
alpha=(1-x^2)/(1+x^2), beta=2x/(1+x^2),
h=(1-x^2+2x)/(2*(1+x^2)),
Rij=((1+zi*zj)^2+(1+zi*zj)*|zi-zj|)/((1+xi^2)*(1+xj^2)).
```

The last formula equals the physical support sum on the canonical domain.
For any epsilon in [-1,1], replacing `|zi-zj|` by
`epsilon*(zi-zj)` gives a lower bound, since `1+zi*zj > 0` on every root.
For any tau in [0,1], interpolating the two accepted D tolls also gives a
lower bound for their maximum. The saved three dyadic weights have exactly
these ranges: two absolute-value weights and one toll interpolation weight.

The base endpoint expression and the toll increment are

```
-hD + 2*betaD/23 = (-23-38*xD+23*xD^2)/(46*(1+xD^2)),
Tsharp-Tbase = (143*xD-943*xD^2)/(368*(1+xD^2)).
```

For shallow ID the positive common denominator is
`D0=product_j(1-xj^4)`. For steep ID it is `2*xp*D0`, positive on each
physically possible steep-axis case. The separately impossible xp=0 face is
nevertheless retained in the closed scalar certificate. Multiplication by
these denominators and the integer scale 5888 gives a polynomial of degree
at most six in each variable. No sign of an unknown denominator is assumed.

Each saved box uses the ordinary tensor power-to-Bernstein identity at
degree six. Nonnegative exact coefficients prove nonnegativity over its
entire closed box. A dyadic split retains both closed halves, including the
shared face. The independent checker must reconstruct the physical rational
features, validate all weight ranges, check every exact integer coefficient,
and verify all 32 complete parent unions. The numerical optimizer and the
producer's own checks are not the independent acceptance gate.

## 5. Lift to all nine original squares and strict radius

Actual AB, (1), (2), and (3), together with `T(thetaA)>=0`, give

```
xD-xA-hA-hD+T(thetaA)+T(thetaD) >= 2.                    (4)
```

Use the accepted physical two-square weighted caps on A/E in the leftward
direction and D/G in the rightward direction. They use the same original
squares, arbitrary centers and physical separator owners. Their sum is

```
46*[xD-xA-hA-hD+T(thetaA)+T(thetaD)]
 +(27/2)*[xG-xE-hE-hG] <= 2*(211/4).                    (5)
```

The cap sum is strict for `q<Q`. Actual EF and FG imply
`xG-xE-hE-hG >= 2*hF >= 1`. Equations (4)-(5) thus give
`105.5 > 46*2+13.5=105.5`, a contradiction. This discharges the whole guarded
domain, including the fully aligned scalar face, at strict radius. No
additional angle, height, sign, owner, or H/I replacement is assumed.

## 6. Aligned face and the original strictly weak CD bit

For clarity, no global closed-Q exclusion or classification is inferred from
the mere nonnegative scalar certificate. The strict-radius argument already
handles all its zero faces. The fully aligned B,I,D face has the inherited
original CD blocker as well, so it is not left as an unproved numerical limit.

On that face physical BI and ID separation, with vertical gaps below one,
forces their horizontal gaps at least one. Equality at Q in (4)-(5) forces
the nonnegative A toll to vanish, so A is aligned, and every row gap is one.
Thus `xD-xA=3`. Equality of the ordinary endpoint caps aligns E,G, and equality
of the short-chain width aligns F. The original AB and BC projection links,
and the original CD cone inset inequality, give the same inherited chain

```
3 >= 1 + 2*hB + hC + 1/(4*hC) >= 3.
```

Since `hB=1/2` and `hC+1/(4*hC)-1=(2*hC-1)^2/(4*hC)`, C is aligned.
The CD inset gap is then at least one, contradicting the original strictly
weak CD bit. This uses original AB/BC/CD and preserves both original extras;
it does not add a cone or a contact to I or H.
