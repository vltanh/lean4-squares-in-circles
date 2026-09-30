# Analytic normalization of six squares

## Scope and endpoint

The normalization source is assembled in
`SquaresInCircles/Six/Normalization/Complete.lean` and exported separately by
`SquaresInCircles/Six/AnalyticNormalization.lean`. Its endpoint is
`Normalization.normalize_of_candidate`: an actual six-square `Packing`, with
squared radius at most `Six.qStar`, admits the normalized model and a recorded
`CongruentOrDiagonal` relation. The model's geometric properties are proved
from that packing, not inserted as additional assumptions on the problem.

This companion explains the analytic replacements for the last normalization
certificates: fixed-pin covering, broad windows and Appendix A. It also records
how they connect to the already written analytic strong-core, cap, moving-pin
and ordering arguments. Compilation and kernel acceptance remain deferred.
The later D-edge classification, tighter candidate domain and common pair
lower envelope are separate unfinished analytic conversions.

Throughout set

\[
 Q_0=\frac{142559}{50000},\quad R_0=\sqrt{Q_0},\quad
 \rho_0=\sqrt{Q_0-\tfrac14}-\tfrac12,\quad c_0=\rho_0-1.
\]

The elementary constant lemmas give

\[
 \rho_0<\frac{1113}{1000},\quad c_0<\frac{113}{1000},\quad
 r_c:=\frac32-\rho_0>\frac{77}{200},\quad
 a_{\min}=2-\rho_0>\frac{177}{200},\quad U_0<\frac{117}{250}<\frac12.
\]

A signed chart has center coordinates `(a,b)` in its side frame, primary phase
`t`, and exact containment inequality

\[
 (a+\tfrac12)^2+(|b|+\tfrac12)^2\le Q_0,\qquad a\ge\tfrac12,\quad |b|\le a.
\]

The original open- and closed-square predicates, rather than bounding boxes,
are used throughout.

## 1. What is established before pins

`NormalizeFrame` translates the disk center to zero, aligns the containing
square, and uses a quarter-turn to make its center coordinates nonnegative.
No reflection is required at that stage. The existence of the containing
square follows from the existing Seven exterior-ring theorem below squared
radius `13/4`.

`StrongCore` proves

\[
 0\le c_x,c_y\le c_0
\]

before pins or sectors. It uses the genuine three-branch Seven markers and the
strict five-marker separation. The small-secondary-center forbidden arc is

\[
 (-\pi/2+2/3,\ \pi/2-3/8),
\]

whose length is `pi-25/24 > 2*pi/3`; the other central-coordinate regime uses
`(-27/50, pi/2)`, also longer than `2*pi/3`. `Analytic/CoreSmallNorth`,
`CoreSmallSouth`, `CoreLargeEast`, `CoreLargeQuadrants` and `ForbiddenArcs`
contain the complete quadrant/separator arguments and modular lift handling.
There is no central-coordinate grid. Temporary diagonal symmetry proves the
symmetric bound on the original packing; it does not impose D's later angle
convention.

The central square contains the open disk of radius `r_c`. The nearest point
of an exterior square avoids this disk. Combining that fact with containment
first rules out `|b| >= 1/2`, then gives

\[
 a_{\min}\le a\le\rho_0,\qquad |b|\le U_0<\frac12.
\]

`CoreGeometry`, `ChartBounds` and `NearestPoint` connect this to the actual foot
on the relative interior of the near edge. The same bounds make both secondary
central separating margins strictly negative and select the genuine marker's
axial branch. Thus the central separation alternatives reduce to OWN or one
of the four cardinal directions, without assuming a pin assignment.

## 2. A universal sixty-degree two-pin lemma

Let two pins have radius `9/10` and phases `q` and `q+pi/3`. Suppose the primary
phase lies between them, and write `v=t-q`, so `0 <= v <= pi/3`. In the square's
side frame the two pins have coordinates

\[
 \tfrac9{10}(\cos v,-\sin v),\qquad
 \tfrac9{10}(\cos(\pi/3-v),\sin(\pi/3-v)).
\]

The far normal inequalities are automatic from `a>=1/2`. At least one near
normal inequality is strict: one pin is within `pi/6` of the primary direction,
and its normal projection is larger than `rho0-1/2`. Both transverse
inequalities cannot fail in the same direction because

\[
 \tfrac9{10}\{\sin v+\sin(\pi/3-v)\}
 =\tfrac9{10}\cos(v-\pi/6)<1.
\]

A remaining crossed failure would force, after exchanging the two pins when
necessary,

\[
 a+\tfrac12\ge1+\tfrac9{10}\cos v,\qquad
 |b|+\tfrac12\ge1-\tfrac9{10}\sin(\pi/3-v).
\]

On the whole interval `0 <= v <= pi/3`,
`cos v >= 1-v/2`. For `v<=1` this follows from `cos v>=1-v^2/2`; for `v>=1`
it follows from `cos v>=1/2`. Also `sin x<=x` and `pi<22/7`. Consequently the
two nonnegative far-corner coordinates are at least

\[
 A=\frac{19}{10}-\frac9{20}v,\qquad B=\frac2{35}+\frac9{10}v.
\]

Their squared sum exceeds the containment ceiling by the identity

\[
 A^2+B^2-Q_0
 =\frac{81}{80}\left(v-\frac{50}{63}\right)^2
  +\frac{304609}{2450000}>0.
\]

This contradiction proves that at least one of the two pins is in the open
square. The proof is `Analytic/PinArc.sixty_pin_cover`; it uses no OWN or cap
assumption and no subdivision of the angle interval.

## 3. OWN profiles, fixed pins and broad windows

Write `h(t)=(|cos t|+|sin t|)/2`. OWN is the actual inequality

\[
 a-\tfrac12-c_x\cos t-c_y\sin t-h(t)\ge0.
\]

### East

In the east primary octant, the strong central box yields the profiles

\[
 a\ge\tfrac12+\tfrac12\cos t+\tfrac12\sin t\quad(t\ge0),
\]

\[
 a\ge\tfrac12+\tfrac12\cos v+\tfrac{387}{1000}\sin v
 \quad(t=-v\le0).
\]

Each positive sine/cosine combination is concave on the first octant. Checking
its natural endpoints at `3/10` or `5/12` and `pi/4`, with the displayed Taylor
bounds in `OwnAxisWindows`, contradicts `a<=rho0` outside

\[
 -\frac5{12}<t<\frac3{10}.
\]

The existing analytic moving-pin theorem puts `(1+c_x,0)` inside the square.
Contract its transverse coordinate towards that of the origin: since `|b|<1/2`,
the transverse coordinate of `(9/10,0)` remains strictly inside. Its normal
coordinate follows directly from `cos t>=5/6` and `a<=rho0`. Thus the fixed east
pin is inside. This is `FixedPinInclusions.own_east_fixed_pin`.

### West

For primary phase `pi+theta`, a negative deviation `theta=-v` gives

\[
 a\ge\tfrac12+\tfrac{387}{1000}\cos v+\tfrac12\sin v.
\]

Concavity and the explicit endpoints `v=2/3, pi/4` imply `theta>-2/3`.
For `theta<=-pi/12`, a missed W pin would imply a negative signed transverse
coordinate and the two lower bounds

\[
 a+\tfrac12\ge\frac{277}{200}+\frac v3,\qquad
 |b|+\tfrac12\ge\frac{49}{40}-\frac9{10}v.
\]

Their squared sum satisfies the single completed-square identity

\[
 \left(\frac{277}{200}+\frac v3\right)^2+
 \left(\frac{49}{40}-\frac9{10}v\right)^2-Q_0
 =\frac{829}{900}\left(v-\frac{2307}{3316}\right)^2
  +\frac{20199561}{165800000}>0.
\]

Hence the left flank contains the W pin. On the remaining interval
`-pi/12 <= theta <= pi/4`, the sixty-degree lemma covers W or D.

If the W pin itself is inside, the positive deviation improves to `theta<5/8`.
Otherwise monotonicity on the octant and the explicit Taylor values give

\[
 a+\tfrac12\ge1+\frac{387}{1000}\frac{279}{200},\qquad
 |b|+\tfrac12\ge\frac9{10}\frac{387}{500},
\]

whose squared sum is greater than `Q0`. This argument uses the actual pin's
transverse coordinate and not a fabricated support branch.

## 4. Cardinal caps and the five-pin assignment

An actual cardinal separating margin puts the entire closed square in a
cardinal cap. To find its primary direction, split only into the four primary
quadrants. A deep cap cannot face the short coordinate: the signed cap bounds
would imply the short coordinate is larger than the primary coordinate.
The backwards primary direction is impossible from `a>=|b|` and
`cos v>=|sin v|`. The remaining direction has `|v|<2/5` by the exact cap profile.

For east and north the cap depth is at least `1/2`, so `|v|<1/4`. The actual
open cap-piercing point, contracted as above, gives the corresponding fixed pin.
For a west cap, rotation to the east-facing frame gives depth at least `r_c`.
Its left flank uses the same completed-square obstruction as OWN; the remaining
arc uses the sixty-degree lemma. South and north follow by local diagonal
point-set identities. These local identities do not re-normalize the packing.

The resulting location information is retained in `PinLocations`:

| Primary location | Pin guaranteed inside | Additional information |
|---|---|---|
| E | E | `-5/12 < deviation < 3/10` |
| N | N | reflected E window |
| W | W or D | left flank contains W; if W is inside, deviation `<5/8` |
| S | S or D | reflected W information |

All five exterior squares therefore meet the five-pin set. Interior-disjointness
makes the chosen pin assignment injective; equal finite cardinalities make it
bijective. A square cannot contain a second pin because that pin already belongs
to a different square's interior.

This uniqueness also proves the broad labelled windows, without a second
certificate. A square assigned D in the W primary quadrant cannot lie on the
left flank, since it would also contain W. Its deviation from `5*pi/4` is
therefore greater than `-pi/3 > -15/14`. The S-quadrant case gives the other
endpoint. The exact windows are

| Label | Phase center | Lower deviation | Upper deviation |
|---|---:|---:|---:|
| E | 0 | `-5/12` | `3/10` |
| N | `pi/2` | `-3/10` | `5/12` |
| W | `pi` | `-2/3` | `5/8` |
| D | `5*pi/4` | `-15/14` | `15/14` |
| S | `3*pi/2` | `-5/8` | `2/3` |

Real phase representatives are identified using their common angle class and
the strict bound on their difference by `2*pi`; no modular representative is
silently discarded.

Finally, wrong cardinal axes are excluded directly by the fixed pin coordinates.
For example every non-E pin has x-coordinate at most `3/10`, whereas an east-cap
square lies to the right of `1/2+c_x`. Analogous coordinate signs give the other
exclusions. Together with the strong-core secondary exclusions, the allowed
central axes are `{OWN,E}`, `{OWN,N}`, `{OWN,W}`, `{OWN,W,S}`, `{OWN,S}`.

`PinPacking` now constructs these fields using `five_pin_cover`,
`labelled_window` and `allowed_axis_of_pin`. `PinReflection` uses the same
analytic coordinate lemma when transporting the packing.

## 5. Ordering, moving pins and the one global reflection

The existing analytic `OwnMovingPin` argument uses

\[
 a+\tfrac12\ge1+(\tfrac12+x)\cos t+\tfrac{77}{200}|\sin t|.
\]

Failure of the transverse moving-pin inequality supplies a second far-corner
lower bound. Increasing x from zero increases the sum of squares; at x=0 the
unit-circle relation gives the polynomial lower bound displayed in
`MovingPinPolynomial`. It is positive on the entire interval
`0<=|sin t|<=5/12`. Thus the certificate previously used for OWN is absent.
Cardinal cases use the actual cap-piercing theorem.

The W/D order proof is likewise analytic. A reversed order and the broad
windows give an angle gap at most `41/40`. A center-projection estimate excludes
both primary SAT axes. The two pins, separated by `pi/3`, force both secondary
separators to point forward, but their forward projections are strictly below
the separation threshold. All four axes fail, a contradiction.

The only global diagonal reflection swaps E/N and W/S while fixing D and puts
D's phase at most `5*pi/4`. It is retained in `CongruentOrDiagonal`. The ordinary
`Congruent` definition is unchanged. Cardinal is preferred on ties. Cap piercing
proves one helper per cardinal side, and the cardinal angle bound excludes D's
south-cardinal alternative after this half-window choice.

The remaining D west-cardinal possibility is eliminated next.

## 6. Appendix A: one stress, two possible secondary normals

Suppose D is west-cardinal. W cannot also be west-cardinal, by one-helper
uniqueness, so W is OWN. Write their phases as `pi+t` and `pi+u`. The already
proved windows, cardinal bound and W/D order give

\[
 -\frac23\le t\le u\le\frac25,\qquad u\ge-\frac25.
\]

Both squares retain their core-exclusion and containment bounds. Put
`delta=u-t`, so `0<=delta<=16/15`. Monotonicity of cosine and its degree-six
Taylor bound at `16/15` give `cos delta>=12/25`. The uniform primary projection
lemma excludes both primary axes and both signs. The short transverse bound
excludes both reversed secondary axes. Only the forward W-secondary and
D-secondary normals remain.

Use one multiplier triple

\[
 (\alpha,\beta,\mu)=\left(\frac3{10},\frac9{20},\frac14\right)
\]

on the directed edges C-D, C-W, W-D. Let z=t for W-secondary and z=u for
D-secondary. The incidence forces are

\[
 g_C=(\alpha+\beta\cos t,\ \beta\sin t),
\]
\[
 g_W=(-\beta\cos t-\mu\sin z,\ -\beta\sin t+\mu\cos z),\qquad
 g_D=(-\alpha+\mu\sin z,\ -\mu\cos z).
\]

In particular,

\[
 |g_W|^2=\frac{53}{200}+\frac9{40}\sin(z-t),\qquad
 |g_D|^2=\frac{61}{400}-\frac3{20}\sin z.
\]

The mixed term in the first formula is **positive**. The D-secondary source is
not claimed to dominate W-secondary.

For every contained square, the universal far-vertex support inequality is
`g.center <= R0*|g|-width(g)`. The following signed projections are valid lower
bounds on the widths, without requiring any unproved absolute-value sign:

\[
 h_W\ge\frac9{40}+\frac18\{\sin(z-t)+\cos(z-t)\},
\]
\[
 h_D\ge\frac3{20}(\cos u-\sin u)+\frac18\{\sin(u-z)+\cos(u-z)\}.
\]

The central force is bounded by

\[
 C(t)=c_0\left(\frac3{10}+\frac9{20}\cos t+\frac9{20}\max(\sin t,0)\right).
\]

Adding the three separating inequalities and applying these supports gives a
nonpositive defect. Direct algebra identifies it with one of

\[
 \Phi_W=H(t,u)-R_0\sqrt{53/200}-R_0\sqrt{61/400-(3/20)\sin t},
\]
\[
 \Phi_D=H(t,u)-R_0\sqrt{53/200+(9/40)\sin\delta}
                 -R_0\sqrt{61/400-(3/20)\sin u},
\]

where

\[
 H=\frac{17}{20}+\frac3{10}\cos u+\frac3{10}\max(-\sin u,0)
 +\frac9{40}(\cos t+|\sin t|)+\frac14(\cos\delta+\sin\delta)-C(t).
\]

We prove both defects strictly positive, contradicting actual separation.

### 6.1 W-secondary

The rational bounds `R0<8443/5000`, `c0<113/1000` and
`sqrt(53/200)<=103/200` are immediate squared comparisons. One completed square
proves a global radical majorant:

\[
 \left(\frac{99}{250}-\frac{13}{80}z\right)^2
 -\left(\frac{61}{400}-\frac3{20}z\right)
 =\frac{169}{6400}\left(z+\frac{1704}{4225}\right)^2+\frac7{338000}.
\]

Its affine side is nonnegative on the required sine range. It yields the
minorant

\[
 M=C+\frac3{10}\cos u+L\sin u+A\cos t+K\sin t+
       \frac14(\cos(u-t)+\sin(u-t)),
\]

with

\[
 C=-\frac{3611073}{5000000},\quad A=\frac{3483}{20000},\quad
 K_- =\frac{19759}{400000},\quad K_+=\frac{179419}{400000}.
\]

Use `K_-` when t is negative and `K_+` when it is nonnegative; L is `-3/10`
when u is negative and zero otherwise. There are exactly three sign regions:
a negative triangle, a mixed-sign rectangle and a positive triangle.

Expanding the difference-angle terms writes M, in either coordinate, as a
constant plus a sine/cosine linear combination. Its coefficient signs on the
appropriate positive or negative interval prove concavity. The diagonal is
also such a combination. Consequently the only endpoints needed are

\[
 (-2/3,-2/5),\ (-2/5,-2/5),\ (-2/3,0),\ (0,0),\
 (-2/3,2/5),\ (0,2/5),\ (2/5,2/5).
\]

These are the vertices of the order domain and the two absolute-value walls,
not a numerically selected mesh. The global degree-six cosine and degree-seven/
five sine inequalities give positive rational lower values at all seven.
For the most restrictive listed vertex `(-2/3,2/5)`, one such lower value is
`29284771/430565625000 > 1/20000`. The other six are larger. Thus `Phi_W>0`.

### 6.2 D-secondary

Keep the positive mixed term. For `r(x)=sqrt(p+q sin x)`, exact differentiation
and `r^2=p+q sin x` give

\[
 r''=-\frac r4+\frac{p^2-q^2}{4r^3}.
\]

Therefore `A cos x+B sin x-R r(x)` is concave if `R>=0`, `p^2>=q^2`, the
radicand is positive, and

\[
 Rr(x)\le4(A\cos x+B\sin x).
\]

Write `Phi_D=17/20-(3/10)c0+J(t)+H_1(u)+G(u-t)`, where

\[
 J_-=(9/40-9c_0/20)\cos t-(9/40)\sin t,\qquad
 J_+=(9/40-9c_0/20)(\cos t+\sin t),
\]

\[
 H_{1,-}=\tfrac3{10}(\cos u-\sin u)-R_0\sqrt{61/400-(3/20)\sin u},
\]
\[
 H_{1,+}=\tfrac3{10}\cos u-R_0\sqrt{61/400-(3/20)\sin u},
\]

\[
 G(\delta)=\tfrac14(\cos\delta+\sin\delta)
           -R_0\sqrt{53/200+(9/40)\sin\delta}.
\]

J is concave on each sign interval. For H1, `|u|<=2/5` gives `cos u>=23/25`
and the root at most `1/2`; these establish the sufficient curvature bound.
For G, `cos delta>=12/25`, `sin delta>=0` and the unit-circle identity imply

\[
 Q_0(53/200+(9/40)\sin\delta)\le(\cos\delta+\sin\delta)^2,
\]

which proves its curvature bound. All radicands are bounded strictly away from
zero on their intervals. Affine changes of argument preserve concavity.

Separate coordinate concavity and diagonal concavity again reduce to the same
seven vertices. Rational upper bounds for the W-force root at difference
angles `0,4/15,2/3,16/15,2/5` are respectively

\[
 103/200,\quad57/100,\quad637/1000,\quad17/25,\quad297/500.
\]

Upper bounds for the D-force root at u=`-2/5,0,2/5` are
`23/50,391/1000,307/1000`. Each is proved by squaring and the explicit Taylor
sine inequalities. The least of the resulting endpoint lower values occurs
at `(-2/3,0)` and is

\[
 \frac{2507096063}{344452500000}>0.
\]

Thus `Phi_D>0` on the entire domain. This completes the actual geometric
west-cardinal exclusion. The compatibility theorem
`Normalization.WestCardinal.impossible` now calls this analytic proof and
contains no finite checks.

## 7. Assembly and completion boundary

`PinPacking.D_west_negative` supplies the exact domain, W/D core exclusions,
W OWN margin, D west margin and actual pair disjointness to Appendix A. The
west-cardinal contradiction, together with the already excluded south case,
forces D canonically OWN, including exclusion of cardinal ties.

The normalized packing therefore has the strong/coarse central box, genuine
chart and side-nearest bounds, fixed and moving pins, the labelled windows,
cyclic primary order, the cardinal-preferred two-choice rule, one cardinal
helper per side, cardinal angle bounds and opposite-pair budgets. N25+ and the
candidate-radius `4*cStar` budget are retained with their required cardinal
hypotheses. The optional diagonal reflection is explicitly carried to the
later equality argument.

The independent entry point is `Six/AnalyticNormalization.lean`.
`SixNormalizationAxiomAudit.lean` contains deferred audit commands, not executed
output. The static import review and explicit rational endpoint calculations
are development checks only; neither is substituted for a Lean proof premise.
The theorem bodies perform the displayed analytic reductions themselves.

The analytic normalization source is now assembled. This statement does not
close the separate analytic conversion of the fixed D-edge classification,
tails and common pair envelope, or claim compiler/kernel acceptance of the
unrestricted n=6 theorem.
