# A radial side channel with a nearby actual circle corner has a uniform angle gap

Date: October 26, 2026.

**Status: accepted complete local hand lemma and conditional whole-region
consequence after independent saved-source and physical-scope review.**
See REVIEW_C6_RADIAL_NEAR_CORNER_ROOT_2026_10_26.md.
The local lemma covers an entire radial-incident channel
whenever its actual application on the other boundary unit lies within
distance one of an actual circle corner. It does not assume that every
application has this property. A separate corollary proves the
central-capacity premise for the whole one-radial subfamily in which
both incident channels have that actual geometric property.

**Current full subfamily conclusion:** the independently reviewed
SIX_CYCLE_ONE_RADIAL_BOTH_ADJACENT_PORTS_CLASSIFICATION.md now
classifies the whole both-adjacent family into the already excluded
right-turn three-slider family. Its Section9 also excludes the entire
both-near-corner distance family. The local geometry and capacity
lemmas below remain valid, but their earlier partial allocation
conclusion is superseded by that full classification and completion
join. The general one-radial parent still has other open port types.

No full one-radial gate or original roadmap count is closed here. All
physical units, genuine channels, actual means and individual radial
corner weights remain unchanged.

## 1. Exact radial channel and the extra local premise

Work throughout

\[
       K:=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
       \qquad d(R)=\sqrt{R^2-\frac14}-1.
\tag{1}
\]

Let S be an actual physical two-circle-corner loaded unit in an
alternating all-side cycle. Its actual positively oriented radial
frame gives

\[
                   S=[d,d+1]\times[-1/2,1/2].
\tag{2}
\]

The complete support cover in Section 1 of
`RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md` proves that an
original reserve-one channel from S to another loaded unit uses a
strict inner vertex. After reflecting the full configuration if
needed, its actual application and normal are

\[
 P=(d,1/2),\qquad g=(-\cos\alpha,\sin\alpha),
                       \quad 0<\alpha<\pi/2.
\tag{3}
\]

The true unloaded degree-two transmitter equation fixes the original
application on the next unit as

\[
                     Q=P+g=(d-\cos\alpha,1/2+\sin\alpha).
\tag{4}
\]

No transverse mean is moved or selected. The local extra premise is
that the next unit has an actual circle corner z satisfying

\[
                       |z|=R,\qquad |z-Q|\le1.
\tag{5}
\]

For example (5) holds when Q is a vertex adjacent to its unique actual
circle corner. It is not asserted for an opposite vertex, a general
shared-side mean, or an arbitrary side-interior application. A zero
individual circle multiplier at z is harmless: (5) is a physical
circle-contact statement.

**Local theorem.** Under exactly (1)--(5),

\[
                              \alpha>\frac{12}{25}.
\tag{6}
\]

The bound is in radians. It covers every original force ratio and
every actual application satisfying (5).

## 2. One complete radius and angle calculation

The triangle inequality applied to (5) gives

\[
                                |Q|\ge R-1>0.
\tag{7}
\]

Use `R^2=(d+1)^2+1/4` to expand the difference of squares:

\[
 |Q|^2-(R-1)^2
       =2R-1+\sin\alpha-2d(R)(1+\cos\alpha)
       =:\Delta(R,\alpha).
\tag{8}
\]

For fixed `0<=alpha<pi/2`, this is strictly decreasing in R,
because

\[
 \partial_R\Delta
  =2-2(1+\cos\alpha)\frac{R}{\sqrt{R^2-1/4}}<0.
\tag{9}
\]

Both factors in the subtracted product are strictly greater than one.
At `R=K`, the exact strict bound `d(K)>91/100` follows from

\[
 K^2-\frac14-\left(\frac{191}{100}\right)^2
                           =\frac{101}{40000}>0.
\tag{10}
\]

Suppose `alpha<=12/25`. The elementary complete-interval estimates
`sin(alpha)<=alpha` and `cos(alpha)>=1-alpha^2/2`, together
with (8)--(10), give

\[
\begin{aligned}
 \Delta(R,\alpha)
 &\le\Delta(K,\alpha)\\
 &<2K-1+\alpha-
          2\frac{91}{100}\left(2-\frac{\alpha^2}{2}\right)\\
 &=\frac{91}{100}\alpha^2+\alpha-\frac{69}{100}\\
 &\le\frac{91}{100}\left(\frac{12}{25}\right)^2
          +\frac{12}{25}-\frac{69}{100}
  =-\frac{21}{62500}<0.
\end{aligned}
\tag{11}
\]

The quadratic increases on the nonnegative alpha interval, and
`2-alpha^2/2>0`, so every replacement has the stated direction.
Equation (11) contradicts (7). This proves the complete local theorem
with a rational gap; no angle subdivision or numerical bound is used.

## 3. Exact consequence when both radial-incident ports satisfy (5)

Now suppose the whole positive component is the original alternating
C6 with exactly one physical radial load S and two physical-unique
loads B,C. Retain all nine original units and the three arbitrary
completion squares. Suppose both applications on B,C at their
respective S-incident channels satisfy (5), using their actual unique
circle corners. This is the additional premise of this section.

The two actual applications on S are its different strict inner
vertices. Their distinctness follows from the original torque signs,
as proved in Section 1 of
`SIX_CYCLE_ZERO_DIAGONAL_TWO_RADIAL_EXCLUSION.md`; that local
argument requires only this radial unit and its two real incident
side channels, not a second radial unit. In its actual frame write

\[
 P_+=(d,1/2),\quad g_+=(-\cos\alpha,\sin\alpha),
 \qquad
 P_-=(d,-1/2),\quad g_-=(-\cos\beta,-\sin\beta),
\tag{12}
\]

with both angles strictly between zero and `pi/2`. The actual
positive force-polygon turn at S is exactly

\[
                         \theta_S=\pi-\alpha-\beta.
\tag{13}
\]

Apply the local theorem separately to the two unchanged channels.
Then

\[
 \alpha+\beta>\frac{24}{25}>\frac\pi4,
                       \qquad \theta_S<\frac{3\pi}{4}.
\tag{14}
\]

For the fixed angle comparison, `pi<22/7` gives
`pi/4<11/14<24/25`; the latter rational gap is `61/350`.

The unique-loaded upper-turn theorem used next is the **full local
theorem** in Section 1 of
`SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md`. Its proof covers
all actual loaded side-axis owners, arbitrary original shared means,
all non-owner vertex pairs, and their limiting cases. The local
calculation has no diagonal-transmitter hypothesis and does not assume
that the two ports are on one side or that their turn exceeds `pi/2`.
It therefore gives unconditionally, at the present unique loads,

\[
                         \theta_B,\theta_C\le\frac{3\pi}{4}.
\tag{15}
\]

The accepted force-polygon theorem gives the exact turn sum `2pi`.
Combining it with (14)--(15) proves

\[
                         \theta_B,\theta_C>\frac\pi2.
\tag{16}
\]

For the strictly obtuse radial-turn branch currently under study,
`theta_S>pi/2` is its actual premise. If instead `theta_S=pi/2`,
the already accepted complete classification and three-slider
completion exclusion in
`SIX_CYCLE_ONE_RADIAL_RIGHT_TURN_CLASSIFICATION.md` applies.
Thus no right-turn endpoint is silently discarded.

## 4. Why the original same-side port hypotheses now follow

At each unique unit, (16) allows the **local** feature consequence
used in Section 5 of
`SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md`.
There is no reliance on its separate three-unique global turn proof.
More explicitly, the complete local owner cover in the source cited
for (15) has the following consequences when the turn is greater than
`pi/2`:

- Outer side-axis cases and the two-axis case have turn at most
  `pi/2`, so are excluded.
- In a single inner-axis case, the other actual port must be the
  appropriate inner vertex on that same side; the alternative
  adjacent-to-circle vertex gives turn at most `pi/2`.
- With no loaded-axis owner, the opposite-vertex pair gives turn at
  most `pi/2`. The remaining two ordered pairs are the adjacent
  vertices on an inner side.

These cover every true owner, shared mean and endpoint. Coinciding
applications are excluded by the same actual-transmitter overlap
argument: their outward normals have angle `pi-theta<pi/2`,
so the two original side-interior transmitter half-planes overlap;
the shared-side endpoint case uses the existing outward side ray and
has the same strict overlap. No force is deleted to obtain distinct
ports.

Consequently each of B,C has its two distinct actual applications on
one physical inner side, with chord length in `(0,1]`. S already
has its two distinct inner vertices on one side by (12), with chord
length exactly one. Together with the three strict turns, these are
exactly the mask-independent premises of
`SIX_CYCLE_ALL_SIDE_CENTRAL_CAPACITY_ONE.md`.

**Whole-region corollary.** In this full one-radial subfamily, the
entire central free union of the actual six-body ring contains at
most one of the three original additional unit squares. Thus at least
two extras must lie in the union of the original exterior pockets.

The two radial-incident pockets individually retain their already
proved capacity at most one from
`RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md`. No capacity is
asserted here for the third pocket, and no coupled three-extra
allocation is claimed excluded by these necessary restrictions alone.

## 5. Retained physical scope and the precise remaining cases

The proof uses neither a radial concurrence inside S nor any upper
bound on the norm of that concurrence. Such an assumption would be
invalid for the unrestricted physical radial mask. Both original
radial corner weights, including either zero endpoint, remain
arbitrary, as do all transmitter sliders and every extra square.

If either radial-incident application is more than distance one from
its unit's actual unique circle corner, the extra premise (5) fails
and this corollary does not apply. In particular opposite-corner
applications and general non-endpoint means retain their full
original obligations. The complete strictly obtuse one-radial family,
the global sharp bound, equality classification and the earlier
prerequisite audit remain open. No original gate or checklist count
is changed by this local result. No computational certificate,
sampling premise, Lean compilation or CI action is used.
