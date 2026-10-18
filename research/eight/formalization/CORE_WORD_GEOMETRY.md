# Common quarter-word core/core costs without recursive searches

## Result and integration

`Arithmetic/CoreWordGeometry.lean` proves every common core/core entry
from the original geometric states. `WordGeometry.common_pair` now uses
this theorem whenever both endpoints are core, before selecting the
remaining finite certificates. Its public statement, original separating
axis, and common marker at each vertex are unchanged.

This removes **192 individual depth-96 recursive certificate declarations**:
three quarter increments, four ordered pairs of closed core charts, four
sign pairs, and four original axes. The generated common block decreases
from 432 to 240 declarations at this first checkpoint. The role labels
in the two wrong-word tables are unchanged.
The source generator omits exactly the core/core common class, so rerunning
it cannot restore the removed searches.

The source is an uncompiled draft. No Lean compilation, CI, or certificate
evaluation was performed. Exact rational arithmetic checked the margins
below; it does not establish Lean elaboration.

## The same marker on the complete core boundary

The common label is

\[
  \ell(a,b)=\frac{73}{10}\left(\frac7{12}-a\right)
             +\frac{291}{250}b,
  \qquad \psi(a,b)=\arctan(b/a)-\ell(a,b).
\]

The core consists of the closed side `a=7/12`, `0≤b≤1/2`, and the
closed circle arc

\[
 (a-1/2)^2+(b-1/2)^2=1/144,\qquad 1/2\le b\le a.
\]

On the side, the tangent to arctangent at `3/4` and the fixed bound
`atan(3/4)<161/250` give

\[
 \arctan(12b/7)-\frac{291}{250}b
 <\frac{41}{250}-\frac{117}{1750}b
 \le\frac{41}{250}.
\]

The cubic lower bound `atan x≥x−x³/3` gives nonnegativity throughout
`0≤x≤6/7`. Both arctangent estimates are the previously proved analytic
lemmas, with no adaptive subdivision.

On the corner, put `d=b−1/2`. The circle equation gives

\[
 a>67/120,\quad a\le7/12,\quad
 6d^2\le7/12-a\le d/2.
\]

The tangent at `6/7` bounds the angle increase from the side junction
by `(9/5)d`. Consequently the increase in the marker is at most

\[
 \left(\frac95-\frac{291}{250}\right)d-\frac{219}{5}d^2
 <\frac1{400}.
\]

This is one completed-square inequality. The exact peak is
`8427/3650000<1/400`. The corner upper bound is therefore below
`41/250+1/400<7/40`.

For the lower bound, `b≤a` and `a>67/120` give
`ell(a,b)<2081/2500`, while `b/a≥6/7` gives `atan(b/a)>2/3`. Thus

\[
 \psi(a,b)>-\frac{1243}{7500}>-\frac7{40}.
\]

The complete marker interval is `−7/40<psi<7/40`. Multiplying by the
original sign preserves this symmetric interval, including `b=0` and
both labels at a side/corner junction. `commonMarker_core_eq` identifies
this actual-coordinate label with the unchanged scalar label used by
the quarter-word proof.

## Center separation supplies every pair inequality

`CorePairGeometry.core_gap` already proves that every positive core/core
ray gap exceeds `4/3`: both center radii are less than `4/5`, and the
disjoint squares contain disjoint open incircles of radius `1/2`.
The resulting center distance is at least one, which excludes a smaller
ray gap by the cosine law.

For the lifted frame difference `phi` and original signed markers,

\[
 \phi+\ell_i-\ell_{i+1}
 =\delta-\psi_i+\psi_{i+1}
 >\frac43-2\frac7{40}=\frac{59}{60}.
\]

The largest common threshold is `391/400`; the exact reserve is

\[
 \frac{59}{60}-\frac{391}{400}=\frac7{1200}>0.
\]

No quarter increment or axis occurs in this argument. Thus all 192
original cases are covered at once, including multiple feasible axes.
Each vertex still has one marker value shared by its two incident edges,
so the global telescoping budget remains valid.

## Four geometric separator exclusions in the general word layer

The primary and secondary core obstructions also apply to an arbitrary
quarter lift, before any candidate-word or tangent-cut assumption.
`WordGeometry.original_not_core_excluded` now transfers the actual
separating-axis margin to the same four geometric estimates used by the
affine coverage proof:

| Original axis, zero-based | Excluded state condition | Angle condition |
|---|---|---|
| 1, target primary | Target is core | Quarter increment zero, `|phi|≤7/10` |
| 3, source primary | Source is core | Quarter increment zero, `|phi|≤7/10` |
| 0, source secondary | Target is core and source sign is negative | Every angle |
| 2, target secondary | Source is core and target sign is positive | Every angle |

For a primary axis, `cos(phi)−|sin(phi)|≥11/200` and the width at least
one require the receiving primary coordinate to exceed one. A core
coordinate is at most `7/12`. For a secondary axis, the orthogonal
projection identity bounds the core contribution by `5/6`; the indicated
signed transverse coordinate contributes at most zero, while the width
is at least one. These margins are strictly negative.

`WordProblems.CoreSeparatorExcluded` expresses these four semantic
classes, with no row identifiers or numerical partitions. The retained
certificate dispatchers require that this predicate be false, and the
actual geometry proves that fact. The originally selected feasible axis
is retained. At `b=0` the signed product is zero regardless of the sign,
so there is no exception or uncovered sign boundary.

This removes another 424 individual depth-96 certificate declarations:

| Family | Original declarations | After common core/core cost | After separator exclusions |
|---|---:|---:|---:|
| Common increments | 432 | 240 | 200 |
| Wrong word `0010111` | 684 | 684 | 492 |
| Wrong word `0011011` | 684 | 684 | 492 |
| **Total** | **1,800** | **1,608** | **1,184** |

The additional removals comprise 40 common declarations and 192 from
each wrong-word family. Every retained individual statement is byte-for-byte
identical to its preceding version. The source generator now omits both
the whole common core/core class and the four impossible separator classes.
The remaining 1,184 finite decisions are still active and unevaluated.
