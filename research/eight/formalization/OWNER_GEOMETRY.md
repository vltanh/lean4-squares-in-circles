# Owner geometry: four complete table replacements

## Result and exact scope

The entire closed half-angle interval

\[
 -\frac38\le z\le0,\qquad t=2\arctan z,
\]

is now excluded by one four-circle argument. The hypotheses are the
existing candidate frame, the signed tangent cuts, the intended owner
sets, the containing squared radius
\(q\le Q_0=9789/2500\), and total aligned mismatch \(S\le1/1000\).
The result includes zero tilt, both interval endpoints, simultaneous
feasible axes, and all original center positions. No radial contact
equality or center proximity is assumed.

The quantitative inequality is

\[
\boxed{
q\ge \frac{2257}{576}
  +\frac{451}{4608}(-\sin t)
  -\frac{3001}{1000}\frac{41}{48}\,S.}
\tag{1}
\]

Since \(-\sin t\ge0\), the difference between the right side at
\(S=1/1000\) and \(Q_0\) is exactly

\[
\frac{2257}{576}
 -\frac{3001}{1000}\frac{41}{48}\frac1{1000}
 -\frac{9789}{2500}
=\frac{34477}{144000000}>0.
\tag{2}
\]

The draft Lean proof is in `Candidate/GeometricOwners.lean`:
`AlignedStress.four_circle_bound`, `negative_tilt_quantitative`, and
`negative_tilt_excluded`. It has not been compiled. The exact scalar
identity, coefficient, and strict reserve below were independently
checked with Python's `Fraction` arithmetic; that calculation did not
run Lean, a historical certificate replay, or an optimizer.

## 1. The seven nominal inequalities retain every allowed owner

Use the original own-frame coordinates
\((a_i,-\sigma_i b_i)\), with roles \((H,G,A,B,T,D,E)\).
Let \(d_i\) be the five aligned frame differences and write

\[
I=\{H,A,B,T,D\},\qquad S=\sum_{i\in I}|d_i|.
\]

Set \(r=-\sin t\ge0\), \(c=\cos t\), and
\(W=(1+c+r)/2\). The allowed owner sets are exactly the existing
terminal sets

\[
\{1,3\},\{1\},\{1,3\},\{3,4\},
\{1,3\},\{3,4\},\{2\}.
\]

The two allowed owners have the same nominal projection on each
aligned edge. For each actual feasible owner, the existing amplitude
and support-cusp estimates give

\[
F_i^{\rm nominal}\ge1-\frac{1001}{1000}|d_i|,
\qquad i\in I.
\tag{3}
\]

For clarity, the elementary estimate behind (3) is
\(|F_i(\phi+d)-F_i(\phi)|\le3|d|/2\) together with

\[
W(d)\ge1+\frac{|d|}{2}-\frac{d^2}{4}-\frac{|d|^3}{12}.
\]

At \(|d|\le1/500\), the resulting loss is at most
\((1001/1000)|d|\). The G-to-A angle has no error. The E-to-H
angle error has magnitude at most \(S\); its projection and support
changes together cost at most \(2S\).

Thus all actual configurations satisfy the following seven rows:

| Edge | Necessary nominal inequality |
|---|---|
| H to G | \(b_H+b_G\ge1-(1001/1000)|d_H|\) |
| G to A | \(-b_G+a_Ac+b_Ar\ge W\) |
| A to B | \(b_A+b_B\ge1-(1001/1000)|d_A|\) |
| B to T | \(a_B-b_T\ge1-(1001/1000)|d_B|\) |
| T to D | \(b_T+b_D\ge1-(1001/1000)|d_T|\) |
| D to E | \(a_D+b_E\ge1-(1001/1000)|d_D|\) |
| E to H | \(a_H-a_Er-b_Ec\ge W-2S\) |

Every retained signed axis is included in (3). Selecting an owner is
used only to obtain one necessary inequality on each edge. The proof
does not assert that another simultaneously feasible axis disappears.
The nominal-collapse proof now checks only the seven edges and four
axes; it no longer enumerates all functions from edges to axes.

## 2. The weights come from the exact aligned configuration

Put

\[
\alpha=\frac{31}{72},\qquad
\omega=\frac{1271}{1728},\qquad
\varepsilon=\frac{41}{48}.
\tag{4}
\]

These constants are determined by the four aligned farthest corners

\[
(41/24,1),\quad(41/24,1),\quad
(3/2,31/24),\quad(3/2,31/24).
\]

All four have squared norm \(2257/576\). The first two carry circle
weight \(31/144\); the last two carry weight \(41/144\). Their
weights sum to one. Twice a circle weight times its displayed corner
is, respectively, one of the force vectors

\[
(\omega,\alpha),\quad(\omega,\alpha),\quad
(\varepsilon,\omega),\quad(\varepsilon,\omega).
\]

Equivalently, before normalization the three edge weights are
\(24/41,1,36/31\). The circle-weight mass is \(1728/1271\).
These are exact geometric ratios, with no fitted decimal multipliers.

Weight the seven rows above, in cyclic order, by

\[
(\omega,\omega,\alpha,\omega,\omega,
  \varepsilon,\varepsilon).
\tag{5}
\]

The \(b_G\) and \(b_T\) terms cancel exactly. Define

\[
\begin{aligned}
\mathcal F={}&\omega c\,a_A+(\alpha+\omega r)b_A
  +\omega a_B+\alpha b_B\\
 &+\varepsilon a_D+\omega b_D
  +\varepsilon a_H+\omega b_H
  +\varepsilon[-a_Er+b_E(1-c)],\\
\mathcal B={}&3\omega+\alpha+\varepsilon
             +(\omega+\varepsilon)\frac{1+c+r}{2}.
\end{aligned}
\tag{6}
\]

All five aligned weights are at most \(\varepsilon\). Consequently,
the full weighted angular loss is bounded by

\[
L=\frac{1001}{1000}\varepsilon S+2\varepsilon S
 =\frac{3001}{1000}\varepsilon S.
\tag{7}
\]

This is a bound on the shared total mismatch, without any separate
signed-error alternatives. The necessary weighted inequality is
\(\mathcal B-L\le\mathcal F\).

## 3. Four circle completions and one quadrant estimate

Containment gives

\[
(a_i+1/2)^2+(b_i+1/2)^2\le q.
\tag{8}
\]

For positive \(\mu\), use only the elementary completed-square bound

\[
C(a+1/2)+D(b+1/2)
\le\mu q+\frac{C^2+D^2}{4\mu}.
\tag{9}
\]

Apply (9) to A, B, D, and H with forces

\[
(\omega c,\alpha+\omega r),\quad
(\omega,\alpha),\quad
(\varepsilon,\omega),\quad
(\varepsilon,\omega)
\]

and circle weights \(31/144,31/144,41/144,41/144\).

The E force needs no circle completion. Core avoidance and containment
already give the weaker sufficient bounds \(a_E\ge1/2\), \(b_E\le1\).
Because \(r\ge0\) and \(1-c\ge0\),

\[
\varepsilon[-a_Er+b_E(1-c)]
\le\varepsilon[-r/2+(1-c)].
\tag{10}
\]

Combining (6), (8)--(10) and \(c^2+r^2=1\), all center variables
cancel and leave the exact inequality

\[
q\ge\frac{2257}{576}
 +\varepsilon r
 -(\omega+3\varepsilon/2)(1-c)-L.
\tag{11}
\]

One can check (11) directly without an expansion table. The only varying
force norm is

\[
(\omega c)^2+(\alpha+\omega r)^2
=\omega^2+\alpha^2+2\alpha\omega r.
\]

Since \(\alpha=2(31/144)\), its contribution to (9) changes by
exactly \(\omega r\). Every other force norm is constant.

## 4. One chord inequality covers the entire half-chart

The half-angle identities give

\[
1-c=(-z)r\le\frac38r
\qquad(-3/8\le z\le0).
\tag{12}
\]

Therefore the nonconstant term in (11) is at least

\[
\left[\varepsilon-\frac38(\omega+3\varepsilon/2)\right]r
=\frac{451}{4608}r\ge0.
\]

This proves (1), and (2) completes the contradiction. All comparisons
are closed up to the final strictly positive rational reserve. In
particular, the support cusp at zero and either endpoint of the
half-angle chart create no additional case.

## 5. Dependency change and remaining work

`Candidate/GeometricOwners.lean` imports `Candidate/Nominal.lean` and
generic arithmetic/analysis dependencies, with no generated owner or
tilt tables. It also now owns the existing continuous projection
estimates formerly in `DualApplication.lean`.

`tilt_window` first calls the geometric theorem to obtain \(z>0\).
Its certificate lookup then uses only the remaining closed tails

\[
[0,1001/20000]\ \cup\ [2/25,3/8].
\]

The former `Tilt000.lean` through `Tilt017.lean` are removed, along
with their imports and entries in `tiltLeft`. This removes exactly
18 bundles, 378 quartics, 1,890 Bernstein coefficient checks, 16,740
generated Lean lines, and 1,136,918 bytes. The owner generator filters
these nonpositive bundles so regeneration cannot reinstate them.

The three chain arguments below remove 28 of the quarter-owner
patterns as well. There remain 20 quarter-owner patterns, 15 mixed-owner
patterns, and 41 positive tilt bundles. Their geometric replacements are
still open. In particular, the negative-tilt theorem uses the intended
owners; it does not by itself supply the quarter or mixed restrictions.

A useful warning for the positive-tail work is that freezing the
stationary stress at the sharp positive tilt does not give a lower
radius bound increasing away from that tilt. Exploratory evaluation
of that frozen stress gives a negative tilt Hessian. A replacement
there should use the primal five-corner chain, adaptive geometric
forces, or another provable whole-region inequality.

## 6. A primary span excludes an entire quarter-owner class

The second replacement is independent of the tilt sign and both mixed
owners. Assume the candidate frame, signed tangent cuts, zero-edge owner
restriction, \(q\le Q_0\), and \(S\le1/10\). Suppose an intended
owner (axis 3 or 4) is feasible on B to T, and a forbidden owner (axis 1
or 2) is feasible on D to E. Select any feasible owner on T to D; the
zero-edge restriction says it is axis 1 or 3.

The three nominal projections are, respectively,

\[
a_B-b_T,\qquad b_T+b_D,\qquad a_E-b_D.
\]

For any aligned edge, containment and the true separating inequality
give the exact per-edge estimate

\[
F_i^{\rm nominal}\ge1-\frac32|d_i|.
\tag{13}
\]

It follows from the center-amplitude bound and \(W\ge1\); no small
angle approximation or owner table is involved. Adding the three rows
telescopes both transverse coordinates and gives

\[
\boxed{a_B+a_E\ge3-\frac32
  (|d_B|+|d_T|+|d_D|)\ge3-\frac32S.}
\tag{14}
\]

On the other hand, canonical containment already gives
\(a_i<283/200\). Thus

\[
a_B+a_E<\frac{283}{100}
 <\frac{57}{20}
 \le3-\frac32S,
\]

which is a contradiction. At \(S=1/10\) the strict span reserve is
\(1/50\). The quarter-capture call only needs \(S\le3/200\), so it
satisfies this hypothesis with room to spare.

`Candidate/GeometricOwnersQuarter.lean` proves this as
`quarter_telescoping_primary_bound` and
`quarter_mixed_direction_excluded`. Its projection identities inspect
each of the four original axes. Hence a forbidden feasible D axis is
excluded even when another D axis is also feasible. The proof does not
assume a future quarter or mixed owner conclusion.

In the original 48-pattern quarter enumeration, the excluded class is

\[
(1,g,1,3,1,1,h),\qquad g,h\in\{1,2,3,4\}.
\]

If any forbidden quarter axis remains, every selected feasible B axis
must now be forbidden: this is immediate when the offending edge is B,
and follows from (14) when the offending edge is D. The remaining
complete pattern set therefore has only

\[
(1,g,1,1,1,d,h),\qquad
g,h\in\{1,2,3,4\},\ d\in\{1,3\},
\]

with exactly 32 patterns before the next geometric reduction.
`quarter_owners` derives this restriction before requesting any
certificate.

The removed modules are `Quarter008`--`Quarter011`,
`Quarter020`--`Quarter023`, `Quarter032`--`Quarter035`, and
`Quarter044`--`Quarter047`. They contain exactly 480 quartics, 2,400
Bernstein coefficient checks, 20,688 generated Lean lines, and
1,384,893 UTF-8 bytes. Their imports, owner-table entries, and generator
outputs have been removed. This step left 32 quarter groups and 1,065
quarter rows, before the reduction below.

Together the two geometric replacements remove 34 generated modules,
858 quartics, 4,290 Bernstein coefficient checks, 37,428 generated Lean
lines, and 2,521,811 bytes. These are source/dependency counts. No Lean
compilation or runtime claim is made.

## 7. One rotated corner removes another eight quarter patterns

Suppose a forbidden B-to-T axis is feasible, and G-to-A axis 3 is
feasible (axis `2` in Lean's zero-based indexing). No owner restriction
on D-to-E or E-to-H is needed. Write \(c=\cos t\) and \(s=\sin t\).
The actual G-to-A angle has no mismatch. Add its nominal projection to
the zero-edge A-to-B projection and the forbidden B-to-T projection:

\[
\begin{aligned}
&(a_Gc-b_Gs-b_A)+(b_A+b_B)+(a_T-b_B)\\
&\qquad=a_Gc-b_Gs+a_T\\
&\qquad\ge\frac{1+c+|s|}{2}+2-
  \frac32(|d_A|+|d_B|).
\end{aligned}
\tag{15}
\]

The cancellation is exact for either actual forbidden B axis and
either allowed zero-edge A axis. Since \(b_G\ge0\), replacing
\(-s\) by \(|s|\) only increases the rightward projection of G's
center. Complete its corner disk with circle weight \(1/4\):

\[
c(a_G+1/2)+|s|(b_G+1/2)
\le\frac q4+c^2+|s|^2=\frac q4+1.
\tag{16}
\]

Combining (15) and (16), using
\(c+|s|\ge1\) and \(|d_A|+|d_B|\le S\), gives

\[
\boxed{a_T+\frac q4\ge\frac52-\frac32S.}
\tag{17}
\]

The reusable lemma `rotated_corner_primary_span` proves the scalar
step on the entire closed right semicircle \(c\ge0\),
\(c^2+s^2=1\). Thus it covers both signs of the tilt, zero tilt,
and both closed endpoints of the original half-angle chart.
`G_axis_two_forbidden_quarter_bound` supplies its hypotheses directly
from actual square containment and feasible axes.

At the allowed mismatch \(S\le3/200\), the canonical primary bound
\(a_T<283/200\) contradicts (17). The exact strict reserve is

\[
\frac52-\frac32\frac3{200}-\frac{283}{200}
 -\frac14\frac{9789}{2500}
=\frac{209}{2500}>0.
\tag{18}
\]

This removes every pattern
\((1,3,1,1,1,d,h)\), where \(d\in\{1,3\}\) and
\(h\in\{1,2,3,4\}\), in the historical one-based axis labels.
The corresponding modules are `Quarter024` through `Quarter031`.
They contain 240 quartics, 1,200 Bernstein coefficient checks,
10,344 generated Lean lines, and 682,081 UTF-8 bytes.

The remaining exact quarter pattern family is

\[
(1,g,1,1,1,d,h),\qquad
g\in\{1,2,4\},\quad d\in\{1,3\},\quad
h\in\{1,2,3,4\}.
\]

Its completeness proof uses the direct index \(8g'+4d'+h'\), with
\(g'\in\mathrm{Fin}\,3\), \(d'\in\mathrm{Fin}\,2\), and
\(h'\in\mathrm{Fin}\,4\). It checks just these 24 concrete owner
vectors. The previous exhaustive decision over all functions
\(\mathrm{Fin}\,7\to\mathrm{Fin}\,4\) is removed.

All three replacements together delete 42 generated modules,
1,098 quartics, 5,490 Bernstein coefficient checks, 47,772 generated
Lean lines, and 3,203,892 bytes. The owner generator filters all three
excluded regions, and the generation index now has 24 quarter groups
with 825 rows, 15 mixed groups with 729 rows, and 41 positive tilt
bundles with 861 rows. Exact static checks confirmed the disjoint
48-pattern partition (16 plus 8 removed, 24 retained), all 24 direct
selector outputs, the reserve in (18), and the remaining source imports.
No Lean compilation or historical certificate replay was run.

## 8. Two forbidden directions force A toward its transverse side

Suppose both B-to-T and D-to-E have a forbidden feasible axis. The
zero-edge projections on A-to-B and T-to-D give two chains:

\[
b_A+a_T\ge2-\frac32(|d_A|+|d_B|),\qquad
b_T+a_E\ge2-\frac32(|d_T|+|d_D|).
\tag{19}
\]

Give the second chain weight \(2/3\), so the T force is
\((1,2/3)\). A circle completion with weight \(3/10\) gives

\[
a_T+\frac23b_T\le\frac3{10}q+\frac{10}{27}.
\tag{20}
\]

All four error coefficients are at most one. Consequently

\[
b_A\ge\frac{10}{3}-\frac32S-\frac23a_E
  -\frac3{10}q-\frac{10}{27}
\ge\frac{1110307}{1350000}>\frac{81}{100}.
\tag{21}
\]

Here the final comparison uses \(a_E<283/200\), \(q\le Q_0\),
and \(S\le3/200\). This is a geometric bound on the original A
center; no circle equality or approximate stationary position is
assumed. The Lean theorems are `double_forbidden_transverse_quantitative`
and `double_forbidden_transverse_bound` in
`Candidate/GeometricOwnersDouble.lean`.

Now suppose G-to-A axis 1 is feasible (axis `0` in Lean). Set
\(r=|\sin t|\), \(c=\cos t\). On the entire closed half-angle
chart, \(c\ge0\), \(c^2+r^2=1\), and

\[
\frac rc=\frac{2|z|}{1-z^2}\le\frac{48}{55}<\frac9{10}.
\tag{22}
\]

The statement used in Lean is the denominator-free inequality
\(r\le(9/10)c\), including both chart endpoints. A single
supporting line of A's corner disk, with force \((1,9/10)\) and
circle weight \(1/3\), gives

\[
a_A+\frac9{10}b_A
\le\frac q3+\frac{163}{400}
\le\frac{17127}{10000}.
\tag{23}
\]

Because \((9/10)c-r\ge0\), (21) and (23) imply

\[
\begin{aligned}
a_Ac+b_Ar
&\le\frac{17127}{10000}c-b_A\left(\frac9{10}c-r\right)\\
&\le\frac{9837}{10000}c+\frac{81}{100}r.
\end{aligned}
\tag{24}
\]

Add the actual G-to-A and nominal H-to-G inequalities. The G transverse
coordinate cancels; \(b_A\ge0\) permits replacing \(-\sin t\)
by \(r\). Since \(b_H<9/10\), this forces

\[
\frac35-\frac32|d_H|
\le\frac{4837}{10000}c+\frac{31}{100}r
\le\frac{23}{40}.
\tag{25}
\]

The last bound is a single support inequality for the unit direction
circle, since

\[
\left(\frac{23}{40}\right)^2-
 \left(\frac{4837}{10000}\right)^2-
 \left(\frac{31}{100}\right)^2
=\frac{55931}{100000000}>0.
\]

The source uses circle weight \(23/80\) to express this without a
square root. But \(|d_H|\le S\le3/200\), so (25) is impossible:

\[
\frac35-\frac32\frac3{200}-\frac{23}{40}
=\frac1{400}>0.
\tag{26}
\]

No E-axis assumption appears anywhere in this exclusion. Every actual
forbidden B or D axis, every allowed H, A or T zero axis, and every
simultaneously feasible G axis is treated with its original inequality.
`G_axis_zero_double_forbidden_excluded` therefore removes all four
modules `Quarter000` through `Quarter003`: 120 quartics, 600 Bernstein
coefficient checks, 5,172 generated Lean lines, and 346,353 UTF-8 bytes.

The remaining quarter selector has just five \((G,D)\) pairs, in
zero-based Lean indices: \((0,2),(1,0),(1,2),(3,0),(3,2)\).
For each pair E has four choices. The direct selector is \(4k+e\)
with \(k\in\mathrm{Fin}\,5\), \(e\in\mathrm{Fin}\,4\), and
the completeness proof explicitly establishes these five possibilities.
The 48 original patterns split disjointly as \(16+8+4+20\).

The cumulative owner/tilt deletion is now 46 modules, 1,218 quartics,
6,090 Bernstein checks, 52,944 generated Lean lines, and 3,550,245
bytes. Remaining owner inputs have 20 quarter groups with 705 rows,
15 mixed groups with 729 rows, and 41 positive tilt bundles with 861
rows. The generator excludes every removed class, the direct selector
was checked against all 20 retained source vectors, and the rational
support constants and reserves above were checked exactly. These are
uncompiled proof-source changes.
