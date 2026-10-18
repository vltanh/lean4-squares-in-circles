# Owner geometry: seven complete table replacements

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

The six chain arguments below remove 40 of the quarter-owner
patterns as well. There remain eight quarter-owner patterns, 15 mixed-owner
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

## 9. All four E axes bound the negative tilt under a forbidden D direction

A forbidden feasible D-to-E axis gives

\[
a_E-b_D\ge1-\frac32|d_D|.
\]

Since \(b_D\ge0\) and \(S\le3/200\), it follows that
\(a_E\ge391/400>39/40\). The H tangent cone gives
\(b_H\ge a_H/2\), and containment gives
\(a_H\ge1/2\), hence \(b_H\ge1/4\).

Suppose the negative sine magnitude \(r=-\sin t\) were at least
\(9/20\). On the closed half-angle chart,
\(3/4\le c=\cos t\le1\) and \(r\le1\). The four nominal E
projections have the following upper bounds, where \(U=283/200\):

| E axis in Lean | Projection | Upper bound | Minimum gap below \(W-3/100\) |
|---|---|---|---|
| 0 | \(a_Hc-b_Hr-b_E\) | \(U(c-r/2)\) | \(787/8000\) |
| 1 | \(a_H-a_Er-b_Ec\) | \(U-(39/40)r\) | \(3/32\) |
| 2 | \(a_Ec-b_Er-b_H\) | \(Uc-1/4\) | \(3/100\) |
| 3 | \(a_E-a_Hr-b_Hc\) | \(U-r/2-c/4\) | \(27/400\) |

Here \(W=(1+c+r)/2\). Each last-column gap follows on the entire
rectangle \(c\in[3/4,1]\), \(r\in[9/20,1]\), without using a
particular relation between \(c\) and \(r\). For the first row,
\(c-r/2\ge0\) permits multiplying the primary upper bound by
that factor. Every discarded term has its sign justified by
\(b_E\ge0\), \(c\ge0\), and \(r\ge0\).

But every actual feasible E axis requires its nominal projection to be
at least \(W-2S\ge W-3/100\). Thus all four axes fail at once.
The direct theorem `forbidden_D_negative_tilt_bound` concludes

\[
\boxed{\sin t>-9/20}
\tag{27}
\]

for every forbidden feasible D axis. This argument includes the
boundary \(\sin t=-9/20\), all four original E axes, and all their
possible ties. Its source is `Candidate/GeometricOwnersTiltCone.lean`.

Now assume both quarter directions are forbidden. By (21),
\(b_A\ge81/100\), and the support (23) gives \(a_A\le1\).
If G-to-A axis 3 is feasible in Lean, its nominal projection is

\[
F_G=a_G-a_A\sin t-b_A\cos t\ge W.
\tag{28}
\]

For \(\sin t\ge0\), nonnegativity of \(a_A\) and
\(c\ge3/4\) give

\[
W-F_G\ge\frac12+\frac{131}{100}c-U
\ge\frac{27}{400}>0.
\]

For \(\sin t\le0\), (27) gives \(0\le r<9/20\).
The unit-circle identity then gives \(c\ge89/100\). Hence

\[
W-F_G\ge\frac12+\frac{131}{100}c-\frac r2-U
\ge\frac{259}{10000}>0.
\tag{29}
\]

Both signs contradict (28). No E owner was selected in advance, and
the proof does not rely on a future mixed-owner restriction.
`G_axis_three_double_forbidden_excluded` removes `Quarter036` through
`Quarter039`, containing 120 quartics, 600 Bernstein checks, 5,172
generated Lean lines, and 349,491 bytes.

There are now four remaining \((G,D)\) pairs:
\((0,2),(1,0),(1,2),(3,2)\), with four E axes each. The direct
quarter selector checks these 16 vectors. The separate mixed selector
now also avoids a decision over all owner functions: it orders the
16 mixed pairs by \(4g+e\), skips only the intended pair \((0,1)\),
and checks the remaining 15 source vectors explicitly.

The cumulative owner/tilt deletion is 50 modules, 1,338 quartics,
6,690 Bernstein checks, 58,116 generated Lean lines, and 3,899,736
bytes. The owner manifest has 16 quarter groups with 585 rows,
15 mixed groups with 729 rows, and 41 positive tilt bundles with
861 rows. The exact disjoint quarter partition is
\(48=16+8+4+4+16\). Both explicit selectors, all rational gaps,
the generator's filtering, and source imports were checked statically.
No Lean compilation or historical replay was run.


## 10. Every forbidden D axis is excluded by four short-arc chains

The last case with both quarter directions forbidden is G-to-A axis 1
in Lean. The A support (23) improves the primary bound to
\(a_A\le99/100\). If \(\sin t\ge0\), that G projection satisfies

\[
a_A-a_G\sin t-b_G\cos t\le99/100<1\le W,
\]

because \(a_G,b_G,\cos t\ge0\). Therefore \(\sin t<0\).
The all-axis E argument from Section 9 then gives
\(0<r=-\sin t<9/20\). The scalar proof deliberately uses the
closed, larger domain

\[
\frac34\le c,\qquad 0\le r\le\frac9{20},\qquad c^2+r^2=1.
\]

On this domain the following elementary chord bounds hold:

\[
\frac78\le c\le1,\qquad
1-c\le\frac8{15}r^2,\qquad 1-c\le\frac r4.
\tag{30}
\]

Indeed, \(c<7/8\) contradicts the unit-circle equation and
\(r\le9/20\). Then \(1+c\ge15/8\) gives the quadratic bound,
and \((8/15)r^2\le(6/25)r\le r/4\) gives the linear bound.
These statements are `short_negative_geometry` in
`Candidate/GeometricOwnersDoubleComplete.lean`.

The G projection and the H zero-edge projection now read

\[
a_A+a_Gr-b_Gc\ge W,\qquad
b_H+b_G\ge1-\frac32S,
\quad W=\frac{1+c+r}{2}.
\tag{31}
\]

Every actual E axis has its nominal projection from the table in
Section 9 at least \(W-2S\). Give the H inequality weight \(c\),
and give E weight one except in its axis-2 case, where its weight is
also \(c\). The G transverse coordinate always cancels. The exact
resulting forces and demands are as follows:

| E axis in Lean | Sum of coordinate forces | Demand before error |
|---|---|---|
| 0 | \(a_A+a_Gr+c a_H+(c-r)b_H-b_E\) | \(2W+c\) |
| 1 | \(a_A+a_H+c b_H+(a_G-a_E)r-b_Ec\) | \(2W+c\) |
| 2 | \(a_A+a_Gr+c^2a_E-crb_E\) | \((1+c)W+c\) |
| 3 | \(a_A+a_E+(a_G-a_H)r\) | \(2W+c\) |

The error in the first, second, and fourth rows is at most
\((2+3c/2)S\), and in the third row at most \(7cS/2\).
Since \(0\le c\le1\) and \(S\ge0\), every row loses at most
\(7S/2\). This uses the shared total mismatch, with no independent
error assigned to each nominal edge.

Write \(U=283/200\). We use only the original containment and cone
bounds

\[
a_A\le1,\quad a_G,a_E\le U,\quad
 a_E\ge39/40,\quad a_H\ge1/2,\quad b_E\ge0,
\]

and the H corner disk
\((a_H+1/2)^2+(b_H+1/2)^2\le q\).
For any real force \((x,y)\), its single circle completion with
weight \(1/3\) is

\[
x a_H+y b_H
\le\frac q3+\frac34(x^2+y^2)-\frac{x+y}{2}.
\tag{32}
\]

There is no sign restriction on \((x,y)\) in (32). The first row
uses \((x,y)=(c,c-r)\), and the second uses \((1,c)\).
After the primary-coordinate bounds and the unit-circle identity,
the direction terms needed for their respective gaps are

\[
\begin{aligned}
3c-\frac{183}{200}r+\frac34r^2+\frac32cr&\ge3,\\
\frac52c+\frac34r^2+\frac{14}{25}r&\ge\frac52.
\end{aligned}
\tag{33}
\]

The quadratic chord bound in (30), together with
\(cr\ge(7/8)r\) and \(r^2\le(9/20)r\), proves the first
line with residual at least \((3/200)r\), and the second with
residual at least \((119/400)r\). The discarded terms
\(-b_E\) and \(-b_Ec\) are nonpositive. Thus each of these
first two rows forces

\[
\frac72S\ge\frac32-\frac q3\ge\frac{487}{2500}.
\tag{34}
\]

For the third row, (30) gives

\[
(1+c)W+c\ge3,
\]

with residual at least \((17/80)r\). Also
\(r+c^2=1+r-r^2\le5/4\), so its force is at most
\(1+5U/4=443/160\); the discarded term \(-crb_E\) is
nonpositive because all three factors are nonnegative. Hence this
row forces \(7S/2\ge37/160\).

For the fourth row, its force is at most
\(1+U+(U-1/2)r\), so the gap is at least

\[
2c-U+(3/2-U)r\ge\frac{67}{200}.
\]

All sign uses have been stated: \(r,c,b_E\ge0\),
\(3/2-U=17/200>0\), and each primary bound is multiplied
only by \(r\), \(c^2\), or one. The four exact reserves after
subtracting the full mismatch loss \((7/2)(3/200)=21/400\)
are

\[
\frac{1423}{10000},\quad
\frac{1423}{10000},\quad
\frac{143}{800},\quad
\frac{113}{400},
\tag{35}
\]

respectively. Every reserve is strictly positive. Consequently every
actual E axis fails, and G axis 1 is excluded even when another E or
G axis is feasible simultaneously. No interval partition is used.

`G_axis_one_double_forbidden_excluded` combines this scalar proof with
the original projection inequalities. `double_forbidden_excluded`
then covers all four G axes: axes 0 and 3 use Sections 8 and 9, axis
2 uses Section 7, and axis 1 uses (30)--(35). Finally,
`D_quarter_owners` chooses any feasible B axis. Its intended case is
excluded by the primary span from Section 6, and its forbidden case
by `double_forbidden_excluded`. The result is the full geometric
restriction

\[
\boxed{\text{every feasible D-to-E axis belongs to the intended
quarter-owner set }\{2,3\}\text{ in Lean}.}
\tag{36}
\]

The hypotheses remain \(q\le Q_0\), the candidate frame and tangent
cuts, the previously established zero owners, and \(S\le3/200\).
There is no prerequisite quarter-owner, mixed-owner, or tilt-window
table. `quarter_owners` obtains (36) before its remaining lookup.

This removes `Quarter012` through `Quarter015`: 120 quartics,
600 Bernstein coefficient checks, 5,172 generated Lean lines, and
350,441 bytes. Combined with Section 9, the checkpoint removes eight
modules, 240 quartics, 1,200 Bernstein checks, 10,344 generated lines,
and 699,932 bytes. The final quarter selector has just the 12 vectors

\[
![0,g,0,0,0,2,e],\qquad g\in\{0,1,3\},\quad e\in\{0,1,2,3\},
\]

in the order \(4k+e\) for \(g=![0,1,3]_k\). The original 48
patterns split as 32 with forbidden D, four additional forbidden-B
patterns with G axis 2 and intended D, and these 12 retained patterns.
The remaining source modules are `Quarter004`--`Quarter007`,
`Quarter016`--`Quarter019`, and `Quarter040`--`Quarter043`.

Cumulatively, the six owner/tilt replacements remove 54 generated
modules, 1,458 quartics, 7,290 Bernstein coefficient checks, 63,288
generated Lean lines, and 4,250,177 bytes. The manifest now has 12
quarter groups with 465 rows, 15 mixed groups with 729 rows, and 41
positive tilt bundles with 861 rows. Exact static checks verify the
four force identities, direction residuals and reserves, all 12
quarter selector outputs and all 15 mixed selector outputs, the
48-pattern partition, generator filtering, manifest counts, and
resolved source imports. No Lean compilation or historical replay
was run.


## 11. The H corner gives a global short arc and removes every G-axis-3 quarter pattern

The H cone has \(b_H\ge a_H/2\). At the test corner
\((29/25,29/50)\), the squared radius exceeds the permitted ceiling by

\[
\left(\frac{29}{25}+\frac12\right)^2+
\left(\frac{29}{50}+\frac12\right)^2-Q_0
=\frac4{625}>0.
\tag{37}
\]

Thus the original H corner disk and its cone imply
\(a_H\le29/25\). This is `H_primary_twenty_nine`; its underlying
`corner_primary_twenty_nine` only needs a transverse coordinate at
least \(29/50\). No contact equality is assumed.

### A short negative arc before any owner restriction

Set \(L=447/800\), \(V=29/25\), and \(U=283/200\).
Containment and the H cone give

\[
L\le a_H\le V,\quad b_H\ge a_H/2\ge L/2,
\quad L\le a_E\le U,\quad b_E\ge0.
\]

On the entire rectangle \(3/4\le c\le1\),
\(3/8\le r\le1\), all four nominal E projections fail:

| E axis in Lean | Projection upper bound | Minimum gap below \(W-3/100\) |
|---|---|---|
| 0 | \(V(c-r/2)\) | \(43/200\) |
| 1 | \(V-Lr\) | \(21/256\) |
| 2 | \(Uc-L/2\) | \(7/320\) |
| 3 | \(U-Lr-(L/2)c\) | \(117/3200\) |

Here \(W=(1+c+r)/2\). The first bound uses
\(c-r/2\ge0\) and \(b_H\ge a_H/2\); the other three
use only products of the stated nonnegative factors. Every actual
E axis requires its nominal projection to be at least
\(W-2S\ge W-3/100\). Consequently

\[
\boxed{\sin t>-3/8}
\tag{38}
\]

holds for every candidate frame with \(q\le Q_0\), tangent cuts,
and \(S\le3/200\). Neither zero owners, quarter owners, nor mixed
owners are assumed in `global_negative_tilt_bound`. The excluded
boundary \(\sin t=-3/8\) has a strict reserve in every E case.

### A forbidden B axis first bounds A

The A zero edge followed by a forbidden B edge gives

\[
b_A+a_T\ge2-\frac32(|d_A|+|d_B|).
\]

The original T cone contains \(a_T\le349/250\), hence

\[
b_A\ge2-\frac32\frac3{200}-\frac{349}{250}
=\frac{1163}{2000}>\frac{29}{50}.
\]

Equation (37), now applied to A, gives \(a_A\le29/25\).
This is `forbidden_B_A_coordinates`; it spends only the actual A and
B errors before bounding their sum by \(S\).

Suppose G axis 3 in Lean is feasible. If \(\sin t\ge0\), then
\(a_A\ge0\), \(c\ge3/4\), and \(a_G\le U\) imply

\[
a_G-a_A\sin t-b_Ac
\le U-\frac{29}{50}\frac34=\frac{49}{50}<1\le W.
\]

This is impossible with reserve \(1/50\). Thus \(\sin t<0\),
and (38) leaves only the closed scalar domain

\[
0\le r\le3/8,\qquad c\ge3/4,\qquad c^2+r^2=1.
\tag{39}
\]

It also gives \(9/10\le c\le1\) and
\(1-c\le(4/7)r^2\). The first follows from
\(c^2=1-r^2\ge55/64>(9/10)^2\). The second follows from
\((1-c)(1+c)=r^2\) and \(1+c\ge7/4\).

### One four-circle stress covers all four E axes

The D axis is already captured geometrically by (36). Give the seven
nominal separation inequalities the following weights:

\[
(\lambda_H,\lambda_G,\lambda_A,\lambda_B,
 \lambda_T,\lambda_D,\lambda_E)
=\left(\frac25,1,c,c,\frac25,\frac9{20},\frac9{20}\right).
\tag{40}
\]

The A and B projections telescope, cancelling the B transverse
coordinate and the negative A transverse force from G. Write
\(w=2/5\), \(e=9/20\). The common part of the force is

\[
(a_G+w b_G)+r a_A+(c a_T+w b_T)+(e a_D+w b_D).
\]

The following four additional forces are the exact contributions of
H and E, after including D's positive E transverse term:

| E axis in Lean | Additional force |
|---|---|
| 0 | \(ec a_H+(w-er)b_H\) |
| 1 | \(e a_H+w b_H-er a_E+e(1-c)b_E\) |
| 2 | \((w-e)b_H+ec a_E+e(1-r)b_E\) |
| 3 | \(-er a_H+(w-ec)b_H+e a_E+e b_E\) |

The common demand is

\[
D(c,r)=\frac{29}{20}W+2c+\frac54.
\]

All aligned weights in (40) are at most one and nonnegative on (39).
Thus their true weighted absolute errors cost at most \(3S/2\),
and the E error costs at most \(2eS=9S/10\). The complete loss is
therefore \(12S/5\). This is the explicit `shared_loss` proof;
it does not spend a fresh total mismatch budget on each edge.

Complete four original corner circles, using weight \(11/40\) on
G and T and weight \(3/20\) on D and either H or E. The force
directions are

| Circle | Force direction |
|---|---|
| G, all cases | \((1,w)\) |
| T, all cases | \((c,w)\) |
| D, all cases | \((e,w)\) |
| H, E axis 0 | \((ec,w-er)\) |
| H, E axis 1 | \((e,w)\) |
| E, E axis 2 | \((ec,e(1-r))\) |
| E, E axis 3 | \((e,e)\) |

Their circle weights sum to \(17/20\). Each is a direct instance
of the supporting inequality

\[
x a+y b\le\mu q+\frac{x^2+y^2}{4\mu}-\frac{x+y}{2}.
\tag{41}
\]

For E axis 1, the remaining E terms are bounded using
\(a_E\ge L\), \(b_E\le9/10\), \(r\ge0\), and
\(1-c\ge0\). For E axis 2, the remaining H term is
\(-(1/20)b_H\le0\). For E axis 3, its transverse H term is
nonpositive because \(c\ge9/10\) gives \(w-ec<0\), and
its primary H term is at most \(-eLr\). Every case uses
\(r a_A\le(29/25)r\). No sign assumption on a circle force
itself is needed for (41).

For reproducibility, after these coordinate bounds and
\(c^2=1-r^2\), the four resulting lower bounds on demand minus
force are

\[
\begin{array}{c|l}
0&\displaystyle \frac{241}{1320}+\frac{69}{20}c-\frac3{50}r+
 \frac{10}{11}r^2-\frac{17}{20}q\\[2pt]
1&\displaystyle \frac{17}{6600}+\frac{363}{100}c-\frac{2937}{16000}r+
 \frac{10}{11}r^2-\frac{17}{20}q\\[2pt]
2&\displaystyle \frac{361}{2640}+\frac{69}{20}c+\frac3{200}r+
 \frac{10}{11}r^2-\frac{17}{20}q\\[2pt]
3&\displaystyle \frac{191}{528}+\frac{129}{40}c-\frac{2937}{16000}r+
 \frac{10}{11}r^2-\frac{17}{20}q.
\end{array}
\tag{42}
\]

Substitute \(c\ge1-(4/7)r^2\), \(r\le3/8\),
\(r^2\le9/64\), and \(q\le Q_0\); discard the positive
linear term in case 2. This gives the respective exact lower bounds

\[
\frac{556183}{4200000},\quad
\frac{4813153}{67200000},\quad
\frac{458183}{4200000},\quad
\frac{3920153}{67200000}.
\]

Every one exceeds \(1/20\). The lemma
`ForbiddenBStress.four_circle_gap` therefore gives one common gap
\(D-F\ge1/20\). Comparing this with the entire true error loss
produces the exact contradiction

\[
\frac1{20}-\frac{12}{5}\frac3{200}=\frac7{500}>0.
\tag{43}
\]

`G_axis_three_forbidden_B_excluded` covers both signs of tilt and
all four original E axes, including all feasible-axis ties. Its
source is `Candidate/GeometricOwnersForbiddenB.lean`.

This removes `Quarter040` through `Quarter043`: four modules,
120 quartics, 600 Bernstein coefficient checks, 5,172 generated
Lean lines, and 343,769 bytes. The remaining quarter selector is
\(![0,g,0,0,0,2,e]\) with \(g\in\{0,1\}\) and all four E
axes, so it checks eight concrete vectors. Its source bundles are
`Quarter004`--`Quarter007` and `Quarter016`--`Quarter019`.

Cumulatively, the seven owner/tilt replacements remove 58 generated
modules, 1,578 quartics, 7,890 Bernstein checks, 68,460 generated
Lean lines, and 4,593,946 bytes. The owner manifest has eight quarter
groups with 345 rows, 15 mixed groups with 729 rows, and 41 positive
tilt bundles with 861 rows. Exact static checks verify the four
weighted force identities, the scalar bounds and reserves, both
small selectors, the 48-pattern partition, generator filtering,
manifest counts, and resolved source imports. These remain uncompiled
proof-source changes; no historical certificate replay was run.
