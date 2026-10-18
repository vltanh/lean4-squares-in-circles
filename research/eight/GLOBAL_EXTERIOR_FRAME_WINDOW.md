# Global exterior-frame concentration: M5 and M6 are excluded

**Theorem, with exact computer assistance.** Let eight unit squares with
pairwise disjoint open interiors be contained in a disk of squared radius

\[
q\le Q:=9789/2500.
\]

There is a unique square containing the origin. The other seven square
frames, considered modulo \(\pi/2\), lie in a common open frame interval
of length \(\pi/4\). In fact they lie in an interval of length strictly
less than \(7/10\) radians.

Consequently the largest closed 45-degree frame window among all eight
squares contains at least seven labels. **The entire M5 and M6 branches
are impossible under the research ceiling.** This includes both folded
M5 types and every Jensen defect; the former small-J/diffuse split is not
a dependency of this proof.

This theorem is a global reduction, not unrestricted radius optimality.
M7 and M8 still require sharp lower bounds and equality classification.
The active exits are in [the gated roadmap](GATED_ROADMAP_2026_10_16.md).

## 1. Exact central-core input

[CENTRAL_CORE_CERTIFICATE.md](CENTRAL_CORE_CERTIFICATE.md) proves that
every eight-square packing at \(q\le98/25\) has a unique central square
whose open interior contains the closed disk of radius \(\rho=1/12\).
Since \(Q<98/25\), it applies here. Every other closed square stays at
distance strictly greater than \(\rho\) from the origin. Relax this to
distance at least \(\rho\).

The central-core theorem uses a complete exact dyadic certificate for
four continuous sign branches, followed by a hand counting argument.
It was replayed in this continuation with undefined-behavior checks:
the [retained replay](certificates/central_core/replay_2026_10_17.log)
reproduces all four published counts and strict margins. This is an
explicit computer-dependent premise until its hand conversion is supplied.

## 2. Preserve the actual exterior frame tour

Order the seven exterior centers by polar angle. Their radii obey

\[
7/12\le r_i<71/50.
\]

Every adjacent pair has center distance at least one. The elementary
corner maximum in
[CYCLIC_RADIAL_BOUNDARY_REDUCTION.md](CYCLIC_RADIAL_BOUNDARY_REDUCTION.md)
therefore gives every directed gap

\[
3/5<\delta_i<\pi,\qquad \sum_{i=0}^6\delta_i=2\pi.
\]

Keep all actual square frames fixed and retain the seven adjacent SAT
nonoverlap conditions. For one center, select an actual SAT witness on
each of its two incident edges. The two resulting affine halfplanes
have a nonzero common recession direction. Translate to the first
outer-disk or core boundary. This preserves both witnesses, the cyclic
order, and all frame differences. Repeat for each label.

The resulting seven-cycle consists entirely of outer-boundary states
(`O`) and core-boundary states (`C`). Nonneighbor overlaps are allowed
in this relaxation; the seven true neighbor SAT constraints remain.
The hand reduction covers every original packing and preserves

\[
U:=\sum_{i=0}^6(w_i-1),\qquad
w_i=\frac{1+|\cos(\theta_{i+1}-\theta_i)|
                  +|\sin(\theta_{i+1}-\theta_i)|}{2}.
\]

## 3. A complete continuous pair certificate

Parameterize a boundary state by \(t=\tan\alpha\in[-1,1]\), where
\(\alpha\) is its frame relative to its center ray. Split the outer
curve at \(|t|=1/4,3/7\), and keep the core as one type. There are four
types in total. Choose one type consistently at each shared endpoint.

The [four-type pair theorem](FOUR_TYPE_BOUNDARY_PAIR_CERTIFICATE.md)
supplies an explicit rational piecewise affine state potential \(\psi\)
and a symmetric rational matrix \(\Gamma\) such that every feasible
ordered pair satisfies

\[
\delta_i-\frac9{50}(w_i-1)+\psi_{i+1}-\psi_i
\ge\Gamma_{\tau_i,\tau_{i+1}}.
\]

All 40 closed type/sign branches were completed, including every pair
of the eight affine pieces. The certificate uses the true four square
SAT axes with both signs, exact radial roots, and outward 48-bit dyadic
enclosures with 128-bit products. No sampled pair cost is accepted as
a bound. Sources, exact constants, every branch log, and the manifest
are committed alongside the proof.

| Continuous-cover item | Completed total |
|---|---:|
| Type/sign branches | 40 |
| Initial closed piece rectangles | 2,560 |
| Tangent subdivision nodes | 3,746,056 |
| Terminal rectangles | 1,874,308 |
| Maximum subdivision depth | 24 |
| Largest accepted SAT upper bound | \(-53128/2^{48}<0\) |

Both the geometric acceptance rules and the completed source/data/log
binding have independent written audits. The [manifest](fourtype_pair_logs_checked/manifest.json)
has status `ALL BRANCHES PASSED`. The proof note gives build and replay
commands. Hand conversion of these continuous inequalities remains open.

## 4. A short hand seven-walk inequality

The [odd-cycle lemma](FOUR_TYPE_ODD_CYCLE_LEMMA.md) proves directly that
every closed seven-step walk on the four types satisfies

\[
\sum_i\Gamma_{\tau_i,\tau_{i+1}}\ge6209669/10^6.
\]

Its proof subtracts the smallest edge cost, then checks the four
triangles and self-loops of a four-vertex graph. It does not require a
computer enumeration. The state potentials telescope around the
physical seven-cycle, giving

\[
2\pi-\frac9{50}U\ge\frac{6209669}{10^6}.
\tag{1}
\]

The explicit rational estimates \(\sqrt2>239/169\) and
\(\pi<355/113\), proved in that note, yield

\[
\frac{6209669}{10^6}+\frac9{50}(\sqrt2-1)-2\pi
>\frac{19848893}{19097000000}>0.
\]

Combining with (1) proves \(U<\sqrt2-1\).

## 5. Frame-circle lifting closes M5 and M6

For geodesic frame distance \(d\in[0,\pi/4]\), the width excess is
\(h(d)=(\cos d+\sin d-1)/2\). Concavity gives

\[
h(d)\ge\frac{2(\sqrt2-1)}\pi d.
\]

Thus \(U<\sqrt2-1\) forces the seven-frame tour to have total geodesic
length less than the frame-circle circumference \(\pi/2\). Its
shortest signed increments have winding number zero, so they lift to
a closed real walk. A closed real walk with range \(D\) has variation
at least \(2D\). Hence \(D<\pi/4\), proving the common open window.
This elementary argument is written in
[FRAME_SEMICIRCLE_FORCING.md](FRAME_SEMICIRCLE_FORCING.md).

Using the sharper form of (1) and the metric triangle inequality for
\(h\), [EXTERIOR_FRAME_CONCENTRATION.md](EXTERIOR_FRAME_CONCENTRATION.md)
further proves

\[
U<\frac{8307403}{20340000},\qquad D<7/10.
\]

The central frame is unrestricted by this tour argument. Among all
eight frames a closed 45-degree window nevertheless contains the
seven exterior labels. This proves the announced M5/M6 exclusion.

## 6. Global radial patterns available for the next gate

The same complete pair theorem, strengthened by a hand core-to-core
bound, proves that a boundary representative cannot have adjacent `C`
states; see [NO_ADJACENT_CORE_BOUNDARY_STATES.md](NO_ADJACENT_CORE_BOUNDARY_STATES.md).
The binary seven-cycle therefore has five possible necklaces.

A second [complete continuous certificate](THREE_CORE_BOUNDARY_EXCLUSION.md)
excludes `COCOCOO`: six cross-edge costs plus one outer-edge cost give

\[
\sum_i\delta_i\ge\frac{3929}{625}
>\frac{710}{113}>2\pi.
\]

Its eight closed branches cover 512 initial rectangles, 754,058 nodes,
and 377,285 terminal rectangles. A third
[complete certificate](SHORT_TWO_CORE_BOUNDARY_EXCLUSION.md) excludes
the short-separation two-core word `COCOOOO`: all 28 directed role/sign
branches pass, and their seven costs sum to \(125709/20000>2\pi\).
This cover has 9,535,240 nodes and 4,768,516 terminal rectangles.
The full exact data and replay logs are retained. Every original packing
therefore has a boundary representative in one of the three words

| Radial pattern | Status at this checkpoint |
|---|---|
| `OOOOOOO` | Retained |
| `COOOOOO` | Retained |
| `COOCOOO` | Retained; includes the candidate topology after slider motion |

These are seven-state continuous families, not fully classified
contact graphs. Their exact physical angle sum and all seven true
neighbor SAT alternatives must remain in any terminal proof. The
new [uniform local sharpness theorem](HUMAN_UNIFORM_SLIDER_LOCAL_SHARPNESS.md)
includes the entire candidate-compatible slider rectangle, but its
neighborhood hypotheses must still be proved for every relevant
survivor. Global optimality and equality are still open.
