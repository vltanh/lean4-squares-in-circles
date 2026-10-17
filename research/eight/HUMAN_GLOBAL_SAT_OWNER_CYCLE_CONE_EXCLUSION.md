# A global disk-native SAT-owner cycle obstruction: no directed 60-degree triangle

**Status: complete, unconditional-in-topology HAND THEOREM for the
eight-square search sublevel**, 2026-10-13. This is a genuine
pruning rule for the still-open full SAT-angle-owner program in
[GLOBAL_SAT_ANGLE_FIBER_DUALITY.md](GLOBAL_SAT_ANGLE_FIBER_DUALITY.md),
not another cap-offset threshold and not a complete sharp proof.

It eliminates whole DISCRETE SAT-owner words on an open angular
region, without searching any center coordinates, and works
for every square frame independently.

## Theorem (exact directed-cycle support cone obstruction)

Let \(S_1,\ldots,S_N\) be genuine unit squares of independent frames,
with disjoint open interiors, contained in a disk centered at zero
of squared radius \(R^2\le q_+=9789/2500\).
Let \(p_i\) be their centers.

For each directed edge \(i\to j\) of a chosen **simple cycle**
\[
i_1\to i_2\to\cdots\to i_k\to i_1,
\quad k\ge3,
\]
suppose we prescribe one ACTUAL TRUE square SAT-owner
unit normal \(n_i\in\{\pm e_{i},\pm f_{i},
\pm e_{i+1},\pm f_{i+1}\}\), oriented from its
edge's starting square toward its ending square, and
the corresponding genuine support separator holds:
\[
n_i\cdot(p_{i+1}-p_i)
\ge w_i:=H_{i}(n_i)+H_{i+1}(n_i)\ge1.
\tag{1}
\]
Then the following **center-free necessary inequality** holds:
\[
\boxed{
\sum_{i=1}^k w_i
< \frac{283}{200}
    \sum_{i=1}^k |n_{i-1}-n_i|,
\qquad n_0:=n_k.
}
\tag{2}
\]
The strict inequality applies whenever the cycle has nonzero
normal variation; if all normals agree the separators themselves
are immediately contradictory.

Two geometric consequences are especially simple:

**(A) Every directed three-square SAT owner cycle whose three
signed owner-normal directions lie in ONE closed angular arc
of width at most \(60^\circ=\pi/3\) is IMPOSSIBLE.**
Equivalently, among the genuine owner choices for any triangle
of squares, one cannot select a positively directed
three-cycle of separators whose directions all lie inside
a single \(60^\circ\) cone.

**(B) A directed SAT owner cycle of ANY length \(k\ge3\)
whose signed normal directions all lie in an angular arc
of width at most \(2/3\) radians is IMPOSSIBLE.**

These conclusions are valid for every square frame, every
center position, and any other six/five/... square labels
in the packing. They do not assume an outer-center
classification, central contact, or candidate topology.

## Proof

**Step 1: a strict, universal disk bound on true square centers.**

The four genuine vertex squared norms of a square of center p
and unit frame e,f are
\[
|p|^2+\tfrac12\pm p\cdot e\pm p\cdot f.
\]
Therefore disk containment forces
\[
R^2\ge |p|^2+\tfrac12+|p\cdot e|+|p\cdot f|
\ge |p|^2+|p|+\tfrac12,
\]
because the frame's two absolute projections have ℓ¹ norm
at least their ℓ² norm.

At \(r_0:=283/200\), an exact rational comparison gives
\[
r_0^2+r_0+\tfrac12-q_+
=\boxed{13/8000>0}.
\]
Since the left-hand radius expression increases in \(|p|\ge0\),
\[
\boxed{|p_i|<r_0=283/200
\quad\text{for every square center}.}          \tag{3}
\]

**Step 2: telescope a directed genuine SAT support cycle.**

Sum the \(k\) genuine directed inequalities (1):
\[
\begin{aligned}
\sum_i w_i
&\le \sum_i n_i\cdot(p_{i+1}-p_i)\\
&=\sum_i(n_{i-1}-n_i)\cdot p_i\\
&\le\sum_i|n_{i-1}-n_i|\,|p_i|\\
&<r_0\sum_i|n_{i-1}-n_i|
\end{aligned}                                               \tag{4}
\]
provided any coefficient is nonzero.
If all coefficients vanish, the right side of the first
inequality is identically zero, contradicting
\(\sum_iw_i\ge k>0\) even more directly.
This proves the generic owner rejection (2).

**Step 3: a 60-degree triangle cannot occur.**

For a three-edge cycle, the three coefficient norms in
(2) are the three **PAIRWISE CHORD lengths** between
the three signed owner normals.
Assume all their ray angles belong to a common (unwrapped)
arc of length \(\Theta\le\pi/3\).
Order the angles \(\alpha\le\beta\le\gamma\) in that arc.

For two unit vectors of angle difference d≥0,
their chord length is \(2\sin(d/2)\le d\).
Therefore
\[
\begin{aligned}
\sum_{\text{three pairs}}|n_i-n_j|
&\le(\beta-\alpha)+(\gamma-\beta)+(\gamma-\alpha)\\
&=2(\gamma-\alpha)\le2\pi/3.
\end{aligned}
\]
Using the elementary strict rational upper bound \(\pi<22/7\),
\[
r_0\sum|n_i-n_j|
\le\frac{283}{200}\frac{2\pi}{3}
<\frac{283}{200}\frac{44}{21}
=\frac{3113}{1050}
=3-\boxed{\frac{37}{1050}}
<3.
\]
But the three true unit-square support sums give
\(\sum_iw_i\ge3\), contradiction.
This proves (A), with a uniform rational reserve
at least \(37/1050\) before the additional positive
true-square support surplus.

**Step 4: narrow cones forbid all longer directed owner cycles.**

If the \(k\) edge-normal angles lie in a common unwrapped
arc of angular length \(\Theta\le2/3\),
every consecutive pair satisfies
\(|n_{i-1}-n_i|\le|\theta_{i-1}-\theta_i|
\le2/3\).
Equation (4) would imply
\[
k\le\sum_iw_i
<\frac{283}{200}\,k\,\frac23
=\frac{283}{300}k
=k-\frac{17}{300}k,
\]
a contradiction. This proves (B). QED.

## Exact rational nonparallel example

Choose three real unit-square frames via the *rational
half-angle tangents*
\[
z_A=0,\quad z_B=\tfrac14,\quad z_C=\tfrac12.
\]
Their genuine side normals are
\[
e_A=(1,0),\qquad
e_B=(15/17,8/17),\qquad
e_C=(3/5,4/5).
\]
The three angles span about 53 degrees; they are
**different true frames**, not an aligned ansatz.

Try the directed actual SAT-owner cycle
\[
A\xrightarrow{e_A}B,\quad
B\xrightarrow{e_B}C,\quad
C\xrightarrow{e_C}A.
\]
The three exact support sums are
\(\sum w_i=301/85\).
The three center-force coefficients
\[
e_C-e_A,\quad e_A-e_B,\quad e_B-e_C
\]
have squared Euclidean norms
\[
4/5,\quad4/17,\quad16/85,
\]
respectively. The rational norm upper bounds
\(9/10,\ 1/2,\ 9/20\) follow by positive
squaring and give
\[
r_0\sum_i|n_{i-1}-n_i|
\le\frac{283}{200}
 \left(\frac9{10}+\frac12+\frac9{20}\right)
=\frac{10471}{4000}.
\]
Thus an entirely rational, **strict contradiction** is
\[
\boxed{
\sum_iw_i-r_0\sum_i|n_{i-1}-n_i|
\ge\frac{301}{85}-\frac{10471}{4000}
=\frac{62793}{68000}>0.}                      \tag{5}
\]

[verify_global_sat_owner_cycle.py](verify_global_sat_owner_cycle.py)
checks all actual rational frames, signed true SAT owners,
support sums, claimed rational norm enclosures, and the
exact positive margin from
[global_sat_triangle_cycle_example.json](global_sat_triangle_cycle_example.json).

## Why this helps the ONE remaining global proof

The full eight-square SAT-angle reduction has at most
\(8^{28}\) raw signed pair-owner words; most are
mutually inconsistent before any center optimization.
The present theorem supplies a **cheap, rigorous
owner-word rejection rule**:

1. Given a candidate angular box and a chosen directed
   signed SAT owner for each pair, inspect each of the
   \(\binom83=56\) square triples.
2. If one of their three directed owner cycles has
   all signed normals in one certified 60-degree arc,
   reject the entire box/owner word **without branching
   any center variables**.
3. More generally apply the exact center-free
   inequality (2) directly; interval upper bounds
   on the normal coefficient norms and interval lower
   bounds on the true square supports give a sound
   rational certificate for any longer cycle.

An exploratory 2,000-word sample for each of three
frame scenarios rejected approximately **96.75%** of
random owner words for aligned/candidate-like frames,
and **98.8%** for randomly independent frames,
using the **three-cycle rule alone**. These figures
are **diagnostic**, not a worst-case theorem or a
complete proof cover. The sampling script
[computer_probe_global_owner_cycles.py](computer_probe_global_owner_cycles.py)
is labeled NONCERTIFYING.

The theorem is genuinely GLOBAL over all
square centers and frames satisfying the owner
cone hypothesis, but it does not prove the
whole unrestricted radius bound:
many owner words survive, and no finite
complete owner/angle cover has been executed.
The sharp candidate's legitimate SAT owners
must be retained in any exhaustive implementation.

**Status: an exact global SAT-owner reduction,
not the unrestricted \(R_8\ge\widehat R\).**
