# Candidate mismatch: from 13/50 to 1/10

**Status: complete.** The continuous support argument, complete closed
state/angle covers and exact cyclic contraction below are proved. The
fixed coefficient replay and independent assembly audit both pass on the
immutable inputs bound in the companion manifest.

## 1. Conditional statement with no owner or A/B sign assumption

Set

\[
Q=\frac{1957767069}{500000000}=3.915534138,
\qquad (H,G,A,B,T,D,E)=(0,1,2,3,4,5,6),
\qquad k=(0,1,0,1,0,1,1).
\]

Consider an admissible seven-square radial-boundary neighbor cycle at Q.
The previously established frame lifts and physical center angles satisfy

\[
\sum_i\delta_i=2\pi,\qquad \delta_i>19/25,\qquad
\phi_i=\delta_i+\alpha_{i+1}-\alpha_i=k_i\pi/2+d_i,
\qquad |d_i|\le7/10.
\tag{1}
\]

Each adjacent pair has an actual feasible retained forward canonical SAT
separator. Every vertex may independently have core or outer radial kind.
Assume these closed signed tangent domains:

| Role | Domain for u = tan(alpha) |
|---|---|
| H | [1/2,1] |
| G | [-4/5,-1/20] |
| A | [-1,1] |
| B | [-1,1] |
| T | [1/20,4/5] |
| D | [-1,-1/2] |
| E | [-1,0] |

Write

\[
I=\{0,2,3,4,5\},\qquad S=\sum_{i\in I}|d_i|.
\tag{2}
\]

**Theorem.** Under the preceding
hypotheses,

\[
S\le\frac{13}{50}\quad\Longrightarrow\quad S<\frac1{10}.
\tag{3}
\]

The G/T/H/D domains are supplied by the earlier tangent exclusion
theorems, and E by reflection normalization. The full-SAT coarse table
and its printed-reserve corollary supply S<13/50. This theorem assumes
neither the signs of A and B nor a preferred separating axis, including
on the three zero-quarter edges. All four original axes are covered.

The statement is about the boundary representative at Q. The fixed-ceiling
transfer treats an original packing separately; in particular no tangent
preservation is attributed to the initial radial deformation.

## 2. The closed state arcs and the charged pair expression

In a square's canonical frame write its center as (a,-sigma b), where
0<=b<=a, sigma is +1 or -1, v=b/a and u=sigma v. The two boundary
curves are

\[
\begin{array}{ll}
O:&(a+1/2)^2+(b+1/2)^2=Q,\\
C:&a=7/12\quad(0\le v\le6/7),\\
 &(a-1/2)^2+(b-1/2)^2=1/144\quad(6/7\le v\le1).
\end{array}
\tag{4}
\]

The input `MISMATCH_026_TO_01_AFFINE_HAND_DATA.json` gives 401 closed
rational arcs covering all 18 nonempty role/kind/sign domains in the
statement. Both signs of A and B are retained, including their common
zero endpoint. Each arc carries a rational affine label L=c+pa+qb.
Every core arc remains in its side or corner domain, split at the exact
junction 6/7. A vertex at any shared endpoint chooses one containing
arc once, and uses its label on both incident edges. Every such pair
of choices is included in the table.

Put

\[
\gamma=\frac{448791}{500000}=.897582,
\qquad \beta_i=\begin{cases}1/400&i\in I,\\0&i\notin I,\end{cases}
\qquad h(x)=\frac{\sin x+\cos x-1}{2}\quad(0\le x\le.7).
\tag{5}
\]

The table's pair conclusion is

\[
\phi_i-\beta_i h(|d_i|)+L_i-L_{i+1}>\gamma.
\tag{6}
\]

For a source (a,-sigma b) and target R_phi(A,-tau B), let
W=(1+|sin(phi)|+|cos(phi)|)/2. The four retained margins, in their
original directed order, are

\[
\begin{aligned}
M_1&=\sigma b+A\sin\phi-\tau B\cos\phi-W,\\
M_2&=A-a\cos\phi+\sigma b\sin\phi-W,\\
M_3&=a\sin\phi+\sigma b\cos\phi-\tau B-W,\\
M_4&=a-A\cos\phi-\tau B\sin\phi-W.
\end{aligned}
\tag{7}
\]

Each fixed row supplies a rational lambda>=0 and proves

\[
\phi-\beta_i h(|d_i|)+L_s-L_t-\gamma-\lambda M_j>0
\tag{8}
\]

on its entire source arc, target arc and fixed angle interval. Actual
separation means M_j>=0, so (8) implies (6). The charge is attached to
the original edge. Reversing and reflecting axes 2 and 3 leaves its
value unchanged, because |sin(phi)|+|cos(phi)| is even and has period
pi/2. No charge is transferred onto either uncharged mixed edge.

## 3. Continuous elimination and fixed polynomial inequalities

The independently reviewed `AFFINE_ARC_ONE_ANGLE_HAND_KERNEL.md` proves
the reduction of (8) to univariate polynomial inequalities. Subtracting
lambda M_j separates the two coordinate minima. The source minimum has
constant coefficients. The target is bounded by a monotone endpoint,
both endpoints of a concave arc, or the support of the entire circle;
straight core sides use endpoints. The derivative or concavity
conditions required by each choice are part of that row's fixed
polynomial premises.

For a circle with center (a0,a0) and radius r0,

\[
Xa+Yb\ge a_0(X+Y)-r_0\sqrt{X^2+Y^2}.
\tag{9}
\]

The radical uses the global majorant, valid for V>=0 and rational z>0,

\[
\begin{split}
T_z(V)&=\frac{5z+15V/z-5V^2/z^3+V^3/z^5}{16},\\
T_z(V)-\sqrt V
&=\frac{(\sqrt V-z)^4(V+4z\sqrt V+5z^2)}{16z^5}\ge0.
\end{split}
\tag{10}
\]

On each declared angle interval write phi=k pi/2+r x with r in {-1,1}
and 0<=x<=.7. Alternating sine and cosine bounds through degrees 9 and
10 give rational lower polynomials for (8) and its support premises.
For a polynomial P on [l,l+w], expand P(l+w t)=sum_j a_j t^j and put

\[
b_k=\sum_{j=0}^k a_j\frac{\binom{k}{j}}{\binom nj}.
\]

Then

\[
P(l+w t)=\sum_{k=0}^n b_k\binom nk t^k(1-t)^{n-k}.
\tag{11}
\]

Nonnegative b_k prove a premise on the whole closed interval; strictly
positive b_k prove a strict cost. The frozen checker performs this exact
rational arithmetic on the supplied finite rows. It performs no search,
optimization or adaptive subdivision. The numerical fit and the
discovery history are not inputs to the mathematical proof.

## 4. Complete angle cover before axis normalization

Equation (1) gives delta_i<710/113-114/25. If the signed source and
target arc angles range over [s-,s+] and [t-,t+], every actual relative
angle belongs to

\[
[19/25-s_++t_-,\;710/113-114/25-s_-+t_+]
\cap[k_i\pi/2-\rho_i,k_i\pi/2+\rho_i],
\tag{12}
\]

where rho_i=13/50 on I and rho_i=7/10 on the two mixed edges. These
restrictions are declared for each original directed edge before any
axis reversal. The possible interval is separated into its two closed
sign halves at k_i pi/2. An isolated endpoint, including zero, remains
part of the required cover.

The conditional kernel uses outward rational arctangent and pi brackets
to cover the full necessary domain (12). It checks every original
source/target arc pair and all four original axes. Its explicit
`difference_ranges` are precisely the seven closed intervals just
stated. The independent assembly reconstructs this union with a
different arctangent identity, so a sign reversal or lost endpoint
cannot be hidden by a cost-row replay.

The completed fixed table has the following exact totals:

| Object | Count |
|---|---:|
| Closed state arcs | 401 |
| Nonempty role/kind/sign domains | 18 |
| Original-axis angle chains | 123,168 |
| Fixed rows | 131,255 |
| Premise and cost polynomials | 354,398 |
| Rational coefficient lower bounds | 2,903,573 |

Every premise coefficient bound is nonnegative and every cost bound is
strictly positive. The least strict cost coefficient is
\(76173/20000000000000>0\). The decisive complete arithmetic output
has SHA-256

```
13a7dc18a78aaa4bbdeef9dc0d83b8f0098ba6c0e6e68ba55401d41849ef0f24
```

The frozen DATA has SHA-256

```
3230d71cdb3f1aa513aa74de04dc49429bb6ff2759a115cd55d98b160e1fedf4
```

The verifier is byte-identical to the previously independently reviewed
conditional affine-arc kernel,
`6af3d41fe7d404da7dd286c46644160f5444edd3028d864701266e9a4cd18697`.
The independent audit reconstructs all 18 state domains and all 123,168
original-axis angle chains using a different rational arctangent
identity. It binds the complete coefficient replay and independently
checks the exact contraction below. An additional scan verifies every
explicit coefficient list, its printed minimum and its ordered row
index. No incomplete report or unresolved row remains in this table.

## 5. A strict contraction by concavity

On [0,13/50], h is increasing and concave, since h'=(cos x-sin x)/2>0
and h''=-(sin x+cos x)/2<0. Also h(0)=0. If S>0, concavity gives

\[
h(|d_i|)\ge\frac{|d_i|}{S}h(S),
\qquad \sum_{i\in I}h(|d_i|)\ge h(S).
\tag{13}
\]

For S=0 conclusion (3) is immediate. Summing (6) with the same label
on each vertex's two incident edges, and using sum phi_i=2pi, gives

\[
2\pi>7\gamma+\frac1{400}\sum_{i\in I}h(|d_i|)
\ge7\gamma+\frac1{400}h(S).
\tag{14}
\]

If S>=1/10, monotonicity and the alternating bounds sin x>=x-x^3/6
and cos x>=1-x^2/2 imply

\[
h(S)\ge h(1/10)\ge
\frac1{20}-\frac1{400}-\frac1{12000}=\frac{569}{12000}.
\tag{15}
\]

But the exact rational comparison is

\[
7\frac{448791}{500000}+\frac1{400}\frac{569}{12000}
-\frac{710}{113}
=\frac{18173}{2712000000}>0.
\tag{16}
\]

Together with 2pi<710/113, this contradicts (14), proving (3).
No equality case is discarded: the contradiction is strict even at
S=1/10 and at every closed partition or sign boundary.

## 6. Interface to the next hand stage

Once (3) is established, the independently reviewed mismatch bootstrap
forces the signs H/A/T positive and G/B/D negative, and its earlier
zero-quarter argument gives only axes 1 or 3 on H->G, A->B and T->D.
The narrow theorem `MISMATCH_01_TO_015_AFFINE_HAND_THEOREM.md` then
applies: it retains all four axes, allows weaker H/D cones, and proves
S<3/200. The independently reviewed quarter-owner theorem subsequently
gives axes 3 or 4 on B->T and D->E before the final mismatch stage.
Thus no owner or A/B sign is used here to prove its own prerequisite.


## 7. Reproduction and immutable proof inputs

The exact inputs are `MISMATCH_026_TO_01_AFFINE_HAND_DATA.json` and the
frozen `verify_mismatch_026_to_01_affine_hand.js`. The supplied
`MISMATCH_026_TO_01_AFFINE_HAND_COMPACT_REPORT.json` retains every
polynomial degree and its strict or weak coefficient lower bound, as
well as the full output hash. The completed proof is independently
reviewed in `MISMATCH_026_TO_01_INDEPENDENT_AUDIT.md` and bound in
`MISMATCH_026_TO_01_AFFINE_HAND_MANIFEST.json`.

Run `python replay_mismatch_026_to_01_hand.py` to reproduce every
coefficient and compare the entire output and compact records. Add
`--save-full` to retain the optional large arithmetic output. Run
`python audit_mismatch_026_to_01_independently.py` to independently
reconstruct the exact state/angle/axis unions and cyclic contraction.
Neither procedure searches for an unlisted state or angle partition.
