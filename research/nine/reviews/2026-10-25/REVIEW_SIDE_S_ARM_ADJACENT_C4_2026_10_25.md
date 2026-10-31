# Independent review: the complete side-normal S arm with adjacent C4 loads

**Verdict: PASS.** This is an independent full hand review of
`SIDE_S_ARM_ADJACENT_C4_EXCLUSION.md`, including its physical channel,
radial-arm, circle-shadow and original finite-cover dependencies.
The entire existing gate
**M6.B4L2.C4.CHAIN.LBC.S_SIDE** is excluded over its full original
radius window. No other arm type, load orbit, attachment parent or
coarse cell is closed by this review.

The reviewed source has SHA-256
`2cc6d94216ad4db8bda3d11402207431587271e9c7f53d90c65c27d451b44224`.
The review date is 2026-10-25. No source proof was changed by the
reviewer, and no roadmap was edited.

## 1. Exact original scope

The original gate is the six-body positive component

\[
 A-B-C-D-A,\qquad A-U-L,
\]

with a genuine radial S leaf \(L\), a true unloaded side-normal
transmitter \(U\), and exactly \(B,C\) positively loaded among
the C4 vertices. The reflection interchanging \(B,D\) is already
part of this gate. The actual degrees are

\[
 \deg A=3,\quad
 \deg B=\deg C=\deg D=\deg U=2,\quad
 \deg L=1.
\]

This is exactly the arm/load/width domain in
`FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md`, Sections 1 and 3.1,
and the original checklist description. All three other physical
units remain in the nine-square packing. All shared-side means,
possible zero individual circle-corner weights, endpoint applications
and positive body-pair forces remain. No unloaded degree-two equation
is imposed on the true degree-three root \(A\).

The source works throughout

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\quad
 T=\sqrt{R^2-\frac14},\quad d=T-1,\quad\delta=T-2.
\]

No canonical-minimizer hypothesis is added. The selected physical
certificate and its original genuine-leaf conclusions are the same
ones used in the finite cover.

## 2. The two channels keep their actual applications

The genuine S leaf is

\[
 L=[d,d+1]e+[-1/2,1/2]Je.
\]

Its actual inner force application is \(de\). At the true unloaded
side-normal \(U\), force and torque balance give opposite parallel
forces on a single line, with a displacement of exactly one between
their actual applications. Thus the application on \(A\) is
\(\delta e\), and \(A\) is supported in
\(e\cdot x\le\delta\). This is a consequence of the real arm;
the source does not replace a free mean by a midpoint or assume
that \(A\) has the frame of \(U\).

The other true unloaded vertex \(D\) transmits between \(A,C\).
The actual physical unit \(B\) touches both endpoints. Sections
1--2 of `UNIT_BYPASS_NORMAL_CHANNEL.md` therefore reduce its
reserve to one. The diagonal alternative is genuinely excluded:
equality in the unit-bypass diameter bound would give two parallel
diagonal units with transverse center distance at most one, while
interior disjointness requires at least \(\sqrt2\).

Consequently the actual applications and support inequalities are

\[
 p_C-p_A=n,
 \qquad A\subseteq\{n\cdot x\le\alpha\},
 \qquad C\subseteq\{n\cdot x\ge\alpha+1\}.
\]

This implication has unrestricted endpoint degrees. Both physical
contacts to the bypass, including endpoint contacts and shared sides,
are allowed. No force or torque equation at \(B\) is substituted
for an endpoint equation.

## 3. The center bound and the full lower interval

For a contained unit square with center \(c\) and orthonormal
side axes \(u,v\), its farthest corner gives

\[
 R^2\ge |c|^2+\frac12+|c\cdot u|+|c\cdot v|
       \ge |c|^2+|c|+\frac12.
\]

Solving the quadratic yields \(|c|\le d+1/2\). Every unit-square
directional halfwidth is at least \(1/2\). Thus the channel gives

\[
 \alpha+\frac32\le n\cdot c_C\le|c_C|\le d+\frac12,
 \qquad\alpha\le\delta.
\]

For \(\delta<0\), the retained point \(\delta e\in A\) also
gives

\[
 \alpha\ge\delta(n\cdot e)\ge\delta.
\]

The sign reversal in the last inequality is correct. Both chains
must be equalities. Since \(\delta<0\), equality forces \(n=e\).
Equality in the center chain forces

\[
 c_C=(d+1/2)e,\qquad H_C(e)=1/2.
\]

The second equality forces a square side axis parallel to \(e\):
for an orthonormal side frame the halfwidth is
\((|e\cdot u|+|e\cdot v|)/2\), whose minimum is attained only
when one component is zero. The center and frame therefore fix
the entire square as

\[
 C=[d,d+1]e+[-1/2,1/2]Je=L.
\]

These are two distinct original physical units, so their identical
open interiors contradict packing disjointness. This excludes every
negative \(\delta\), with no force-ratio, owner or circle-mask
restriction.

## 4. The full upper interval and the geometric detour theorem

The original radius window gives \(\delta<1/60\). For
\(\delta\ge0\), apply the inward support-segment lemma from
`RADIAL_BRIDGE_AND_LEAF_REDUCTION.md`, Lemma 3.1, to the actual
support point \(p=\delta e\) of \(A\). The entire segment
\(p-te\), \(0\le t\le1\), lies in \(A\), including all
vertex, side-interior and side-endpoint support types. Taking
\(t=\delta\) gives \(O\in A\).

This exactly satisfies the only central-location input of
`FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md`, Theorem 4.1:

\[
 \operatorname{dist}(O,A)\le\max(\delta,0).
\]

That theorem is stated and proved for arbitrary endpoint units
of a physical normal channel of reserve at least one. It does not
require that the initial endpoint have a direct leaf or positive
degree two, nor that the far endpoint be circle-loaded. Its bypass
needs only physical circle contact. The actual \(A-D-C\) channel
and the positively loaded physical unit \(B\) meet these inputs.

I checked the complete geometric theorem rather than relying on
its C4-with-direct-leaf title. Its proof first obtains
\(-\delta\le\alpha\le\delta\) and \(R\ge\sqrt{17}/2\).
Every point of the far endpoint then has \(n\)-projection greater
than \(59/60\). Its orientation-independent narrow-cap lemma gives

\[
 \angle(n,p)<\beta=\arctan(13/20)
\]

at a far-endpoint/bypass contact \(p\). At a root/bypass contact
\(q\), the bypass's circle contact and unit diameter give
\(|q|>3/5\), whereas \(n\cdot q\le\delta<1/60\). Hence

\[
 \angle(n,q)>\arccos(1/36).
\]

The local circle-shadow theorem used next is Section 2 of
`BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md`. That section proves for
**every single circle-touching unit**, without a seven-cycle or a
degree assumption, that its shadow is shorter than
\(\omega=\arctan(23/16)\) at \(R\ge\sqrt{17}/2\). I checked
both side-frame cases \(b\ge1\) and \(1/2\le b\le1\),
including the equality endpoint \(b=1\). Thus
\(\angle(p,q)<\omega\), and the angular triangle inequality
contradicts the preceding lower bound because

\[
 \beta+\omega<\pi/2,
 \qquad
 \cos(\beta+\omega)=\frac{21}{\sqrt{446665}}>\frac1{36}.
\]

The strict numerical bounds are exact. For example,

\[
 (121/60)^2-(1105/256-1/4)=31/57600>0,
\]

and the final squared comparison is
\(756^2-446665=124871>0\). The narrow-cap lemma's reserve is
\(4633/180000>0\), and the two shadow cases have strict rational
reserves after squaring their positive sides. No empirical angular
grid is involved.

The case \(\delta=0\) lies directly in this argument: its actual
root support point is the origin. No limiting, perturbation or
certificate reselection step is needed.

## 5. Exact acceptance and limits

The two intervals \(\delta<0\) and \(\delta\ge0\) cover
the complete original **M6.B4L2.C4.CHAIN.LBC.S_SIDE** gate, including
its reflected CD representative. The proof excludes the actual
six-body core while preserving all nine units, so no completion
capacity calculation is needed.

The proof does not exclude the other arm widths/types, the BD or
BCD block-load domains, a full C4-arm attachment parent, or the
coarse C1.4.b2 cell. No new gate, polynomial packet, computational
certificate, Lean compilation or CI run is introduced.

Reviewed dependency hashes:

| Source | SHA-256 |
| --- | --- |
| `FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md` | `e90f5724065c9b65d2a3938f65a76820168d7448194cd0f716f01430588cb7d8` |
| `BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md` | `b768db590361b6fca9a7a89b3acbbcb351579968b88139bbf48ab106a9b7afcf` |
| `UNIT_BYPASS_NORMAL_CHANNEL.md` | `d6008ceb18b2c8921c1f3711e6babfea3a01761487352ef4dca60579a83353b8` |
| `FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md` | `2432860117c06c4ce46075dacf41cebc5a642fb368a45aa85da1f19f99776581` |
| `RADIAL_BRIDGE_AND_LEAF_REDUCTION.md` | `6154eee2ab1114d063b0dbd1a2800c3522cbb1b46ec44a258c1c89d8ffb9e975` |

