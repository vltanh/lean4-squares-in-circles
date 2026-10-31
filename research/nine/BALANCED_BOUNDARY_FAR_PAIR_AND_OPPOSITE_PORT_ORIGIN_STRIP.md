# Balanced boundary loads and opposite unit ports force the origin into the port strip

Date: October 28, 2026.

**Status: complete proposed uniform hand reductions, frozen for full root
and separate independent review. No whole original H4 family is declared
excluded.**

All squares below are actual closed unit squares with disjoint open
interiors in the unchanged circle

\[
          79/40\le R\le\sqrt{1105}/16.
\]

All physical circle corners, nonnegative individual corner weights,
positive totals, original normals, real contact applications, shared-side
means and additional packing squares remain. The first two theorems are
independent of pair degrees and of local equilibrium equations.

Put

\[
 m=19/15,\qquad M=91/60,\qquad \sigma=1/\sqrt2,
 \qquad \theta=\arccos(9/25),\qquad
 \alpha=\pi-\theta/2.
 \tag{1}
\]

## 1. A touching pair among three balanced boundary loads has a far endpoint

Let B,C,E be three actual boundary squares with positive total circle
load and full outward resultants

\[
                    F_B+F_C+F_E=0.
\]

Suppose B and C physically touch. Then at least one of the actual minor
center angles between E and B,C is **strictly greater than** \(\alpha\).

The complete full-window metric proof
`GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md`,
Sections 2--3, gives the following degree-free facts, retaining every
physical mask and zero individual coefficient:

* Every actual boundary center radius belongs to \((m,M)\).
* Every circle resultant is nonzero and within \(\pi/12\) of its
  own center direction.
* The three resultant directions have the actual circular center order,
  and every consecutive directed center gap is strictly below
  \(7\pi/6\).

The physical contact BC has center distance at most \(\sqrt2\).
Since each boundary center radius is greater than \(5/4\), its minor
center angle \(g\) satisfies

\[
 \cos g
 =1-\frac{|c_B-c_C|^2-(|c_B|-|c_C|)^2}{2|c_B||c_C|}
 >9/25,
 \qquad g<\theta.
 \tag{2}
\]

This minor BC arc is a consecutive center gap. If it contained the E
direction, its complementary directed gap would exceed
\(2\pi-\theta>3\pi/2>7\pi/6\), contradicting the preceding gap
bound. No physical neighbor-order hypothesis beyond the stated metric
facts is needed for this step.

Suppose both minor E endpoint angles were at most \(\alpha\). If
one of their corresponding consecutive directed gaps were a major gap,
that gap would be at least

\[
 2\pi-\alpha=\pi+\theta/2>7\pi/6,
 \tag{3}
\]

since \(\theta>\pi/3\). This is impossible. A directed gap equal
to \(\pi\) is also impossible because \(\alpha<\pi\).
Consequently all three consecutive directed gaps are their minor gaps.
Their sum is at most

\[
                       g+2\alpha<\theta+2\alpha=2\pi,
\]

whereas the three consecutive gaps sum to \(2\pi\). This proves
the strict far-endpoint assertion. It does not discard a fourth load:
the balance of precisely B,C,E is an explicit hypothesis.

## 2. A wide boundary-center angle forces the circle origin between two ports

Let C,E be actual boundary squares containing actual points
\(P_C,P_E\), respectively, with

\[
 |P_C-P_E|=\sqrt2,
 \qquad e=(P_C-P_E)/\sqrt2.
\]

Assume the two actual centers project strictly outward from these
ports:

\[
 e\cdot(c_C-P_C)>0,
 \qquad e\cdot(c_E-P_E)<0.
 \tag{4}
\]

**Port-strip theorem.** If the minor angle between \(c_C,c_E\)
about the original circle origin O is at least \(\alpha\), then

\[
             e\cdot P_E<e\cdot O<e\cdot P_C.
 \tag{5}
\]

Here the points are not assumed to be selected force applications.
There is no owner, shared-side or neighbor-degree restriction in this
theorem, beyond its explicit whole-center projection premise (4).

Take O as the coordinate origin and e as the horizontal direction.
Suppose, to the contrary, that \(e\cdot O\ge e\cdot P_C\).
Every point of a unit lies within \(\sigma\) of its center, so

\[
 (c_C)_x\le\sigma,
 \qquad (c_E)_x< -\sqrt2.
 \tag{6}
\]

The second inequality uses (4) and the full port separation. Set

\[
 u=\arccos(\sigma/m),\qquad
 v=\arccos(\sqrt2/M).
\]

Since \(|c_C|>m\), (6) puts its angular distance from East strictly
above u. Its distance from West is therefore strictly below \(\pi-u\).
Since \(|c_E|<M\), the E direction has distance strictly below v
from West. The angular triangle inequality gives

\[
                 \angle(c_C,c_E)<\pi-u+v.
 \tag{7}
\]

Both u,v lie in \((0,\pi/2)\), and \(u>v\): indeed
\(\sigma/m<\sqrt2/M\) is equivalent to \(M<2m\).
The upper bound in (7) is thus strictly below \(\pi\).
Its cosine can be bounded entirely by exact arithmetic:

\[
\begin{aligned}
 \cos(\pi-u+v)
 &=-\frac{1+\sqrt{(m^2-1/2)(M^2-2)}}{mM},\\
 (m^2-1/2)(M^2-2)&=\frac{537257}{1620000},\\
 \left(\frac{173}{300}\right)^2
       -(m^2-1/2)(M^2-2)&=\frac{1465}{1620000}>0,\\
 mM&=\frac{1729}{900}.
\end{aligned}
 \tag{8}
\]

All radicals and comparison quantities are positive. Consequently

\[
 \cos\angle(c_C,c_E)>-\frac{1419}{1729},
 \qquad
 \angle(c_C,c_E)<\arccos\!\left(-\frac{1419}{1729}\right).
 \tag{9}
\]

But

\[
 \cos\alpha=-\cos(\theta/2)=-\frac{\sqrt{17}}5,
 \qquad
 17\cdot1729^2-25\cdot1419^2=481472>0.
 \tag{10}
\]

Thus \(-1419/1729>\cos\alpha\), and (9) implies that the
angle is strictly below \(\alpha\), a contradiction. Reflection
interchanging C,E gives the same contradiction if O projects at or
to the left of \(P_E\). Both weak outside endpoints are covered,
proving the strict strip (5).

## 3. A support-normal criterion supplies the whole-center projections

The projection premise (4) can be obtained without assuming an
externally owned side contact. Let K be an actual unit, P any actual
minimum-n support point of K, and n a unit normal. Let d be a unit
direction satisfying

\[
                           n\cdot d>1/\sqrt2.
 \tag{11}
\]

Then

\[
                         d\cdot(c_K-P)>0.
 \tag{12}
\]

To prove it, set \(w=c_K-P\). The support half-width of a unit
in every direction is at least \(1/2\), so
\(n\cdot w\ge1/2\), while \(|w|\le\sigma\).
Consequently its perpendicular component obeys

\[
 |w-(n\cdot w)n|\le1/2\le n\cdot w.
\]

The direction of w is therefore at most \(\pi/4\) from n.
By (11), n is strictly less than \(\pi/4\) from d. The angular
triangle inequality puts w strictly within \(\pi/2\) of d,
proving (12). This keeps every vertex, side point and original
aggregate side mean, including its endpoints.

In particular, an unloaded unit with two opposite vertex returns
whose outward return normals are strictly within \(\pi/4\) of
the respective outward port-chord directions satisfies (4), whatever
the owners and degrees of those neighbors.

## 4. Literal full-force H-owned H4 end

Retain the complete H4 pentagon graph

    HA, HB, HC, HD, AB, BC, CD, DE, EA,

with H unloaded of true positive degree four and D unloaded of true
positive degree three. The remaining degrees and loads are unchanged.
Suppose H owns the original HD normal. The complete selection-free
fixed-opposite-return theorem gives

\[
\begin{gathered}
 H=[0,1]^2,\qquad P=(p,1),\quad 0<p<1,\\
 D=P+[0,1]u+[0,1]v,
 \quad u=(a,b),\quad v=(-b,a),\quad a,b>0,\quad a^2+b^2=1,\\
 P_C=P+u,\qquad P_E=P+v,\\
 f_C=(\eta+\gamma b)u-\eta v,
 \qquad f_E=-\eta u+(\eta+\gamma a)v,
 \qquad \eta,\gamma>0.
\end{gathered}
 \tag{13}
\]

These are the complete original force vectors at D, not a new stress.
No C2 equation occurs. Put

\[
 e=(u-v)/\sqrt2,\qquad f=(u+v)/\sqrt2.
\]

In this orthonormal frame the two return vectors are

\[
 f_C=\frac1{\sqrt2}(2\eta+\gamma b,\gamma b),
 \qquad
 f_E=\frac1{\sqrt2}(-(2\eta+\gamma a),\gamma a).
 \tag{14}
\]

Both have strictly positive f-component and are strictly within
\(\pi/4\) of their respective outward e-directions. Their actual
ports are minimum supports on C,E. Section 3 therefore supplies (4)
before any external-owner selector is used. Whenever C,E have minor
center angle at least \(\alpha\), the original circle origin lies
strictly between the projections of their unchanged ports.

For the original `H4_D0.L0124`, take
\((A,B,C,D,E)=(0,1,2,3,4)\). The four loaded boundary bodies form
the path E--A--B--C, and the full component force sum is exactly
\(F_E+F_A+F_B+F_C=0\). The complete four-boundary-path theorem
gives minor angle \(\angle(c_C,c_E)>5\pi/6\). Since
\(\theta>\pi/3\), we have \(\alpha<5\pi/6\), so the strip
conclusion applies to this **entire H-owned-HD feature**.

For `H4_D0.L124`, the exact loaded bodies are B,C,E. Section 1 selects
at least one far pair from (C,E) and (B,E). In the former alternative,
if HD is H-owned, (13)--(14) give the strip. In the latter alternative
the graph-preserving reflection exchanges the unloaded ends A,D and
the loaded bodies B,C; the same implication applies **if the reflected
far end is H-owned**. The reflection does not turn a non-H-owned end
into an H-owned end, and a hypothesis at only the other end is not
silently transferred. The far-end and owner conjunction is essential
in this three-load join.

## 5. One genuine degree-two boundary moment now puts O below the chord

Continue in (13)--(14), assume the far-center condition just used, and
suppose additionally that A physically touches the circle. Its total
circle weight may be zero. E is the original loaded degree-two body
with precisely the positive neighbors D,A. C retains its actual third
force.

With the unchanged circle origin zero, the strip gives the chart

\[
 P_E=(-L,h),\qquad P_C=(T,h),\qquad
 L,T>0,\qquad L+T=\sqrt2.
 \tag{15}
\]

The lower D arc is the occupied arc: it contains its actual third
neighbor H at P, while the exterior rim pocket lies on the other arc.
The physical boundary path beginning E--A has the same counterclockwise
order as this lower D-arc order from E to C. Here is the precise order
join. The rim and its actual interior H retain their compatible Jordan
embedding. The path E--A and the remaining boundary continuation leave
the E port on the occupied side, while the D--C port closes the rim
through D. Add the actual circle spokes at the physical boundary bodies
and use their disjoint interior paths through the real squares. The
cyclic order at the lower occupied D arc agrees with their circular
order. Weak zero-weight junctions admit the same compatible arbitrarily
small resolution; they do not reverse this order. This is the ordinary
physical port-order argument, with no equation at C.

Let \(g\) be the original E-to-A normal, at its actual application
or shared-side mean Z, and let \(\lambda>0\) be its original
magnitude. The degree-free physical boundary-edge moment theorem
therefore gives

\[
                             \det(Z,g)>0.
\]

Let \(n_E=(-c,s)\) be the unit D-to-E normal. Equation (14) gives
\(c>s>0\). The unchanged full E2 moment equation, with all radial
circle moments zero, is

\[
 |f_E|\det(P_E,n_E)=\lambda\det(Z,g)>0.
\]

Consequently

\[
                           K:=ch-sL>0,
                  \qquad h>\frac{s}{c}L>0.
 \tag{16}
\]

Thus O is strictly below the actual opposite-port chord. This uses only
one true endpoint's degree-two moment. C has no false concurrence or
degree-two equation.

The extra premise that A is physically boundary is automatic in
`L0124`. In `L124` it covers only the original zero-load physical-boundary
refinement of A. If A is physically circle-clear, neither the
boundary-edge moment sign nor the next proper-concurrence argument
has been supplied here; that entire refinement remains open.

## 6. The original E mask and its upper-left center, under its actual side ownership

If the common selected certificate also includes the accepted
fixed-singleton off-line selection rule, its H-owned-HD feature has
DE owned by E. This pre-extraction rule has already been proved at the
exact fixed singletons (13); no current normal is altered here.
Write the whole actual E as

\[
 E=P_E+[0,1]n_E+[-\rho,1-\rho]k,
 \qquad k=Jn_E=(-s,-c),\qquad 0<\rho<1.
 \tag{17}
\]

Put

\[
                       N=cL+sh>0,\qquad Z_E=K+\rho.
\]

Because A is a physical boundary neighbor, the complete all-mask true
E2 proper-concurrence lemma applies. Its point q obeys

\[
 q=P_E+\ell n_E,\quad\ell\ge0,
 \qquad q=\tau F_E,\quad\tau>0.
 \tag{18}
\]

This lemma does not assert that q lies in E for the two-circle-corner
mask. Equation (18) suffices: the resultant has positive n-component
and negative k-component, since \(q\cdot n_E=N+\ell>0\) and
\(q\cdot k=-K<0\).

The center's n-coordinate is \(N+1/2>0\), so every physical circle
corner is on the outer n-face. The negative k-component of the
resultant forces the center's k-coordinate to be nonpositive. Hence

\[
\begin{gathered}
 Z_E\ge1/2,\qquad R^2=(N+1)^2+Z_E^2,\\
 c_E=(N+1/2)n_E-(Z_E-1/2)k.
\end{gathered}
 \tag{19}
\]

For \(Z_E>1/2\) there is one physical farthest corner; for
\(Z_E=1/2\) both outer n-face corners remain physical, with the
negative-k corner carrying positive weight and the other allowed its
full original zero or positive coefficient. This is the complete
original mask cover, not a choice of a favorable circle corner.

Equations (17),(19) give

\[
\begin{aligned}
 (c_E)_x&=-L-c/2-(1/2-\rho)s
              <-L-(c-s)/2<0,\\
 (c_E)_y&=(N+1/2)s+(Z_E-1/2)c>0.
\end{aligned}
\]

Also (18) places the actual resultant in the same strict upper-left
quadrant. These conclusions use the true E2 star and its physical
boundary neighbor A only. They impose no sign on the C resultant
and do not silently assign C an endpoint equation.

## 7. Exact direct inputs and remaining scope

| Source | SHA256 | Use |
| --- | --- | --- |
| GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md | 5da69931a63ac7cbf93ec3ff494489dc05d2245017da1c4dcddf1b4a8a6c956e | Full-window center radii, all-mask resultant deviations and directed-gap bound |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 164d08bb2c4dfe8510247e44298d309920cb88a780221252d833f51aa654225f | Complete four-load path angle lower bound and literal unshortened path |
| INNER_PENTAGON_H_OWNED_UNLOADED_END_FIXED_OPPOSITE_RETURN_VERTICES.md | bc1b08bc93401e25891f1307139c465409e4a3e260670513087b658c210e0f8c | Full original H4/D3 fixed ports and forces |
| INNER_PENTAGON_FOUR_SPOKE_NO_CHORD_OCCUPIED_POCKETS_AND_LONG_PORT_REDUCTION.md | ad0a8e658d303d7527a383c4688fa4bfdae1a04f46cecfb59c424cc4028e02a6 | Both literal original load representatives, degrees, reflection and pocket order |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 | Only degree-free Lemma 1.1, strict moment sign for two physical boundary squares |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Only all-mask Lemma 2.1 at actual E2 with physical boundary neighbor A |
| FIXED_SINGLETON_THREE_FORCE_OFF_LINE_NORMAL_SELECTION_AND_H4_OWNED_END_REDUCTION.md | d5e02f317ecbfdbd3d948fd27f5f78d6eda8803fb679c435ef3101780e1f47b1 | Section 6 alone uses its already compatible E-owned DE conclusion |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Original full force/torque and compatible physical order |

Sections 1--3 are broad local theorems. Section 4 preserves the exact
far-end/owner conjunction for the three-load family. Sections 5--6
preserve the additional physical-boundary premise at A. None proves a
whole original completion capacity. In particular the mixed C3/E2
pocket still requires a complete bound, and the physically clear A
refinement of L124 remains separate. Both original H4 families, their
graph parent and their coarse cells remain open.

No numerical pose, finite angle mesh, computational exclusion
certificate, late normal reselection, deleted force, fixed replacement
mean, Lean compilation or CI is used. All nine actual squares remain.
