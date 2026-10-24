# Loaded vertices of a multi-load simple cycle have nonparallel pair forces

**Status: complete hand whole-family structural theorem; root and
separate independent full audits passed.** Work in
\[
                         79/40\le R\le\sqrt{1105}/16
\tag{1}
\]
with the existing compatible physical certificate, including strict
point normals and diagonal-transmitter avoidance.

**Theorem.** If the entire positive component is a simple cycle with
at least three loaded bodies, the two actual positive pair-force
normals at every loaded body are nonparallel.

This covers isolated loads with two unloaded neighbors, all lengths
and widths of their two maximal transmitter channels, all physical
circle masks and every actual side mean. There is no boundary-neighbor
or nonzero-cycle-moment premise. The distinct-other-endpoints assumption
is supplied by the three-load minimum and is essential: the two-loaded
six-cycle is outside this theorem.

## 1. The complete channel and parallel-load classifications

Fix a loaded body T. On either side, follow the cycle to the next
loaded body. Each intervening vertex is an unloaded exact-degree-two
transmitter. The normal-channel classification gives reserve
\[
                            L\in\{0,1,\sqrt2,2\}.
\tag{2}
\]
Here0 is a direct loaded contact,1 or sqrt(2) is one transmitter,
and2 consists of two side-normal transmitters. Longer runs and a
two-body run containing a diagonal are excluded by the uniform
center bound, as in PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md,
Sections1--2.

The two next loaded bodies are distinct because the full component
is a simple cycle with at least three loads. LONG_CHANNEL_ENDPOINT_MATCHING.md
therefore prohibits reserve2 on both sides of T.

Suppose the actual pair forces at T were parallel. Their nonzero
sum is opposite the circle resultant. Let e be the unit outward
circle-resultant direction. No pair normal can point along +e:
with one positive circle corner it exposes that unshareable circle
point; with two physical circle corners a noncentral weighted
resultant also exposes a circle corner, while the central outward
axis exposes an outer face of support \(\sqrt{R^2-1/4}>R-1\).
A unit beyond that face cannot fit in the disk.

Both pair normals thus point along -e on the same actual support
face. Their positive weighted application has zero moment and is
radial. The exact radial-terminal calculation, valid for these
aggregated parallel forces, leaves precisely:
\[
\begin{array}{ll}
\mathrm{D}:&
  p_D=r e,\quad r=R-\sqrt2,\quad
  \text{both actual applications equal }p_D;\\[2mm]
\mathrm{S}:&
  T=[h,h+1]e+[-1/2,1/2]t,\quad
  h=\sqrt{R^2-1/4}-1,\quad t\perp e.
\end{array}
\tag{3}
\]
For S the two circle weights are equal and positive, and the
weighted application is \(he\); the individual applications
\[
                              he+y_i t,\qquad |y_i|\le1/2
\tag{4}
\]
are kept arbitrary. D has its unique physical far corner in
direction e. This classification includes every original physical
two-corner/zero-individual-weight possibility before the radial law
selects the displayed form.

For later exact comparisons, the window gives
\[
       14/25<r<7/10,\qquad
       9/10<h<61/60,\qquad |h-1|<1/10.
\tag{5}
\]

## 2. Direct loaded neighbors and side-normal single transmitters are impossible

### 2.1. A direct loaded neighbor

For S, any direct neighbor would meet the inner face (4) with
normal -e. C7_FORCE_POLYGON.md, Lemma2.1, proves that every such
neighbor is strictly inside the circle. It cannot be the next
loaded body.

The D case also has a short direct proof. Such a neighbor B contains
\(p_D=re\) and lies in the half-plane \(e\cdot x\le r\).
For each point z of B,
\[
 |z|^2=r^2+2r\,e\cdot(z-p_D)+|z-p_D|^2
                         \le r^2+2<R^2,
\tag{6}
\]
since \(R=r+\sqrt2\) and r>0. Thus B is circle-clear.
Reserve0 is excluded for both radial types.

### 2.2. One side-normal transmitter

For S, the actual application belonging to the next loaded body
is
\[
                              (h-1)e+y_i t.
\]
Its squared norm is less than \(1/100+1/4=13/50\).
But every point of a boundary unit has norm at least
\(R-\sqrt2=r>14/25\), and \(13/50<(14/25)^2\).

For D, the corresponding point is \((r-1)e\), whose norm is
\(1-r<r\) by (5). This likewise cannot belong to a boundary unit.
Thus reserve1 is excluded for both radial types, with all original
side-normal application means retained.

Each incident channel must consequently have reserve sqrt(2) or2.

## 3. The radial-D alternative is impossible

A diagonal transmitter has its application at its extreme diagonal
vertex. Its common normal is along that diagonal. At T of type D,
the same physical application \(p_D\) is also a vertex and the same
normal is T's radial diagonal. This would be a vertex/vertex
contact with the chosen normal equal to a body diagonal, excluded
by the already compatible diagonal-avoidance convention.

Equivalently, that convention requires every diagonal transmitter's
neighboring endpoint application to be in the strict interior of
a neighboring side, whereas \(p_D\) is the unique D vertex.
No existing normal is changed to obtain this exclusion.

Both incident channels of a radial D would therefore have reserve2.
Their other loaded endpoints are distinct. The matching theorem
excludes them. This covers the entire D alternative without a
nonzero common moment or a direct boundary edge elsewhere in the cycle.

## 4. The radial-S alternative is impossible

### 4.1. Two diagonal single-transmitter channels

If both reserves are sqrt(2), the two distinct neighboring
transmitters have the same diagonal direction e and the same
square frame. Their centers are
\[
                       (h-1/\sqrt2)e+y_1t,\qquad
                       (h-1/\sqrt2)e+y_2t.
\tag{7}
\]
By (4), \(|y_1-y_2|\le1\). On each common side axis, their
center difference therefore has magnitude at most \(1/\sqrt2<1\).
The two unit squares overlap in their open interiors. This is
impossible even when the actual T applications are opposite
endpoints of its entire inner face.

### 4.2. One reserve2 and one diagonal channel

The reserve2 channel forces endpoint-center distance at least3.
The farthest-corner center inequality then gives
\[
                         R^2\ge17/4,\qquad
                         K:=\sqrt{R^2-1/4}\ge2.
\tag{8}
\]
This radius floor concerns the original disk and does not require
any geometric hypothesis at the far endpoint beyond its unit size.

Let B be the loaded body at the far end of the diagonal channel.
The compatible diagonal convention gives it the side axes e,t,
with both endpoint applications strict side-interior points.
Since \(c_T=(K-1/2)e\), its actual center is
\[
                 c_B=(K-\tfrac32-\sqrt2)e+\eta t,
                                      \qquad |\eta|<1.
\tag{9}
\]
The first coordinate is negative throughout (1). Hence
\[
\begin{aligned}
 \max_{z\in B}|z|^2
 &<(2+\sqrt2-K)^2+\tfrac94\\
 &=R^2+(4+2\sqrt2)(2-K)\le R^2.
\end{aligned}
\tag{10}
\]
Thus B is circle-clear, contradicting its positive load. The strict
inequality retains both original transverse parameters; it does not
replace an endpoint application by a midpoint.

### 4.3. Two long channels

The only remaining pair of reserves is (2,2). Their other loaded
endpoints are distinct, so LONG_CHANNEL_ENDPOINT_MATCHING.md applies
again. This excludes the last S alternative.

Sections2--4 exhaust the full parallel-force classification (2)--(3)
and prove the theorem.

## 5. Global consequences and exact limits

The nonparallel proper-concurrence theorem
FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md, Lemma1.1, now applies to every
loaded body of every such simple cycle, even if it has no loaded
neighbor. At each loaded body q is a positive multiple of the
circle resultant and every actual contact satisfies
\[
                              p-q=\alpha n,\qquad\alpha\ge0.
\tag{11}
\]
For a physical unique-corner unit q lies inside that unit; a physical
two-corner q is not asserted bounded. These are the complete
all-mask conclusions used in subsequent cycle arguments.

The theorem does not turn a body with an extra positive edge into
a degree-two body. The actual whole-component and exact internal
transmitter hypotheses remain essential. Two different long channels
between the same two loads are deliberately retained outside the
three-load hypothesis. All physical zero-weight circle contacts,
shared-side means and extra packing squares remain.

No completion capacity, secondary minimizer, new normal selection,
numerical pose cover, Lean compilation or CI is used.

