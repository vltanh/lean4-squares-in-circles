# Independent review of the remaining one-share channel-0 capacity theorem

Date: October 26, 2026.

**Verdict: PASS for the entire stated physical orbit and its precise three-allocation consequence.** This review does not assert completion of the remaining all-unique C6 parent gate.

Reviewed source:

- SIX_CYCLE_REMAINING_CAP_0_CAPACITY_ONE.md.

Prerequisites read for the physical and geometric joins:

- SIX_CYCLE_REMAINING_ONE_SHARE_FIVE_SCALAR_COMPATIBILITY.md, including the recovery of the actual circle branch and original shared mean.
- SIX_CYCLE_ONE_SHARE_FULL_ORBIT_COVER_AND_RESIDUE.md and SIX_CYCLE_REMAINING_ONE_SHARE_ANGLE_AND_FORCE_BOUNDS.md.
- SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md, including the actual occupied crosscut and the weak-boundary region-label argument.
- ANNULAR_CENTER_ARC_AT_23_25.md, in full.
- CENTERED_INNER_ARC.md, in full.

The whole-orbit radius theorem was already independently reviewed in REVIEW_C6_COMMON_POINT_FERMAT_BOUND_C6_2026_10_26.md. Its physical join supplies \(R<2\) for exactly the original remaining unique-corner orbit; no additional force or angle box is needed here.

## 1. Original geometry and strict inequalities

The canonical word, sole outgoing share, all three transmitters and all three extras are retained. The channel-0 chart reproduces the actual port equations:
\[
 S_0=[-a,1-a]\times[-b,1-b],\qquad
 S_1=(2-a,-H)+[0,1](X,Y)+[0,1](Y,-X),
\]
with \(a>b>1/2\), \(a^2+b^2=R^2\), \(H=b-1+\ell\), and the actual circle corner \(z_1=(2-a+X+Y,-H-X+Y)\).

The strict inequality \(0<\ell<1\) is legitimate. The \(\ell=1\) endpoint was included initially and excluded by an original closure equation in the orbit source. It was not replaced by a singleton contact or silently deleted.

The original shared torque gives \(\kappa=\ell/(a-b)\), and the actual negative first force component gives \(\kappa a>1\). Thus
\[
 H>b(1-1/a).
\]
The other strict inequality follows from the original nonshared torque. In particular \(AX-BY=z_1\cdot u_1>1/2\), so the division giving \(\eta=Y/(AX-BY)\) has the correct positive sign. Substituting the actual circle coordinates into \(1-\eta A<0\) yields exactly
\[
 YH>(X-Y)(2-a+X).
\]
The case \(X=Y\) is retained. No division by \(X-Y\) occurs.

## 2. Whole-domain channel height

Under the contrary assumption \(0<H\le21/50\), I independently expanded
\[
 R^2-\big[(2-a+\sqrt2)^2+H^2\big]
 =2W\left(H-\frac{(2-a)W}{\sqrt2+T}\right).
\]
The strict local inequality makes the right side positive if \(W>0\), and it vanishes if \(W=0\). Its use therefore covers the full original interval.

The resulting lower bound \(a\ge L=2+\sqrt2-\sqrt{R^2-H^2}\) satisfies
\(\sqrt2<L<3/2\). The actual opposite-corner displacement in \(S_1\) gives the independent upper bound \(a<33/20\). These arguments establish one entire interval \([L,33/20]\subset(1,R)\) containing the original \(a\).

The derivative
\[
 \frac{d}{dx}\left[\sqrt{R^2-x^2}(1-1/x)\right]
 =\frac{R^2-x^3}{x^2\sqrt{R^2-x^2}}
\]
shows that its minimum on this interval occurs at an endpoint. The upper endpoint estimate is strict and uses the correct monotonicity in \(R\).

At the lower endpoint, I reconstructed both the radical expression for \(\mathcal T(L)\) and the identity
\[
 \mathcal T(L)-\frac{\sqrt2}{8}
 =\frac{(1-2x)[8(2+\sqrt2)x^2-4\sqrt2x-\sqrt2]}
        {8(1+2x)},\qquad x=L-1.
\]
The bracket is positive on the entire stated interval: its derivative is at least \(12\sqrt2\), and its value at \(\sqrt2-1\) is \(8-5\sqrt2>0\). The comparison with \(H^2\) has the explicit positive reserve \(1/10000\). Both endpoints therefore contradict the actual strict local inequality. The conclusion \(H>21/50\) is valid for every original physical core in the remaining orbit.

## 3. Actual center gap

The two used components of the original direction cone and closure are
\[
 N\ge\frac{s_0-c_0}{\sqrt2},\qquad
 N=s_1-s_0-1+\delta+Y.
\]
Their substitution gives \(\delta>W/2\). The strictness follows from the original \(\alpha_1>0\), rather than any generic-position assumption.

The center difference is exactly
\[
 C_1-C_0=
 \left(\frac32+\frac T2,\ \delta-\frac{1+W}{2}\right).
\]
Its second component lies strictly between \(-1/2\) and \(1/2\), because \(0<\delta<1\), \(W\ge0\), and \(\delta>W/2\). Consequently
\[
 |C_1-C_0|^2<3+\frac3{\sqrt2}.
\]

The channel-cap endpoint theorem puts the actual two center directions in opposite upper quadrants after the stated reflection. Thus the angle used in the cosine law is the actual outward consecutive-center gap in \((0,\pi]\). Each center has norm at least \(79/40-1/\sqrt2\). If the gap were at least \(\arccos(-119/200)\), the cosine law would contradict the preceding strict distance bound. The use of the lower center norms is valid because the coefficient of their product is positive.

The passage from this exact cosine threshold to \(127^\circ\) is also strict and uses the correct monotone branches. The positive cubic sine remainder and \(\pi>25/8\) imply
\(\sin(37\pi/180)>119/200\), hence \(\arccos(-119/200)<127\pi/180\).

## 4. Full-square inner arcs and routing

The actual occupied-crosscut theorem places each whole pocket extra in \(y\le-H\), not just its center. Its vertical half-width is at least \(1/2\), giving center norm \(>23/25\). Therefore the full statement of ANNULAR_CENTER_ARC_AT_23_25.md applies to each unchanged square at radius \(5/4\), for every independent orientation and without any circle-load assumption.

I read its whole own-frame proof. Both the outer-face and inner-face domains produce the entire connected open intersection, not a selected subarc. The radial-center point lies in that open arc. The outer-face proof covers all four possible differences of angular endpoints, and the inner-face proof checks the sign needed before squaring. Its strict angular length is \(>29\pi/120\).

For the two endpoint units, their center norm is \(>5/4\). The radial-center points lie in their open interiors, and their horizontal coordinates are strictly on the two separated sides of the actual channel. This puts every intersection of the middle channel segment with the upper semicircle between the actual center angles.

Each endpoint's full closed inner-circle arc is connected. Its upper-semicircle restriction is still an interval, since \(C_i\cdot z>0\) for every point of the square. This interval cannot cross the other endpoint's center angle: that radial point belongs to the other open square, and physical nonoverlap forbids its membership in the first closed square.

These facts justify the claimed path to infinity for any purported extra-interior inner-circle point outside the consecutive-center interval. The semicircle path avoids both endpoint intervals and the middle crosscut segment; the horizontal ray then lies below the strictly positive channel height. Hence such a point cannot have the bounded pocket label. This proves routing into the actual consecutive interval without assuming sector containment of the extra or its center.

The endpoint units block the complete closed centered arcs of half-width \(\pi/9\) inside their open interiors. All extra arcs are consequently contained in one free interval of length
\[
 <127\pi/180-2\pi/9=29\pi/60.
\]
Two extras would contribute disjoint open arcs of combined length \(>29\pi/60\), which is impossible. Shared junctions, original application endpoints and additional zero-weight contacts are preserved by the cited compact-interior region-label argument.

## 5. Exact arithmetic and consequence

Using fresh integer and Fraction arithmetic, I reconstructed all thirteen displayed cap and imported arc reserves used in the proof:
\[
\begin{gathered}
 \frac{16783}{280000},\quad
 \frac{30381}{1960000},\quad
 \frac{280141}{43560000},\quad
 \frac{391}{62500},\quad
 \frac1{10000},\quad
 \frac{6957}{1120000},\quad
 \frac{11412799}{3583180800},\\
 \frac{41}{2500},\quad
 \frac{339}{10000},\quad
 \frac1{32},\quad
 \frac7{2116},\quad
 \frac{706855}{594542592},\quad
 \frac{4682051447}{13045963161600}.
\end{gathered}
\]
All equalities and positivity claims agree. The lower-endpoint identity was separately reconstructed in \(\mathbb Q(\sqrt2)[x]\). These checks reproduce fixed hand inequalities; no sampled sign or box partition is a proof premise.

Together with the already accepted central capacity one and empty pocket 1, the new theorem excludes exactly
\[
 (n_c,n_0,n_2)=(0,3,0),(0,2,1),(1,2,0).
\]
It retains exactly
\[
 (0,0,3),(0,1,2),(1,0,2),(1,1,1).
\]
Every one of the original nine squares remains in the physical domain. The source establishes pocket-0 capacity at most one over the whole remaining orbit and no stronger completion claim. No new computational certificate, Lean compilation or CI is involved.

