# A three-edge boundary path has endpoint-center distance less than three

**Status: complete hand geometric scope extension and channel obstruction;
root and separate independent full audits passed.** The complete
metric estimates are already proved in
BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md, Sections1--5. This source
identifies their exact four-body scope, supplies the path-order premise,
and states the full normal-channel consequence. No stress or seventh
boundary square is needed for the geometric theorem.

Work throughout
\[
                         79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

## 1. The full geometric path theorem

**Theorem 1.1.** Let \(S_0,S_1,S_2,S_3\) be four distinct
interior-disjoint unit squares contained in the concentric disk
\(D_R\). Suppose each touches the circle and
\[
               S_0\cap S_1\ne\varnothing,\qquad
               S_1\cap S_2\ne\varnothing,\qquad
               S_2\cap S_3\ne\varnothing.
\tag{2}
\]
Then their endpoint centers satisfy
\[
                              |c_3-c_0|<3.
\tag{3}
\]

Every frame, circle-corner mask, actual contact feature and additional
physical contact is retained. The squares may have arbitrary positive
degrees and circle weights, including zero weights. Only their
physical boundary contacts in (2) enter the theorem.

### 1.1. The ordered center lifts use only the four path bodies

CIRCLE_CONTACT_ANGULAR_ORDER.md, Section3.2, proves that every
physical boundary contact joins angular neighbors: its minor
center arc has length less than72 degrees and contains no third
boundary center. This theorem applies to any physical boundary
set; it does not assume that the set forms a cycle.

At \(S_1\), the two distinct neighboring centers \(c_0,c_2\)
must lie on opposite angular sides. If both contact minor arcs
went in the same direction, the nearer center would lie inside
the other contact's minor arc. The same argument applies at
\(S_2\). Reverse the orientation if needed. The four centers then
have consistent lifts
\[
                    \alpha_0<\alpha_1<\alpha_2<\alpha_3
\tag{4}
\]
whose three successive gaps are the actual contact minor gaps,
each less than72 degrees. Extra boundary squares only strengthen
the empty-arc statement and do not alter this conclusion.

### 1.2. Exact dependency scope of the metric estimate

Here is the complete hypothesis audit of the cited source.

| Part of BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md | Actual input used |
| --- | --- |
| Section1 | Disk bound (1); if \(R<\sqrt{17}/2\), every center radius is less than3/2 |
| Section2 | One arbitrary boundary unit with \(R\ge\sqrt{17}/2\); its angular shadow has width \(<w:=\arctan(23/16)\) |
| Section3 | One possible endpoint with radius \(89/60<r<91/60\), forced whenever the endpoint distance is at least3 |
| Section4 | That same single endpoint's radius and frame; its entire sector of half-angle \(w+t\) lies in a fixed disk of radius \(y_0<3/2\) |
| Section5 | Exactly four boundary squares, their three actual contact points, and the ordered center lifts (4) |
| Section6 | The seven-cycle graph, solely to join every pair by a path of at most three edges; this section is not used here |

In particular the two middle shadow estimates in Section5 concern
only \(S_1,S_2\). No count, contact, orientation or load involving
three additional boundary squares is used in Sections1--5.

For clarity, the final metric assembly is reproduced next. If
\(|c_3-c_0|\ge3\), the center radius bound \(r<91/60\) forces
both endpoint radii to exceed89/60. Let \(t_0,t_3\) be their
maximum angular half-shadows, as computed from their actual frames
in Section3 of the cited source.

Choose contact-angle lifts \(\theta_0,\theta_1,\theta_2\) consistent
with (4). They exist because each successive contact gap is its
minor arc, each square shadow is connected, and each such shadow
has width less than w. The copies containing the corresponding
center lifts cannot disagree by a full turn: their center gap is
less than72 degrees, while their two shadow widths sum to less
than2w and \(72\text{ degrees}+2w<2\pi\).
Telescoping along the four actual squares
gives
\[
\begin{aligned}
 \gamma:=\alpha_3-\alpha_0
 &=(\theta_0-\alpha_0)+(\theta_1-\theta_0)
      +(\theta_2-\theta_1)+(\alpha_3-\theta_2)\\
 &<t_0+2w+t_3<\pi.
\end{aligned}
\tag{5}
\]
The middle differences need not be positive; their upper bounds
are the respective actual shadow widths.

Choose \(\delta_0,\delta_3\ge0\) with
\[
       \delta_0+\delta_3=\gamma,\qquad \delta_i\le w+t_i.
\tag{6}
\]
The cited endpoint-sector theorem puts the two centers, after a
common rotation, in one disk centered at \((x_0,0)\) of radius
\(y_0<3/2\). Its explicit constants and strict margin are
\[
 x_0=\frac{26026}{60\sqrt{3627485}},\qquad
 y_0=\frac{171353}{60\sqrt{3627485}},\qquad
 \frac94-y_0^2=\frac{20777891}{13058946000}>0.
\tag{7}
\]
Their distance is at most \(2y_0<3\), the desired contradiction.
This proves Theorem1.1, including the endpoint \(R=\sqrt{17}/2\).

## 2. A uniform obstruction to long transmitter channels

**Theorem 2.1.** In a selected physical stress certificate, suppose
a positive normal channel joins two boundary squares X,Y, and
its internal vertices are unloaded exact-degree-two transmitters.
If there are at least two internal transmitters, X,Y cannot also
be joined by a physical three-edge path of four boundary squares.

Indeed normal transmission supplies one unit direction n and
total reserve \(L\ge2\). Its actual endpoint support equations give
\[
              n\cdot(c_Y-c_X)=L+H_X(n)+H_Y(n)\ge3,
\tag{8}
\]
because every unit halfwidth is at least1/2. Hence their center
distance is at least3, contradicting Theorem1.1.

The endpoint bodies, and the two intermediate bodies on the
boundary path, may have any positive degrees or further forces.
No force equation is used at them. The transmitter vertices,
however, must have their stated exact degrees and zero circle
loads; further positive forces at an internal transmitter may
not be discarded. All actual side means stay in the telescoping
normal channel.

The boundary path need not consist of positive edges. Physical
zero-stress contacts suffice. The geometric theorem does not need
any normal convention; the channel theorem uses only the existing
full physical transmission equations.

## 3. The whole adjacent-unloaded four-load six-cycle orbit

**Corollary 3.1.** The entire selected simple positive six-cycle
\[
                         X-U-V-Y-A-B-X
\tag{9}
\]
is impossible when X,Y,A,B are loaded and U,V are unloaded.

The path \(X-B-A-Y\) consists of four boundary squares and three
physical contacts. The path \(X-U-V-Y\) is a two-body normal
channel. Theorem2.1 applies directly. This covers both original
transmitter-width alternatives before the disk bound removes
the diagonal ones, all physical zero-weight circle contacts at
U,V, every endpoint frame and mean, and all three arbitrary
completion squares.

Thus the entire four-load C6 orbit with the two unloaded vertices
adjacent is excluded. No equilibrium equation at a loaded endpoint,
proper concurrence, secondary minimizer, completion motion or
hole-capacity estimate is needed.

The other four-load orbits, the three-/five-load orbits and
additional positive chords remain separate domains. The local
Theorem2.1 may also be used in larger graphs, but only with its
actual boundary path and exact unloaded-transmitter hypotheses.
No coarse six-body row is declared closed by this corollary.
No numerical search, Lean compilation or CI is a premise.

