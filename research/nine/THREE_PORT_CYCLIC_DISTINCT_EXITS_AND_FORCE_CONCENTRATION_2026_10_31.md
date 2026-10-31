# Three-port cyclic unloaded modules have three distinct exit hubs

Date: 2026-10-31. Hand-proof continuation for PR #11.

## Result and scope

Fix the original physical force-and-torque certificate of a packing of nine
actual unit squares in the disk about the origin with

\[
R^2\le Q=1105/256.
\]

All original positive pair forces, applications or shared-side means, full
degrees, and all individual circle coefficients remain unchanged. A square
is **unloaded** if its total selected circle coefficient is zero. It may
still physically touch the circle.

Let \(K\) be a connected entirely unloaded set whose full original positive
cut contains exactly three edges. Suppose its induced original positive
graph has cycle rank \(b\ge1\). Suppress only genuine unloaded full-degree-two
paths, retaining their actual internal bodies and all three original cut
edges. A hub is an actual member of full degree at least three.

**Theorem 1. The three reduced exit arms end at three distinct hubs.**
Thus the condition “at most one reduced exit per hub” is automatic for
every cyclic three-port unloaded module, regardless of hub degrees,
cycle rank, or repeated external terminal identities.

This removes an explicit hypothesis from the existing subcubic multicycle
reduction. It also excludes every rank-two **D-peripheral** diamond with
all allowed internal and exit-arm transmitter placements. It does not by
itself exclude arbitrary higher-degree modules with three distinct exit
hubs, four-edge cuts, or a whole original coarse parent.

## 1. Two elementary full-cut facts

For a square \(S\) with center \(c_S\), let
\(h_S(v)\) be its centered support halfwidth. At every unit direction,
\(h_S(n)\ge1/2\); on all vectors it is even, homogeneous, and subadditive.
At an original positive contact \(i\)--\(j\) with outward normal \(n\)
from \(i\) toward \(j\),

\[
n\cdot(c_j-c_i)=h_i(n)+h_j(n).
\]

### Fact A: no unloaded region with a common terminal point

Let \(L\) be a nonempty entirely unloaded set with a nonempty full positive
cut. Suppose every distinct outside terminal contains the same actual
point \(p\). Dot the complete original translation at each member \(i\)
with \(c_i-p\) and sum. Internal pairs contribute

\[
-I,
\qquad I=\sum_{ij\text{ internal}}\mu_{ij}(h_i(n)+h_j(n))\ge0.
\]

At a cut contact with normal \(n\) from \(i\) toward its terminal \(T\),
the supporting line and \(p\in T\) give

\[
n\cdot(c_i-p)\le-h_i(n)\le-1/2.
\]

The summed translation would therefore give

\[
0\le-I-\frac12\sum_{\mathrm{cut}}\mu<0,
\]

a contradiction. In particular no nonempty unloaded positive component
has just one terminal; nor can its entire terminal set consist of two
physically touching squares. This proof allows arbitrary repeated cut
incidences and does not require cut applications themselves to coincide.

### Fact B: a short two-terminal region needs a common positive neighbor

Let an unloaded region \(L\) have exactly two distinct outside terminals
\(A,Z\), with arbitrary full cut multiplicities. Group its complete
outward forces as \(F_A,F_Z\). Summing translations gives
\(F_A+F_Z=0\). Center-dot work gives

\[
F_Z\cdot(c_Z-c_A)
=I+\sum_{\mathrm{cut}}\mu(h_{\rm internal}(n)+h_{\rm terminal}(n))>0.
\]

Hence \(F_Z=\lambda e\), \(F_A=-\lambda e\) for an actual unit vector
\(e\) and \(\lambda>0\). Put \(C=\sum_{\mathrm{cut}}\mu\). Subadditivity
at each of the two unchanged terminal frames yields

\[
\begin{aligned}
\lambda\,g_e(A,Z)
&\ge I+C/2,\\
C&\ge2\lambda,
\end{aligned}
\qquad
g_e(A,Z)=\min_Z e\cdot x-\max_A e\cdot x.
\tag{1}
\]

Consequently \(g_e(A,Z)\ge1+I/\lambda\).

Suppose the actual positive neighbor sets \(N_A,N_Z\) inside \(L\) are
disjoint. Sum the complete translations over \(N_A\). Its cut to \(A\)
is the entire group \(-\lambda e\), and it has no cut to \(Z\). Thus
the original edges from \(N_A\) to \(L\setminus N_A\) have vector sum
\(\lambda e\). Their magnitude sum is at least \(\lambda\), so
\(I\ge\lambda\). Equation (1) gives

\[
g_e(A,Z)\ge2. \tag{2}
\]

The existing full endpoint theorem
`SHARP_CONTACT_RADIUS_AND_NEAR_LONG_ENDPOINT_LOAD_2026_10_31.md`,
Sections 3–4, proves that at such a gap the entire closed outward
dominant side of \(A\) is contact-free. Every original positive normal
at \(A\) has nonpositive projection onto its outward own axis \(u_A\).
The **original** group from \(A\) to \(L\) is \(+\lambda e\), whose
projection onto \(u_A\) is strictly negative because \(e\cdot u_A<0\).
Thus the complete translation at \(A\) cannot vanish if \(A\) is
unloaded. The same argument holds at \(Z\).

It follows that if either terminal is unloaded, \(N_A\cap N_Z\ne\varnothing\).
This is the one-layer instance of the existing arbitrary two-terminal
graph-distance theorem, rederived here to make the exact needed scope
explicit. It uses no planar drawing and no newly selected contact normal.

## 2. Genuine suppression and the exit-host alternatives

An unloaded full-degree-one square is impossible by its translation.
An unloaded degree-two square propagates equal opposite forces; its
complete torque propagates a straight contact channel with width one or
\(\sqrt2\). A returning degree-two channel is impossible because its
positive signed widths would telescope to zero. Thus a cyclic connected
\(K\) has at least one hub, and each reduced cut arm ends at a hub.

Different reduced arms have disjoint internal degree-two bodies. Otherwise
an internal body would have at least three distinct positive neighbors.
The original three cut edges remain distinct, including when external
terminal squares repeat. Every body internal to an exit arm has precisely
the two original positive neighbors on that arm.

There are only three distributions of the three reduced exits among hubs:

\[
3,\qquad 2+1,\qquad 1+1+1.
\]

We exclude the first two without any restriction on hub degrees or
internal cycle rank beyond \(b\ge1\).

### All three reduced exits at one hub

Let that hub be \(A\). Remove \(A\) and the internal degree-two bodies
of its three exit arms. Every remaining positive component of \(K\)
has only \(A\) as an outside terminal: the entire original cut was on
the three removed arms, and their internal bodies have no off-arm edges.
Each such component has a nonempty cut to \(A\) by original connectedness.
Fact A excludes every component.

Therefore the original induced graph on \(K\) is just the hub with its
three transmitted or direct exit arms. It is a tree, contradicting
\(b\ge1\).

### Two exits at \(A\), one at another hub \(H\)

Remove \(A\) and the internal degree-two bodies of its two exit arms.
Retain every other member of \(K\), including every internal body on
the exit arm from \(H\). Any positive component not containing \(H\)
has only \(A\) as its outside terminal, so Fact A excludes it.
Thus all remaining members form one nonempty connected unloaded region
\(L\). Its full distinct outside terminal set is exactly \(\{A,Z\}\),
where \(Z\) is the actual outside endpoint of the original third cut
edge. The two terminals are distinct because \(A\in K\), \(Z\notin K\).

There is exactly one original positive edge from \(L\) to \(Z\); let
its host in \(L\) be \(T\). Since \(A\) is unloaded, Fact B forces a
common positive neighbor of \(A,Z\) inside \(L\). That neighbor must
be \(T\), the unique \(Z\)-cut host.

If the reduced \(H\)-exit arm contains a degree-two transmitter, its
last body \(T\) has only its preceding arm neighbor and \(Z\) as its
full positive neighbors. It cannot also contact \(A\) positively.
Equivalently, that would make this arm end at \(A\), rather than at
the distinct hub \(H\). Hence the third exit arm is direct, \(T=H\),
and \(AH\) is an original direct positive contact.

Now remove \(H\) as well. Every remaining positive component has full
outside terminal set contained in \(\{A,H\}\). Its cut is nonempty
by the original connectedness. The two actual terminal squares \(A,H\)
touch at their original positive contact, so Fact A again excludes
every component. All that remains of the internal reduced graph is
the direct edge \(AH\); the two removed exit arms add only trees.
Its cycle rank is zero, the final contradiction.

Only \(1+1+1\) survives. This proves Theorem 1.

## 3. A stronger global force concentration inequality

The conclusion of Theorem 1 permits the following estimate for every
cyclic three-port module, with arbitrary original degrees and cycles.
It also holds independently for any reduced unloaded module having
at most one exit per hub, whatever its cut size.

Use the existing genuine-channel bound: each reduced internal link or
exit arm incident to an unloaded hub has zero or one genuine transmitter.
Two consecutive transmitters would produce a gap at least two with a
positive inward endpoint force, forcing that hub loaded.

Let \(E\) be the exit hubs and \(F\) the other hubs. Let

* \(S_{EE},S_{EF},S_{FF}\) be total internal channel magnitudes by endpoint
  classes;
* \(N\) be the total magnitude of subdivided internal channels;
* \(N_{EE}\) be the portion of \(N\) whose endpoints are both in \(E\);
* \(A\) be the total magnitude of subdivided exit arms;
* \(C>0\) be the total exit magnitude;
* \(D_E=S_{EE}-N_{EE}\) be the total magnitude of direct original
  contacts between exit hubs.

Every actual square center satisfies \(|c|<M=91/60\). Summing reduced
center-dot work at the unchanged hubs and using the actual terminal
centers gives the strict original-channel estimate

\[
S_{EE}+S_{EF}+S_{FF}+N+A<\frac{31}{60}C. \tag{3}
\]

At each exit hub its unique exit magnitude is at most its total internal
incident magnitude. Summing only over \(E\) gives

\[
C\le2S_{EE}+S_{EF}. \tag{4}
\]

Combining twice (3) with (4) yields

\[
\boxed{S_{EF}+2S_{FF}+2N+2A<\frac{C}{30}.} \tag{5}
\]

Using (4) once more,

\[
\boxed{D_E>\frac{29}{60}C+S_{FF}+(N-N_{EE})+A.} \tag{6}
\]

All terms retain their original strictly positive coefficients. In
particular there must be an actual direct positive edge between two
exit hubs. No sufficiently weak contact has been deleted. The estimate
controls complete groups of channels touching the nonexit hubs, not
only a selected cycle.

## 4. Literal consequences for the current finite topologies

1. **D-peripheral:** its reduced exits are distributed \(2+1\), so every
   internal/exit transmitter placement is excluded by Theorem 1.
2. **D-central with both exit-host links direct:** the exit hubs \(A,B,C\)
   have direct links \(AB,AC\); the fourth hub \(H\), together with
   all transmitters on \(HA,HB,HC\), is an unloaded full three-cut
   module. Its terminals \(A,B,C\) form a connected actual physical
   graph. The separately written complete connected-terminal theorem
   `GLOBAL_UNLOADED_CONNECTED_TERMINAL_CUT_AT_LEAST_FOUR_AND_COMPLETE_THREE_CUT_ALL_SIZE_PHYSICAL_PATH_EXCLUSION_2026_10_31.md`
   excludes it. This consequence imports that source in addition to
   the direct proofs above.
3. **D-central with at most one exit-host link direct:** equation (6)
   makes precisely one such edge direct and quantitatively dominant.
   Its geometric exclusion needs the separate dominant-contact-pair
   argument; it is not claimed here.
4. **All cyclic subcubic three-port modules:** their previously explicit
   one-reduced-exit-per-hub hypothesis is now unnecessary. Their
   existing rank and skeleton reduction applies to the entire cyclic
   subcubic scope. The subsequent house and subdivided-\(K_{2,3}\)
   geometric exclusions remain separate premises.
5. **Higher-degree/higher-rank three-port modules:** the three distinct
   exit-hub reduction and (5)–(6) apply unchanged. They are not by
   themselves a proof excluding every such module.

## 6. Verification boundary

All arguments here are hand proofs. No numerical evaluation, pose search,
mathematical exclusion script, Lean, Lake, or CI was used. The only
imported geometric ingredients of Theorem 1 are the original two-force
channel classification and the whole contact-free outward-side theorem
at gap at least two. Fact A and the needed two-terminal work/one-layer
argument are printed in full. Planarity and the physical occupied-cross
theorem are not needed for Theorem 1 or (5)–(6).

This source proves a structural family result, not the unrestricted
radius bound or equality classification. No canonical coarse/fine ledger
flag is changed by this file alone.
