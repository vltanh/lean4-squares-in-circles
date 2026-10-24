# n=9: full conditional equality family for signed matched 4+3 chains

**Status:** Necessary-and-sufficient hand classification of **the
entire signed-matched 4+3 terminal branch** at \(q=Q=1105/256\).
This is **not** a classification of all unrestricted optimal
nine-square packings: the universal extraction of this terminal
pattern is still OPEN.

Unlike the stratified equality domain, this description permits:
- either independently chosen endpoint vertical sign \(\sigma_L,\sigma_R\);
- nonstratified positions of the three inner chain squares;
- two extra independently oriented squares, with arbitrary **oblique**
  true separating axes.

It contains the exact nonstratified two-stack witness
[TWO_STACK_SHARP_EQUALITY_WITNESS.md](TWO_STACK_SHARP_EQUALITY_WITNESS.md)
after switching the x/y coordinate frame.

## 1. Exact hypotheses

Fix an orthonormal frame (x,y) centered on the disk. Suppose
seven of nine freely oriented unit squares are partitioned
into two *horizontally projection-separated* chains,
\[
 M_L,M_2,M_3,M_R\quad\text{and}\quad B_L,B_2,B_R,
\]
left-to-right. Suppose the corresponding endpoint pairs
\((M_L,B_L)\) and \((M_R,B_R)\) have disjoint **vertical
projection interiors** (the two directions may have independent
signs). Assume the nine squares satisfy the original physical
Packing predicate at \(q=Q\).

The endpoint interlocking lemma of
[SIGNED_MATCHED_CHAIN_STRESS.md](SIGNED_MATCHED_CHAIN_STRESS.md)
guarantees that their **horizontal** projections overlap
at \(q\le Q\). Thus the vertical-separation premise follows
automatically if a single x/y frame separates every pair
by at least one coordinate projection. It is not assumed
automatically when extra oblique axes are essential.

## 2. Seven anchored squares are fully axis-aligned

**Theorem 2.1 (necessity of the signed seven-anchor normal form).**
Under the hypotheses of Section 1, there are signs
\(\sigma_L,\sigma_R\in\{-1,+1\}\) such that the seven
chain squares have the following exact centers and
axis-aligned side frames:

\[
\begin{array}{c|c}
 \text{square}&\text{center}\\\hline
 M_L&(-3/2,\ \sigma_L/16)\\
 M_2&(-1/2,\ \alpha)\\
 M_3&(1/2,\ \beta)\\
 M_R&(3/2,\ \sigma_R/16)\\
 B_L&(-1,\ -15\sigma_L/16)\\
 B_2&(0,\ \gamma)\\
 B_R&(1,\ -15\sigma_R/16).
\end{array}\tag{1}
\]

*Proof.* The chains supply their exact long/short
horizontal span inequalities with minimum reserves 2 and 1.
The assumed vertical separation of each endpoint pair gives
the signed conditions of
[SIGNED_MATCHED_CHAIN_STRESS.md](SIGNED_MATCHED_CHAIN_STRESS.md),
Theorem 1.1. At \(q=Q\) equality holds in that theorem,
so all four stressed endpoints are axis-aligned and pinned
at the four centers in (1), with signs \(\sigma_L,\sigma_R\).

Because the four-chain endpoint horizontal center span is
exactly 3, while all four horizontal projection widths are
at least 1, the three intervening projection gaps must
each be saturated and all four widths must equal one.
Thus \(M_2,M_3\) are also axis-aligned, with their horizontal
center coordinates \(-1/2,1/2\). Similarly the 3-chain
endpoints have center span 2, forcing \(B_2\) to be
axis-aligned at horizontal center coordinate zero.
The remaining heights are \(\alpha,\beta,\gamma\). \(\square\)

This proves that the **seven chain squares** are aligned;
it makes no assertion that the final two squares are aligned.

## 3. Exact, small three-slider domain

Set
\[
 U_M=\sqrt{849}/16-1/2,\qquad
 U_B=\sqrt{1041}/16-1/2,\qquad Q=1105/256.
\]
The seven squares of (1) fit the disk and have pairwise
disjoint open interiors **if and only if**
\[
\boxed{
\begin{aligned}
|\alpha|&\le U_M,&|\beta|&\le U_M,&|\gamma|&\le U_B,\\
|\alpha+15\sigma_L/16|&\ge1,&
|\beta+15\sigma_R/16|&\ge1,\\
|\alpha-\gamma|&\ge1,&|\beta-\gamma|&\ge1.
\end{aligned}}\tag{2}
\]

*Proof.* The pinned endpoint squares touch the circle at
exactly \(Q\). For the interior M squares, exact
axis-aligned circle containment at x=±1/2 is
\((1)^2+(|\alpha|+1/2)^2\le Q\), and likewise for
\(\beta\). For the middle B square at x=0 it is
\((1/2)^2+(|\gamma|+1/2)^2\le Q\).
These are precisely the first three bounds.

Within each horizontal projection chain the
different members are already disjoint.
Between M and B, all pairs are horizontally
separated except \(M_L,B_L\) and \(M_R,B_R\),
which touch vertically at distance 1 by (1),
and the four pairs
\((M_2,B_L),(M_3,B_R),(M_2,B_2),(M_3,B_2)\).
Their horizontal center differences are 1/2,
so their interiors are disjoint if and only if
their corresponding vertical center gaps are
at least 1. These are exactly the remaining
four inequalities in (2). All other cross pairs
have horizontal center difference at least 1.
\(\square\)

This allows configurations not stratifiable as
a single 3-over-4 layer ordering: the height of
\(B_2\) is not forced to lie on the same side of
both interior M squares as B's outer squares.

## 4. Two further squares: exact necessary-and-sufficient conditions

Let \(F_1,F_2\) be any freely rotated unit squares with
centers \(c_1,c_2\) and orthonormal side frames
\((u_i,v_i)\). Write
\[
 D(F_i)=\|c_i\|^2+1/2+|c_i\cdot u_i|+|c_i\cdot v_i|,
\]
and for any direction e put
\[
 H_{F_i}(e)=\tfrac12(|e\cdot u_i|+|e\cdot v_i|).
\]
For a unit square S with known axis-aligned frame, put
\(H_S(e)=(|e_x|+|e_y|)/2\).

Besides (2), impose exactly:
1. **Disk:** \(D(F_1)\le Q\) and \(D(F_2)\le Q\).
2. **Each free-to-anchor pair:** for every
   \(F_i\) and each of the seven centers S in (1),
   there exists
   \(e\in\{(1,0),(0,1),u_i,v_i\}\) with
   \[
          |(c_i-c_S)\cdot e|
             \ge H_{F_i}(e)+H_S(e). \tag{3}
   \]
3. **Free/free pair:** there exists
   \(e\in\{u_1,v_1,u_2,v_2\}\) with
   \[
           |(c_1-c_2)\cdot e|
                \ge H_{F_1}(e)+H_{F_2}(e). \tag{4}
   \]

These conditions are a **finite 9-real-parameter
model** (three slider heights, two planar free centers,
and two free angles), plus two discrete signs and
15 explicit pair-separation disjunctions. All
36 original pair constraints have been reduced:
21 pairs within the seven anchors are decided
by the four scalar tests in (2), leaving only
14 free/anchor and one free/free pair.

**Theorem 4.1 (converse and complete signed-branch equality family).**
Every nine-square packing satisfying Section 1's
two-chain and endpoint hypotheses is, up to a common
rotation/relabeling, exactly one of the configurations
(1)–(4), for one of the four sign choices.
Conversely every choice of parameters satisfying
(2)–(4) forms a physical nine-square packing
inside the disk of squared radius exactly \(Q\).

*Proof.* Necessity of (1) and (2) is Theorem 2.1
and Section 3. Disk containment and open-interior
disjointness of the two further squares are
equivalent to (3)–(4) and their disk tests by the
exact separating-axis theorem. Conversely (2)
handles all seven anchored squares, and (3)–(4)
handles every remaining pair, so the entire
nine-square configuration packs the disk.
The pinned outer anchor vertices are on the
circle at squared radius \(Q\), so this is the
least containing squared radius **about the
stipulated disk center**.
No unrestricted sharp-radius lower bound is
needed for the converse. \(\square\)

### Difference from the earlier stratified family

The older [STRATIFIED_EQUALITY_FAMILY.md](STRATIFIED_EQUALITY_FAMILY.md)
imposes a common seam on all seven anchors and
forces both free squares into the same top layer
with pairwise separated horizontal projections.
The new domain does not require either condition
and permits true oblique F1–F2 separation.
It also includes the two-stack equality witness
[TWO_STACK_SHARP_EQUALITY_WITNESS.md](TWO_STACK_SHARP_EQUALITY_WITNESS.md)
after a quarter-turn of the coordinate frame,
as its four and three vertical projection chains
become the two horizontal chains (1).

**Boundary:** This is a complete equality description
for one **terminal structural class**, not a proof
that every global n=9 equality packing belongs to it.
Such global necessity is precisely G2.X/G5.1 and
remains OPEN. No Lean compilation or kernel audit
is claimed.
