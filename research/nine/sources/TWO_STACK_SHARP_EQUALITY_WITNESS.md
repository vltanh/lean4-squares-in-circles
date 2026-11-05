# n=9 G2.C3.3: exact sharp two-stack packing — reject the impossible-complement shortcut

**Status: new exact nine-square construction and an exact counterexample to
a proposed G2.C3.3 strategy (2026-10-22).**
This is **not** a packing with radius smaller than the conjectured
\(R_*=\sqrt{1105}/16\), and therefore is not a counterexample to the
target n=9 optimal-radius conjecture.

The key discovery is that even at \(q=Q=1105/256\), a packing can have
a **horizontal four-chain** whose *five-square complement* has longest
horizontal projection-disjoint chain of size **two**. Therefore
"eliminate all residual five-square complements" is an INCORRECT
closure target if it excludes equality. A sharp radius theorem must
include the surviving equality branch.

## 1. Nine unit squares, all axis-aligned

Let the disk center be (0,0) and put
\[
Q=\frac{1105}{256}.
\]

Take the following nine distinct centers (every square has the
ordinary axis-aligned unit frame):

\[
\begin{array}{c|r|r|l}
\text{index}&x&y&\text{role}\\ \hline
M_1&-97/64&0&\text{horizontal four-chain}\\
M_2&-33/64&1/2&\text{horizontal four-chain}\\
M_3&31/64&0&\text{horizontal four-chain}\\
M_4&95/64&0&\text{horizontal four-chain}\\ \hline
E_1&-1/16&-3/2&\text{complement}\\
E_2&-33/64&-1/2&\text{complement}\\
E_3&-1/16&3/2&\text{complement}\\
E_4&15/16&-1&\text{complement}\\
E_5&15/16&1&\text{complement}
\end{array}\tag{1}
\]

The x-gaps in M are exactly one:
\[
 -97/64\;\to\;-33/64\;\to\;31/64\;\to\;95/64.
\]
Hence M is a four-square chain with disjoint horizontal
projection interiors.

### Nonoverlap

For axis-aligned unit squares, two square interiors are disjoint
exactly when their centers differ by at least 1 in x **or** in y.
The nine centers in (1) satisfy this pairwise condition.

A short structural check:
- the four M centers are separated by horizontal center gaps of 1;
- \(E_1,E_2,E_3\) are separated vertically (successive center
  gaps \(1,2\)); \(E_4,E_5\) are separated vertically by 2;
- each remaining cross pair is separated in x or y:
  for example E2 and M2 have the same x but a y-gap of 1;
  E2 and M3 have an x-gap of 1; E4/E5 and E1/E3 have
  an x-gap of 1; and E4/E5 have y-gap at least 1 from
  every M center not horizontally distant enough.
Every pair can also be verified directly from the nine
listed rational center coordinates.

### Exact circle containment

For an axis-aligned unit square of center (x,y), the
maximum squared vertex radius is
\[
 F(x,y)=(|x|+1/2)^2+(|y|+1/2)^2.
\]
The squared-radius *slacks*, in the order of (1), are
\[
 Q-F(c_i)=
 \left(
 \frac{15}{4096},
 \frac{9359}{4096},
 \frac{12687}{4096},
 \frac{527}{4096},
 0,\frac{9359}{4096},0,0,0
 \right).\tag{2}
\]
All nine values are nonnegative, and four are zero.
Thus all nine closed squares lie in the disk of squared
radius exactly Q, and the four pinned exterior squares
touch the boundary.

## 2. The five-square complement really has x-chain length two

Let \(E=\{E_1,\ldots,E_5\}\). The first three
E-squares have x-centers
\[
 -1/16,\ -33/64,\ -1/16
\]
whose range is \(29/64<1\), so no two of their
horizontal projection interiors can be disjoint.

The last two E-squares share x-center \(15/16\), so
they cannot be x-separated from each other.
Hence **every horizontal projection-disjoint chain
in E has at most two members**. There is a two-chain,
for example \(E_2,E_4\), since their center difference
is \(15/16+33/64=93/64>1\).

Therefore \(E\) is exactly the residual
G2.C3.3 five-square complement of the current roadmap.
It is physically realizable at \(q=Q\).

## 3. A perpendicular 4+3 terminal certificate

Although E has no horizontal triple, the **nine-square
packing contains two *disjoint vertical* projection
chains**:

\[
\begin{array}{c|c|c}
\text{vertical chain}&\text{squares}&\text{ordered y-centers}\\\hline
V_4&E_1,E_2,M_2,E_3&-3/2,-1/2,1/2,3/2\\
V_3&E_4,M_3,E_5&-1,0,1.
\end{array}\tag{3}
\]

The successive y-gaps in each chain are exactly 1,
so their open vertical projections do not overlap.
The two chains are disjoint as *sets of squares*.

Rotate the entire frame by a quarter turn and invoke
[SIGNED_MATCHED_CHAIN_STRESS.md](SIGNED_MATCHED_CHAIN_STRESS.md):
the four-chain and three-chain satisfy its
**coordinate-separable terminal** assumptions.
Its exact tangent dual gives \(q\ge Q\), with
equality here.

Thus the current stress technology already explains
the sharpness of this residual example *after a frame
switch*. The open theorem is to show that **every**
residual configuration likewise falls under a proved
sharp certificate (not necessarily these exact chains).

## 4. What is now falsified, and what remains open

**REJECTED:** "No five-square x-chain≤2 complement can coexist
with a horizontal four-chain in a nine-square packing at
\(q\le Q\)." Equation (1) is an exact counterexample.

**OPEN (corrected G2.C3.3 goal):** Given any common-coordinate
separable nine-square packing at \(q\le Q\), a horizontal
four-chain M and five-square complement E with x-chain≤2,
prove one of the following:
1. a pair of disjoint **vertical** 4+3 projection chains
   (as in (3)), so the signed stress applies after a
   quarter-turn;
2. a different explicitly stated already-proved terminal
   stress; or
3. a new short exact terminal inequality with complete
   equality conditions.

At \(q=Q\) equality packings satisfying (1) must be retained,
not erroneously ruled out.

**Research hypothesis, not a theorem:** a “frame-switch
or sharp grid stress” dichotomy may close the entire
two-stack complement without enumerating continuous states.

### Verification scope

All arithmetic in (1)–(3) consists of exact rational
substitution and pairwise coordinate differences.
No optimizer result is a premise. This is an
explicit, independently reproducible construction,
not a Lean kernel proof or a global n=9 lower bound.
