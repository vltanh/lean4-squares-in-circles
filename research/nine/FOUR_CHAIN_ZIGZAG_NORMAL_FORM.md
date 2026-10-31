# n=9 G2.C4.2a — exact normal form of every large-zigzag four-chain

**Status: completed structural hand theorem; arbitrary individual
rotations permitted.** No tilted-angle subdivision or computer
certificate is used.

This resolves the *location* of any large-zigzag pair in a
four-square horizontal projection chain. It does **not**
exclude the whole nine-square zigzag packing branch: the
other five squares must still be counted.

## 1. Coarse universal center radius (one simple rational)

Let a freely oriented unit square of center c and orthogonal
unit side axes u,v fit in a disk centered at zero with
\[
 q\le q_*=\frac{1105}{256}.
\]
The maximum squared corner norm is
\[
 \|c\|^2+\frac12+|c\cdot u|+|c\cdot v|
 \ge \|c\|^2+\frac12+\|c\|. \tag{1}
\]
Put \(\rho=61/40\). The right-hand side at
\(\|c\|=\rho\) is
\[
 \rho^2+\rho+\frac12
   =\frac{6961}{1600}
   >\frac{1105}{256}=q_*. \tag{2}
\]
Hence **every square center** in such a packing satisfies
\[
                       \|c\|<\frac{61}{40}. \tag{3}
\]
This is an exact, orientation-independent radius bound.

## 2. Four-chain x-center quantization

Suppose four of the squares have pairwise disjoint
horizontal projection interiors. Order their
centers by x as \(M_1,M_2,M_3,M_4\).
Since each unit square has horizontal half-projection
width at least \(1/2\), neighboring centers differ
by at least one unit:
\[
                 x_{i+1}-x_i\ge1. \tag{4}
\]
Apply (3) to the endpoints and use the three
consecutive gaps (4). Then
\[
\begin{aligned}
 -\frac{61}{40}&<x_1<-\frac{59}{40},\\
 -\frac{21}{40}&<x_2<-\frac{19}{40},\\
  \frac{19}{40}&<x_3< \frac{21}{40},\\
  \frac{59}{40}&<x_4< \frac{61}{40}.
\end{aligned}\tag{5}
\]
For example, \(x_1\le x_4-3<61/40-3=-59/40\)
and \(x_2\le x_4-2<-19/40\),
while \(x_2\ge x_1+1>-21/40\).
The remaining bounds are symmetric.

Thus, without any common-orientation hypothesis,
a four-projection chain has its centers **forced
into four disjoint narrow columns near
\(-3/2,-1/2,1/2,3/2\)**. This is not an
assumption of exact grid alignment.

## 3. Every large zigzag is between the two middle squares

**Theorem 3.1.** Under (1)--(5), the two extreme
chain centers obey
\[
             |y_1|<\frac25,\qquad
             |y_4|<\frac25. \tag{6}
\]
Consequently, if any two chain-square centers
have vertical difference at least 2, those
two squares are necessarily \(M_2,M_3\).

*Proof.* By (5), \(|x_1|,|x_4|>59/40\).
If either outside center had \(|y|\ge2/5=16/40\),
its squared norm would be greater than
\[
 \frac{59^2+16^2}{40^2}
 =\frac{3737}{1600}
 >\frac{3721}{1600}=\left(\frac{61}{40}\right)^2,
\]
contradicting (3). This proves (6).
Every other center satisfies \(|y_i|<61/40\).
The height difference between an outer center and
any center is therefore strictly smaller than
\[
                \frac25+\frac{61}{40}
                =\frac{77}{40}<2.
\]
Differences between the two outside centers are
even smaller. Only the pair \(M_2,M_3\) can
be separated vertically by 2 or more. \(\square\)

**Corollary 3.2 (sharp qualitative order of the zigzag).**
If \(|y_2-y_3|\ge2\), then one middle-chain
center lies above \(1/2\), the other below \(-1/2\);
both outside-chain centers lie strictly between them
in vertical order.

*Proof.* From (5), \(|x_2|,|x_3|>19/40\).
If an inner chain center had \(|y|\ge3/2\),
then
\[
 \|c\|^2 >\left(\frac{19}{40}\right)^2
                  +\left(\frac32\right)^2
   =\frac{3961}{1600}
   >\frac{3721}{1600},
\]
contradicting (3). So \(|y_2|,|y_3|<3/2\).
If the higher center is at least 2 above the
lower, it must exceed \(1/2\), and the
lower must be below \(-1/2\).
By (6) the two outside centers have
absolute heights below \(2/5<1/2\).
\(\square\)

## 4. Global cap capacity for squares outside the zigzag

**Lemma 4.1 (at most one square above the upper inner chain
square).** Assume the zigzag of Corollary 3.2.
Among all other squares entirely above the higher
of \(M_2,M_3\) in vertical projection, there is
at most **one** unit square. Symmetrically, at most
one other square can be entirely below the lower
of \(M_2,M_3\).

*Proof.* The upper middle square has center height
\(y_H>1/2\). Its vertical projection halfwidth
is at least \(1/2\). Any other square T entirely
above it in vertical projection must have
\[
 y_T\ge y_H+h_H+h_T >\frac32.
\]
By the universal center radius (3), its center
must obey
\[
 |x_T|<
 \sqrt{\left(\frac{61}{40}\right)^2
                  -\left(\frac32\right)^2}
 =\frac{11}{40},\qquad
 \frac32<y_T<\frac{61}{40}. \tag{7}
\]
For any two such T and U, the squared distance
between their centers is strictly less than
\[
 \left(\frac{22}{40}\right)^2+
 \left(\frac{1}{40}\right)^2
   =\frac{485}{1600}<1. \tag{8}
\]
But two unit squares with disjoint open interiors
have centers at Euclidean distance **at least 1**:
their open inscribed disks, of radius \(1/2\),
must be disjoint as well. This contradicts (8).
Therefore at most one T exists. Reflecting
the y coordinate proves the lower cap statement.
\(\square\)

This cap lemma is global for independently oriented
squares and does not use common coordinate
separation of T and U.

## 5. Remaining exact tasks

**C4.2a CLOSED:** all large zigzags necessarily involve
only M2 and M3, with opposite signs and the
two extreme centers in the intervening horizontal
band; each far cap holds at most one additional square.

**C4.2b OPEN:** in the coordinate-separable class,
prove that the other five squares cannot be placed
around this quantized zigzag without triggering
one of the already proved sharp stress certificates.
The shadow incidence blocks in
[FOUR_CHAIN_SHADOW_BARRIER.md](FOUR_CHAIN_SHADOW_BARRIER.md)
give the finite combinatorial framework. Counting only
the top and bottom caps is not enough: squares may
occupy different sides of the inner pair or
be horizontally disjoint from one inner chain square.

**C4.2c OPEN (unrestricted oblique branch):**
an extra square whose horizontal projection overlaps
an inner chain square may still be separated from it
along an *oblique own-edge axis*. The vertical cap
capacity only applies when complete vertical order is
actually established. This case belongs to G2.O2/O3,
not to an unproved universal vertical-separation assumption.

No unrestricted n=9 theorem, global equality classification,
Lean, CI or kernel verification is claimed.
