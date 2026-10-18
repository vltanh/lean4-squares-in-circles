# A far singleton must cross to negative transverse center sign in a four-inner fan

Research continuation, 2026-10-12. This is a **new continuous-position
rejection** in the remaining low-k all-single-side branches, proved
for arbitrary square frames. It does not assume a contact graph or
parallelism. The precise threshold is the rational offset \(6/25\).

## Theorem (four inner centers, one far opposite outer singleton)

Let five **distinct** interior-disjoint unit squares be contained
in a disk \(D_R\) of squared radius
\[
R^2\le9789/2500.
\]
Four have center norms strictly less than one, with **two whole squares
in each of two perpendicular positive caps**
\[
S_{R,1},S_{R,2}\subseteq\{x\ge h_R\},\quad h_R\ge0,
\]
\[
S_{U,1},S_{U,2}\subseteq\{y\ge h_U\},\quad h_U\ge6/25.
\]
A fifth square \(D\) is **wholly** beyond the opposite signed side
\[
D\subseteq\{y\le-(1-h_U)\}.
\]
Then the actual center of \(D\) has **strictly negative x coordinate**:
\[
\boxed{p_D.x<0.}                                \tag{1}
\]
No frame, physical contact, or minimizer assumption is needed.
The opposite cap offsets \(h_U\) and \(1-h_U\) are complementary,
as for two opposite sides of a central unit square.

### 1. Preliminary inner/outer radial and angular facts

Two different square centers inside the open unit disk, with
mutual distance at least one by their inscribed open
radius-\(1/2\) disks, have smaller center-ray angular
separation strictly greater than \(\pi/3\).
A square center \(p\) at the stated radius ceiling satisfies
\[
|p|<r_0:=283/200,                              \tag{2}
\]
because \(|p|^2+|p|+1/2\le9789/2500\) and the
left side at \(283/200\) exceeds the ceiling
by \(65/40000>0\).

The two U squares both have inner centers, so
[HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md](HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md)
forces
\[
h_U<H_*:=(\sqrt3-1)/2<1/2.                    \tag{3}
\]
In particular, \(D\) is automatically **outer**:
its center y satisfies
\[
p_D.y\le-(3/2-h_U)<-1,
\]
so \(1<|p_D|<r_0\).

Put
\[
\alpha=\arcsin(h_U+1/2)
\ge\arcsin(37/50)>\pi/4.                      \tag{4}
\]
The latter comparison follows from
\((37/50)^2>1/2\).
The four-inner-center angular fan, proved in
[HUMAN_PERPENDICULAR_FOUR_INNER_CAP_BOUND.md](HUMAN_PERPENDICULAR_FOUR_INNER_CAP_BOUND.md),
forces an actual **R inner square with center below
the x-axis**, whose signed angle \(\theta\) satisfies
\[
-\pi/3<\theta<-\alpha.                        \tag{5}
\]

For completeness: each inner pair must have opposite transverse
center signs, so write the R pair as \(R_-,R_+\) and
the U pair as \(U_+,U_-\).
The U rays have angles in \((\alpha,\pi-\alpha)\),
with U_+ in the NE quadrant and U_- in NW.
Their gap \(>\pi/3\) gives
\(\theta_{U_+}<2\pi/3-\alpha\).
The distinct R_+,U_+ inner rays have gap \(>\pi/3\);
they cannot appear in the reverse order because their
angles belong to \((0,\pi/3)\) and \((\alpha,\pi/2)\),
respectively. Therefore
\(\theta_{R_+}<\pi/3-\alpha\).
The R inner-pair gap \(>\pi/3\) now yields
\(\theta_{R_-}<-\alpha\), proving (5).

Let \(r=|p_{R_-}|\). The whole R-cap center projection
\(p_{R_-}.x\ge h_R+1/2\ge1/2\), together with (4)–(5),
gives
\[
r>\frac{1/2}{\cos\alpha}
\ge\frac{25}{\sqrt{1131}}
>\frac{743}{1000}.                            \tag{6}
\]
The last strict comparison is the integer inequality
\[
625000000-743^2\cdot1131=632581>0.
\]

### 2. The southern cap center's polar lane

By (3), the D-square center has
\[
-p_D.y\ge3/2-h_U>2-\sqrt3/2.
\]
Together with (2),
\[
\frac{-p_D.y}{|p_D|}
>\frac{2-\sqrt3/2}{283/200}
>\frac45.                                     \tag{7}
\]
To check the last inequality, use the rational square bound
\(\sqrt3<217/125\), since \(3\cdot125^2=46875<47089=217^2\).
Hence
\(2-\sqrt3/2>283/250=(4/5)(283/200)\).

Suppose for contradiction that \(p_D.x\ge0\).
The D center angle \(\phi\in[-\pi/2,0)\) then satisfies
\[
-\pi/2\le\phi<-\beta,\qquad
\beta:=\arcsin(4/5)>\pi/4.                   \tag{8}
\]
Both \(\theta\) in (5) and \(\phi\) in (8)
belong to \((-\pi,0)\).
We assert that their ordinary angular separation
\(\delta=|\theta-\phi|\) satisfies
\[
\delta<\arccos(37/50).                       \tag{9}
\]
If \(\phi\le\theta\), then
\(\delta\le\theta+\pi/2<\pi/2-\alpha
\le\arccos(37/50)\).
If instead \(\phi>\theta\), then
\(\delta<\pi/3-\beta<\pi/12<
\arccos(37/50)\); the last inequality follows from
\(37/50<\sqrt3/2=\cos(\pi/6)\).
This proves (9), including the endpoint \(p_D.x=0\).

### 3. Exact center-distance contradiction

Write \(s=|p_D|\). By (2), (6) and (9),
\[
743/1000<r<1,\quad 1<s<283/200,\quad
\cos\delta>37/50.
\]
The cosine law yields
\[
|p_{R_-}-p_D|^2
=r^2+s^2-2rs\cos\delta
<r^2+s^2-\frac{37}{25}rs.                   \tag{10}
\]
The last quadratic is convex separately in r and s.
Its maximum on
\([743/1000,1]\times[1,283/200]\) is attained
at a corner. The four rational corner values are
\[
452409/1000000,\quad
4991417/5000000,\quad
13/25,\quad
36321/40000.
\]
All are strictly below one; the greatest is
\[
4991417/5000000=1-8583/5000000<1.
\]
Thus the two **different** square centers have distance
strictly less than one, impossible because distinct unit squares
contain disjoint open inscribed radius-\(1/2\) disks.
The assumption \(p_D.x\ge0\) is false, proving (1). QED.

## Exact remaining-case consequences

**S3/k=3.** Normalize the exclusive-one-side populations as
R=3,L=1,U=2,D=1. The L singleton is outer because
its opposite triple cap offset is \(>17/24\).
If the U cap had offset \(h_U\ge1/2\), its two members
would both be outer; together with L and at least one
outer R member this would force \(k\ge4\).
Hence the opposite D singleton has offset \(1-h_U>1/2\)
and is outer. If **exactly k=3**, the R triple has one
outer and two inner centers, and **both** U centers
are inner. Applying the theorem gives
\[
\boxed{\text{S3/k=3 and }h_U\ge6/25
\quad\Longrightarrow\quad p_D.x<0.}
\]
The older strict upper bound on this offset
\(h_U<(\sqrt{26311}-100)/200\) is retained.

**S1/k=3.** In the exclusive branch R=3,L=0,U=3,D=1,
the D singleton is outer and each of R,U contributes
exactly one outer center. Thus the other two R and
two U centers are inner. If the U (3+1) triple
offset obeys \(h_U\ge6/25\), the **far D
singleton has x center strictly negative**.
The R triple may simultaneously have small offset,
and the conclusion does **not** assert that D is
wholly beyond the central L-side line.

This is a genuine **signed transverse-center exclusion**,
not a full S1 or S3 rejection and not a
bound on any freely rotated square frame.
It does not touch the S4/k=7 candidate equality class.
The unrestricted \(R_8\ge\widehat R\) remains OPEN.
