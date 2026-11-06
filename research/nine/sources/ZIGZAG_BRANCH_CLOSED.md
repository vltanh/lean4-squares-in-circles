# n=9: eliminate ALL coordinate-separable four-chain zigzags

**Status: CLOSED as a self-contained table-free hand theorem (2026-10-22).**
This finishes G2.C4.2c: no nine independently oriented unit squares
can have a common-frame coordinate-separated packing, a horizontal
four-square projection chain, and a vertical center zigzag ≥2 in
that chain, at squared containing radius q≤1105/256.

The proof is a whole-branch exclusion. The core is an elementary
three-region capacity contradiction, with no discretized angle boxes,
no optimizers in the final mathematical argument, and no assumption
that the nine square orientations coincide. This does **not** settle
the coherent-side branch or the genuinely oblique-separator branch.

## 1. Necessary center geometry

Fix a frame (horizontal x, vertical y). We use the following
necessary properties of any unit-square packing at
\(q\le q_*=1105/256\):

- **Center radius:** every center \(c\) has
  \[
    \|c\|<\rho:=61/40. \tag{1}
  \]
  Indeed, for a square with orthonormal edge axes u,v,
  its most distant corner has squared norm
  \[
   \|c\|^2+1/2+|c\cdot u|+|c\cdot v|
      \ge\|c\|^2+1/2+\|c\|,
  \]
  and at \(\|c\|=61/40\) this equals
  \(6961/1600>1105/256\).

- **Coordinate separation:** because every pair is
  separated by one of the x/y projections in the
  selected frame, its centers \(c=(x,y),c'=(x',y')\)
  satisfy
  \[
    |x-x'|\ge1\quad\text{or}\quad |y-y'|\ge1. \tag{2}
  \]
  This follows because every independently oriented
  unit square has projection width at least one along
  *either* coordinate axis.

Suppose four squares form a horizontally projection-disjoint
chain \(M_1,M_2,M_3,M_4\), in increasing x-center order.
Then successive x-center differences are at least one;
(1) yields
\[
\begin{aligned}
-61/40&<x_1<-59/40,&
-21/40&<x_2<-19/40,\\
 19/40&<x_3< 21/40,&
 59/40&<x_4< 61/40 . \tag{3}
\end{aligned}
\]
From the radius bound:
\[
 |y_1|,|y_4|<2/5,\qquad
 |y_2|,|y_3|<59/40 . \tag{4}
\]
For the first inequality, use
\((59/40)^2+(2/5)^2>(61/40)^2\).
For the second, use
\((19/40)^2+(59/40)^2>(61/40)^2\).

If some pair of chain centers differs vertically by at
least two, the existing zigzag normal-form argument (or
(1)--(4) directly) says it must be \(M_2,M_3\).
Reflect x if necessary so that
\[
 y_2-y_3\ge2 . \tag{5}
\]
In particular
\[
       y_2>21/40,\qquad y_3<-21/40, \tag{6}
\]
because \(y_3>-59/40\), \(y_2<59/40\).
This strengthening from a half to \(21/40\)
is what excludes an extra square above \(M_2\)
or below \(M_3\) even if its center is close
to the vertical axis:
\[
 y_2+1>61/40,\qquad y_3-1<-61/40. \tag{7}
\]

## 2. A universal outer-strip exclusion

**Lemma 2.1.** Every one of the other five square
centers satisfies
\[
                       -7/5<x<7/5. \tag{8}
\]

*Proof.* If \(x\le-7/5\), then (1) implies
\[
 |y|^2<(61/40)^2-(7/5)^2
     =585/1600<(61/100)^2,
\]
so \(|y|<61/100\).
Also \(|y_1|<39/100\), since from \(|x_1|>59/40\),
\[
 |y_1|^2<(61/40)^2-(59/40)^2
       =3/20 <(39/100)^2.
\]
Consequently \(|y-y_1|<1\).
But since \(-61/40<x_1<-59/40\) and
\(-61/40<x\le-7/5\), we also have
\(|x-x_1|<1/8<1\), contradicting (2).

The case \(x\ge7/5\) uses \(M_4\) by reflection.
\(\square\)

## 3. A left/central/right partition

Put
\[
                  L=x_3-1,\qquad U=x_2+1.
                  \tag{9}
\]
Since the chain has \(1\le x_3-x_2<42/40\),
\[
 -21/40<L<-19/40,\quad
 19/40<U<21/40,\quad
            0<U-L\le1. \tag{10}
\]

Partition the five other centers into:

- **Left:** \(x\le L\).
- **Middle:** \(L<x<U\).
- **Right:** \(x\ge U\).

This is an exhaustive, *three-part* partition
rather than a large positional case grid.

**Lemma 3.1 (left capacity ≤2).**
At most two nonchain centers are left.

*Proof.* By (8), each left x lies in
\((-7/5,L]\), an interval of width
less than
\[
 -19/40+7/5=37/40<1. \tag{11}
\]
Thus any two left centers must be separated
by at least one vertically, by (2).

Every left center also satisfies \(|x-x_2|<1\):
the lower bound follows from x>-7/5
and \(x_2<-19/40\); the upper from
\(x\le L=x_3-1\) and \(x_3-x_2<42/40\).
By (2), it must satisfy
\[
 |y-y_2|\ge1 .
\]
The option \(y\ge y_2+1\) is forbidden by
(1) and (7). Therefore
\[
                        y\le y_2-1<19/40.
                        \tag{12}
\]
Also \(x\le L<-19/40\) together with
(1) gives \(y>-59/40\).
So all left y-coordinates lie in
\[
                 (-59/40,19/40),
\]
an interval of length \(78/40<2\).
Three pairwise vertically separated centers
would need total height span at least two;
hence at most two exist. \(\square\)

**Lemma 3.2 (right capacity ≤2).**
At most two nonchain centers are right.

*Proof.* Reflect the preceding argument,
using \(M_3\) instead of \(M_2\).
Every right center has
\[
 x\in[U,7/5),\qquad
 y\in(-19/40,59/40),
\]
each interval shorter than 1 in x and
shorter than 2 in y. Thus at most two. \(\square\)

**Lemma 3.3 (middle capacity ≤1).**
At most one nonchain center is middle.

*Proof.* For \(L<x<U\), both
\(|x-x_2|<1\) and \(|x-x_3|<1\).
By (2) and (7), the center must satisfy
\[
             y_3+1\le y\le y_2-1.
\]
Using (4) gives
\[
                     -19/40<y<19/40.
                     \tag{13}
\]
Both the x interval \((L,U)\) (length ≤1)
and y interval (13) (length <1) are too
short to hold two coordinate-separated
centers. \(\square\)

## 4. Saturating every capacity is impossible

**Theorem 4.1 (global nine-square zigzag exclusion under
coordinate separability).** Suppose the nine independently
oriented unit squares satisfy the original closed-disk
containment and disjoint-open-interior conditions,
and in one chosen orthonormal frame *every pair*
is separated by at least one of the two coordinate
projections. If a horizontally separated four-chain
has any two center heights differing by at least 2,
then
\[
                    q>1105/256.
\]

*Proof.* Suppose \(q\le q_*\).
Lemmas 3.1--3.3 give capacities at most
\(2+1+2=5\) for the five nonchain squares.
For all five to exist, each region must be
saturated: two left, one middle, two right.

Let \(A,B\) be the left centers ordered by
height \(y_A<y_B\), let \(C\) be the one
middle center, and let \(D,E\) be the right
centers ordered \(y_D<y_E\).

Since the two left x-coordinates differ by
less than one, (2) implies
\(y_B-y_A\ge1\). As \(x_A\le L<-19/40\),
the disk bound gives \(y_A>-59/40\).
Therefore \(y_B>-19/40\); (12) also gives
\(y_B<19/40\). Thus
\[
                       -19/40<y_B<19/40.
                       \tag{14}
\]
Similarly, using \(y_E<59/40\) and
\(y_E-y_D\ge1\), one gets
\[
                       -19/40<y_D<19/40.
                       \tag{15}
\]
The middle center C also has this height
band by (13). The vertical separation
of any two among B,C,D is strictly less
than \(38/40<1\). So (2) forces these
**three** centers to be pairwise separated
by at least one horizontally; in their
actual horizontal order this means
\[
                       x_D-x_B\ge2.
                       \tag{16}
\]

But B has \(|y_B|<19/40\), while the
leftmost chain square \(M_1\) has
\(|y_1|<2/5=16/40\).
Thus \(|y_B-y_1|<35/40<1\).
Coordinate separation (2), together with
\(x_B>x_1\), forces
\[
                     x_B\ge x_1+1>-21/40.
                     \tag{17}
\]
Likewise D has \(|y_D|<19/40\) and M4
has \(|y_4|<16/40\), so
\[
                     x_D\le x_4-1<21/40.
                     \tag{18}
\]
The horizontal order is \(x_B\le L<x_C<U\le x_D\),
and (17)--(18) give
\[
              2\le x_D-x_B<42/40<2,
\]
a contradiction. Thus no ninth packing square
exists under the assumed zigzag and
coordinate-separability hypotheses. \(\square\)

## 5. Scope and next gate

**G2.C4.2c is CLOSED by hand.** There is no residual
4×3 zigzag rank case to enumerate. The complete
coordinate-separable four-chain problem now
reduces to **G2.C4.3 (coherent-sign branch)**,
where the four chain center heights have diameter
strictly less than two.

The argument used the full orientation-independent
corner containment only to derive center radius (1).
It used common-coordinate *pair separation*
to get (2), which is **not** valid for a pair
whose only true separator is oblique.
Therefore the theorem does **not** exclude the
unrestricted oblique-only branch G2.O2/O3.
It does not claim the global n=9 optimum.

No Lean compilation, CI or generated certificate
is needed for the hand argument. An independent
mathematical audit and eventual Lean formalization
have not yet been executed.
