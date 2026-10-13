# Two-square far-cap theorem: both centers outer already at offset 97/200

Research continuation, 2026-10-12. This is a new
**whole-orientation, analytic cap capacity lemma**.
It slightly strengthens the trivial statement
"every center in a whole cap of offset >=1/2 is outer"
to the strict rational threshold \(97/200\)
when **two distinct squares** occupy that cap
under the sharp n=8 disk ceiling.

## Theorem

Let two pairwise interior-disjoint **whole unit squares**,
with unrelated orientations, lie in
\[
D_R\cap\{x\ge h\},
\qquad R^2\le9789/2500,\qquad h\ge97/200.
\]

Then **both** of their centers have Euclidean norm
at least one:
\[
\boxed{|p_1|\ge1\quad\text{and}\quad |p_2|\ge1.}  \tag{1}
\]

No actual mutual contact, common square frame,
or choice of a pair-separating axis is assumed.

## Proof: a one-inner-center contradiction

Assume one of the two centers \(p=(p_x,p_y)\)
has norm strictly less than one. Each whole-square
cap membership gives \(p_x\ge h+1/2\).
Thus \(h<1/2\), since \(p_x<1\);
in particular the theorem is automatic if
\(h\ge1/2\).

Write
\[
a=h+1/2,\quad
a_0=197/200,\quad
A=\sqrt{1-a^2}.
\]
Then
\[
a_0\le a<1,\quad
a\le p_x<1,\quad
|p_y|<A.
\]
The rational square comparison
\[
(173/1000)^2-\left(1-(197/200)^2\right)
=77/500000>0
\]
implies
\[
\boxed{0\le A<173/1000.}                       \tag{2}
\]

Let \(q=(q_x,q_y)\) be the center of the
**other, distinct** square.
The universal farthest-vertex inequality
\(r^2+r+1/2\le9789/2500\) gives
\[
|q|<r_0:=283/200,
\]
with positive integer margin \(65/40000\)
at \(r=r_0\).

The already hand-proved arbitrary-frame
[HUMAN_ONE_SQUARE_CAP_ENVELOPE.md](HUMAN_ONE_SQUARE_CAP_ENVELOPE.md)
applies, because \(h\ge97/200>2/5\).
It supplies
\[
(1+h)^2+(|q_y|+1/2)^2
\le R^2\le9789/2500.
\]
Put \(v=|q_y|\). Then
\[
v\le \sqrt{9789/2500-(1+h)^2}-1/2
\le\sqrt{9789/2500-(297/200)^2}-1/2
<81/100.                                        \tag{3}
\]
The final strict comparison is the exact
positive square difference
\[
(131/100)^2-
\left[9789/2500-(297/200)^2\right]
=229/40000>0.
\]

Because \(q_x\ge a>0\) and \(|q|<r_0\),
\[
a\le q_x<\sqrt{r_0^2-v^2}.
\]
We have \(v<81/100\), and
\[
r_0^2-(81/100)^2-(29/25)^2
=21/40000>0.
\]
Thus
\[
\sqrt{r_0^2-v^2}>29/25>1.                      \tag{4}
\]

Now \(p_x\in[a,1)\), while
\(q_x\in[a,\sqrt{r_0^2-v^2})\).
Since the right endpoint is larger than one,
the absolute x-coordinate difference satisfies
\[
|q_x-p_x|<\sqrt{r_0^2-v^2}-a.
\]
Also \(|q_y-p_y|<v+A\). Consequently
\[
\begin{aligned}
|q-p|^2
&<\left(\sqrt{r_0^2-v^2}-a\right)^2+(v+A)^2\\
&=r_0^2+a^2+A^2
  -2a\sqrt{r_0^2-v^2}+2vA\\
&=r_0^2+1-2a\sqrt{r_0^2-v^2}+2vA.
\end{aligned}
\]
Use \(a\ge197/200\), (2)–(4),
and the positivity of all multipliers to
bound this expression **strictly above** by
\[
\begin{aligned}
|q-p|^2
&< (283/200)^2+1
   -2(197/200)(29/25)
   +2(81/100)(173/1000)\\
&=199457/200000
=1-543/200000<1.                              \tag{5}
\end{aligned}
\]

But two interior-disjoint unit squares have
disjoint open inscribed disks of radius \(1/2\).
Their center distance must therefore be
at least one, contradicting (5).
There cannot be any inner center among the
two cap members, proving (1). QED.

## Exact consequences in the n=8 S2 branch

For the **exclusive S2=(3+0,2+2)** side statuses,
let \(t\) denote the signed central-square
coordinate on the 2+2 axis. The nearer
of the two opposite two-square cap offsets is
\[
h_{\rm near}=1/2-|t|.
\]
The farther cap has offset \(\ge1/2\), hence
its two centers are already outer.

The new theorem says
\[
|t|\le3/200
\quad\Longrightarrow\quad
h_{\rm near}\ge97/200
\quad\Longrightarrow\quad
\text{both nearer cap centers outer}.
\]
The perpendicular triple has at least one
distinct outer-center member, so **k>=5**.
Consequently
\[
\boxed{\text{exclusive S2/k=4 requires }|t|>3/200.} \tag{6}
\]

This is a complete elimination of the closed
**near-centered** 2+2 coordinate strip
\(|t|\le3/200\) from S2/k4,
independent of the square frames or contacts.

The theorem also applies to any other
status branch containing **two distinct
actual whole squares** beyond a central side
whose offset is at least \(97/200\);
overlapping double-side labels must still be
counted correctly. It does not exclude all
S2/k4, all S2, or the S4/k7 sharp equality.

## Audit and scope

[verify_two_outer_high_cap.py](verify_two_outer_high_cap.py)
checks the exact rational square margins in
(2)–(5). The written geometric argument,
not an interval-box cover or a computed
center example, establishes the continuous result.

The unrestricted sharp eight-square lower
bound \(R_8\ge\widehat R\), global equality
classification and Lean formalization
remain OPEN.


## Additional exact S4/k=4 corollary (same whole-cap theorem)

The exclusive all-seven-one-side
S4=(2+1,2+2) status branch contains the
real sharp five-corner equality packing.
This corollary **does not** eliminate S4
or its valid k=7 equality realization.

Let t be the signed central-center
coordinate on its **2+2 axis**.
If \(|t|\le3/200\), both opposite 2+2 side
offsets satisfy
\[
h_{\rm near}=1/2-|t|\ge97/200,\quad
h_{\rm far}=1/2+|t|\ge1/2.
\]
The theorem above forces **both actual
square centers on the nearer side outer**,
and the simpler single-center projection
forces **both on the farther side outer**.
These are four distinct square labels:
opposite whole caps cannot share a unit square.

The perpendicular 2+1 axis also contributes
**at least one distinct outer-center square**.
Indeed if its two-member side offset is
\(\ge1/2\), its two side squares are outer.
Otherwise the opposite one-member cap
has offset \(>1/2\), making its singleton
outer. Since the seven status labels
are exclusive, none of these labels
is one of the four 2+2-axis units.

Thus \(|t|\le3/200\Rightarrow k\ge5\),
and in particular
\[
\boxed{\text{exclusive S4/k=4 requires }|t|>3/200.}
\]
This is a **genuine new signed-offset
exclusion** inside the still-open S4/k4
branch; it does not affect the known
S4/k7 equality configuration.
