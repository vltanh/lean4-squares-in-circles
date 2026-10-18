# The negative outer-R angular sector in S3/k=3 is impossible

Research continuation, 2026-10-12. This is a **complete elimination of
one of the two previously surviving continuous angular sectors**
in [HUMAN_S3_K3_SHARPER_OUTER_RAYS.md](HUMAN_S3_K3_SHARPER_OUTER_RAYS.md).
It is not a complete rejection of S3/k=3.

## Theorem and exact remaining sector

Let eight independently oriented, pairwise interior-disjoint unit
squares fit inside a disk \(R^2\le9789/2500\). Let C be the
unique origin-containing square, and suppose all seven exterior
square labels have exclusive one-central-side statuses
S3=(3+1,2+1), normalized as
\[
R:3,\quad L:1,\quad U:2,\quad D:1,
\]
with exactly \(k=3\) exterior center norms \(\ge1\).

The previously established facts are
\[
17/200<h_R<13/100,\qquad 17/200<h_U<1/5,
\]
one outer and two inner R-square centers, two inner U centers,
and two far outer L,D singletons. Write \(\psi\) for the polar
angle of the **sole outer R** square center.

The prior exact two-sector theorem gave
\[
-\pi/9<\psi<-2041/10500
\quad\text{or}\quad
311/500<\psi<8959/10500.
\]
The **entire negative sector is impossible**. Hence a surviving
S3/k3 packing would necessarily have
\[
\boxed{311/500<\psi<8959/10500.}                \tag{1}
\]
The remaining positive sector is *not* proved feasible or impossible.

## 1. The negative outer ray would force an inner R radius >9/10

Suppose for contradiction that
\[
-\pi/9<\psi<-2041/10500<-19/100.                \tag{2}
\]
The four inner R/U centers have their strict angular order
\(R_-,R_+,U_+,U_-\), proved in
HUMAN_PERPENDICULAR_FOUR_INNER_CAP_BOUND.md.
In particular \(R_-\) is the inner R-center with negative
y coordinate. Write its angle as \(\theta<0\), its
radius \(r<1\), and note its true **whole right-cap**
center projection
\[
p_{R_-}.x\ge h_R+1/2>117/200.                   \tag{3}
\]

The prior proof
[HUMAN_S3_K3_SHARPER_OUTER_RAYS.md](HUMAN_S3_K3_SHARPER_OUTER_RAYS.md)
establishes that the outer R ray \(\psi\) is
strictly *above* \(\theta\), and their angular separation
is **strictly greater than \(2\pi/9\)**.
(The inner \(R_-\) radius is \(>7/10\), making the proven
mixed inner/outer angle lemma applicable.)

Consequently,
\[
\theta<\psi-2\pi/9
<-19/100-2\pi/9<-22/25.                         \tag{4}
\]
For the last inequality use the elementary bound
\(\pi>25/8\); then \(2\pi/9>25/36>69/100\).

Since \(\theta\in(-\pi/3,0)\), cosine is positive,
and the alternating Taylor **upper** bound for
\(x=22/25\in(0,1)\) gives
\[
\cos|\theta|<\cos(22/25)
\le1-(22/25)^2/2+(22/25)^4/24<13/20.
\]
The exact final margin is
\[
13/20-[1-(22/25)^2/2+(22/25)^4/24]
=57247/4687500>0.
\]
Combining this with (3),
\[
117/200<p_{R_-}.x=r\cos|\theta|<(13/20)r,
\]
and hence
\[
\boxed{r>9/10}.                                 \tag{5}
\]

## 2. Stronger angular exclusion for a radius >9/10 inner center

**Mixed inner/outer angular lemma.**
For two distinct packed square centers in the present
disk range with radii
\[
9/10<r<1,\qquad1\le s<283/200,
\]
their smaller angular separation is
**strictly greater than \(77/100\) radians**.

Proof: let \(x=77/100\). The alternating cosine
Taylor **lower** bound gives
\[
\cos x\ge1-x^2/2+x^4/24-x^6/720>143/200,
\]
with exact rational strict difference
\[
2093489919911/720000000000000>0.
\]
If the angular gap were \(\le x\), then the
cosine law would yield
\[
|p-q|^2<r^2+s^2-(143/100)rs.
\]
The right side is separately convex in r and s.
Its **four exact corner values** over the rectangle
\([9/10,1]\times[1,283/200]\) are
\[
523/1000,\quad12389/12500,\quad
57/100,\quad39151/40000,
\]
all strictly below one. Thus \(|p-q|<1\),
contradicting the disjoint open inscribed
half-unit disks of two distinct packed squares.
The lemma is proved, independent of all
square-frame choices.

## 3. The forced extra angle contradicts the cap projection

Apply the mixed lemma to the inner \(R_-\)
center, whose radius satisfies (5), and the
distinct outer R center at angle \(\psi\).
Their ordinary angular difference is below \(\pi\),
so the mixed lemma and their known order yield
\[
\theta<\psi-77/100
<-19/100-77/100=-24/25.                         \tag{6}
\]
Again \(\theta\in(-\pi/3,0)\), so
\[
p_{R_-}.x=r\cos|\theta|<\cos(24/25).
\]
The alternating cosine Taylor upper bound gives
\[
\cos(24/25)
\le1-(24/25)^2/2+(24/25)^4/24
<117/200,
\]
with strict exact rational difference
\[
117/200-[1-(24/25)^2/2+(24/25)^4/24]
=32533/3125000>0.
\]
Therefore
\[
p_{R_-}.x<117/200,
\]
directly contradicting its required **whole R cap**
projection (3). The negative sector is impossible,
proving (1). QED.

## Exact scope and next problem

This is a genuine **whole angular-sector elimination** for
exclusive S3/k3 at the n=8 disk ceiling, not a sampled
interval result. The other previously allowed
outer R-center sector
\[
311/500<\psi<8959/10500
\]
remains. Its center has positive y coordinate, but
that does **not** assert the complete rotated square
lies inside the NE origin quadrant.

The 2+1 U offset remains in \(17/200<h_U<1/5\),
the R triple offset in \(17/200<h_R<13/100\),
and all individual pair-separating axes remain unfixed.
No unconditional exclusion of S3/k3 or proof of
\(R_8\ge\widehat R\) follows, and the actual S4/k7
sharp equality construction remains untouched.

[verify_s3_k3_negative_sector.py](verify_s3_k3_negative_sector.py)
audits the rational Taylor, cosine-law endpoint and
angle constants, not a computer interval cover
or Lean formalization.
