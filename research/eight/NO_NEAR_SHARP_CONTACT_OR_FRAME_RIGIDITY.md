# No near-sharp packing contact graph or parallel-frame theorem without a minimizer hypothesis

**2026-10-13. Exact global structural counterexample and general
perturbation theorem.** This note is a deliberate course correction
for the unrestricted eight-square sharp-radius proof.

It does **not** refute the candidate sharp radius or the five-corner
projection inequalities. It proves that a proposed global bridge
of the form "every eight-square packing under the search ceiling
must possess some exact contact, common frame, or prescribed
contact graph" is false. Such topology must be extracted at a
true **radius minimizer**, not from the near-sharp radius
ceiling alone.

## Theorem 1. All square contacts can be removed at arbitrarily small radius cost

Let \(S_1,\ldots,S_N\) be genuine closed unit squares
with pairwise disjoint *open* interiors in a disk of
radius \(R_0\) centered at zero. Write
\[
S_i=p_i+K_i,\qquad
K_i=[-1/2,1/2]e_i+[-1/2,1/2]f_i,
\]
where \(e_i,f_i\) is each true orthonormal frame.

**For every \(R>R_0\)** there exists a packing
of \(N\) unit squares contained **strictly inside**
the disk of radius \(R\), with **all closed square
pairs strictly separated**. Moreover every frame
can be perturbed independently through arbitrarily
small angles, so that **no two frames are parallel
modulo quarter turns**.

### Proof

For every unordered pair i≠j, the SAT theorem supplies
one true side normal \(n_{ij}\) of one of the two square
frames, with sign chosen so
\[
n_{ij}\cdot(p_j-p_i)\ge
H_i(n_{ij})+H_j(n_{ij}),                         \tag{1}
\]
where
\(H_i(n)=(|n\cdot e_i|+|n\cdot f_i|)/2\)
is its centered projected half-width.
For every true unit square and every unit n,
\(H_i(n)\ge1/2\), hence the right side is >=1.

Choose \(\lambda>1\), close to one, and **dilate
only the square centers**:
\[
S_i^\lambda=\lambda p_i+K_i.
\]
Do **not** scale the true square side lengths.
Along the same genuine separating direction
\(n_{ij}\), the new signed support gap is
\[
\begin{aligned}
g^\lambda_{ij}
&=\lambda n_{ij}\cdot(p_j-p_i)
-H_i(n_{ij})-H_j(n_{ij})\\
&\ge(\lambda-1)
 [H_i(n_{ij})+H_j(n_{ij})]\\
&\ge\lambda-1>0.                                \tag{2}
\end{aligned}
\]
Thus **every pair of closed whole squares is
strictly separated** in its original legitimate
SAT direction. No geometric contact remains.

Let \(M=\max_i|p_i|\), finite. Every true vertex
of \(S_i^\lambda\) is an original vertex v
translated to \(v+(\lambda-1)p_i\), so
\[
|v+(\lambda-1)p_i|
\le R_0+(\lambda-1)M.
\]
Taking \(\lambda-1>0\) small enough that
\(R_0+(\lambda-1)M<R\) makes **all** true
vertices, hence all whole squares, strictly
inside the larger disk.

There are finitely many positive pairwise gap
margins and positive disk-vertex slack margins.
The vertices and support functions vary
continuously under frame rotation. We may
therefore rotate each frame by a sufficiently
small *independently selected* angle while keeping
all chosen signed projected gaps positive,
and all true vertices inside the disk.
The finitely many forbidden relative frame
angles modulo \(\pi/2\) can be avoided.
This yields all pairwise distinct frame
orientations. QED.

### Immediate sharp-radius consequence

The previously established exact five-corner construction
fits eight genuine unit squares in radius \(\widehat R\).
Consequently **for every** \(R>\widehat R\), however close,
there exist eight-square packings of radius below R with:

* no actual square-square contacts;
* no repeated square-frame orientation modulo \(\pi/2\);
* all vertices strictly inside the disk.

This does **not** tell us whether \(\widehat R\) is
unrestrictedly minimal; it gives a rigorous obstruction
to proving optimality by forcing an exact contact graph
on **all** near-sharp feasible packings.

## Theorem 2. A completely rational eight-square witness at the old search ceiling

Take the explicit eight rational squares
A,B,C,D,E,T,H,G from
[ANALYTIC_RATIONAL_CONSTRUCTION.md](ANALYTIC_RATIONAL_CONSTRUCTION.md),
which have actual half-width-one frames and all true
vertices strictly within the squared-radius ceiling
\[
q_+=9789/2500.
\]
Their six standard squares use frame (1,0),(0,1);
the remaining H,G use the rational Pythagorean frame
\[
e=(255/257,32/257),\quad f=(-32/257,255/257).
\]

Multiply all **centers only** by the exact rational number
\[
\boxed{\lambda=1+10^{-8}}.
\]
For square j=1,...,8 in the order A,B,C,D,E,T,H,G,
rotate its true frame by the exact rational Pythagorean
rotation with half-angle tangent
\[
\boxed{t_j=j/10^{12},\qquad
 \cos\theta_j=\frac{1-t_j^2}{1+t_j^2},\quad
 \sin\theta_j=\frac{2t_j}{1+t_j^2}.}
\]
Every resulting center, vertex, side axis and frame
coordinate is an **exact rational number**, not a
numerical sample or an algebraic limit.

The independent replay
[verify_generic_no_contact_eight_square_packing.py](verify_generic_no_contact_eight_square_packing.py)
constructs the full eight-square packing and proves,
by exact Fraction comparisons over every actual vertex
and every SAT-owner normal:

\[
\boxed{\begin{aligned}
&q_+-|v|^2>\frac1{2{,}000{,}000}
&&\text{for all 32 genuine true vertices }v,\\
&\max_{\text{4 true pair SAT-owner axes}}
 \left(|n\cdot(p_j-p_i)|-H_i(n)-H_j(n)\right)
 >\frac9{10^9}
&&\text{for all 28 actual square pairs }i<j.
\end{aligned}}
\]
The eight frames are pairwise distinct modulo a right angle,
as tested by exact nonzero pairwise frame dot/cross products.
Exactly one square, C, contains zero in its open interior.

This supplies an **entire real eight-square packing**
below the historical research search ceiling
with **no actual contacts anywhere**,
and **no repeated frames**. It does not use the
unknown unrestricted minimum or a stress certificate.

## Precise implication for the sharp proof: what the missing bridge must say

The sharp five-corner projected chain is proved
optimal *conditional on its five directed inequalities*
in [FIVE_CORNER_OPTIMALITY.md](FIVE_CORNER_OPTIMALITY.md)
and [HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md).
A wider exact seven-actual-square **directed-separator**
implication is already proved in
[HUMAN_SHARP_SEVEN_RING_SEPARATOR_CLASS.md](HUMAN_SHARP_SEVEN_RING_SEPARATOR_CLASS.md).

**Neither** conditional theorem has yet been extracted
from *every* competitive eight-square minimizer.

Theorem 1 here rules out a careless intermediate claim
such as "all packings with \(R^2\le q_+\) have the
candidate's contact graph" or "all packings under
this ceiling have six parallel squares".
It **does not disprove** the weaker possibility that all
small packings satisfy certain **inequalities** in
appropriately chosen directed separation axes.
Opening a contact often preserves the corresponding
non-strict projected separator inequality.

For the *next* global theorem, the correct quantifiers are
therefore:

> For **every attained radius minimizer** with
> \(R<\widehat R\), a guaranteed genuine seven-square
> directed-separator chain of the already proved
> sharp class exists, **or** another independent
> sharp-radius obstruction excludes that minimizer.

The proposed theorem is presently **unproved**.
It is enough to study minimizers: if an eight-square
packing of radius \(R<\widehat R\) existed, compactness
of the eight-center/frame feasible set would provide an
attained **global** minimizing packing of radius
\(R_8\le R<\widehat R\).

The research should target that one global bridge,
**not** a universal exact-contact pattern for every
near-sharp nonminimal packing, and not a proliferation
of marginal cap offset estimates. The valid
seven-outer equality contact ring must remain admitted.
