# Eleven square contact system and isolated attaining family

There is a unique solution of the two exact equations below in the specified
rational rectangle. It produces an eleven-square packing and an explicit
horizontal sliding interval for square 1. Its squared radius is approximately
`4.901206412408145`, and its radius is approximately `2.2138668461332864`.
The existence and local uniqueness certificate uses rational interval
arithmetic and the contraction mapping theorem. No Lean verification is claimed.

This closes exact existence for this candidate family, not unrestricted
optimality. In particular, the seven parallel squares, the two tilted pairs,
and the selected tight constraints are assumptions used to define this family;
they have not been forced on an arbitrary eleven-square packing. Agreement with
Kovacic's published decimal and illustration does not supply a lower bound.

## Parameters and exact equations

The only root variables are the squared radius `q` and the half-angle parameter
`t` for the first tilted pair. Define

\[
 r=\sqrt{q-1/4}-1/2,\qquad w=\sqrt{q-9/4}-1/2,
\]
\[
 v=\frac{2(w-1)}{3+\sqrt{9+4w(w-1)}},\qquad
 c=\frac{1-t^2}{1+t^2},\quad s=\frac{2t}{1+t^2},
\]
\[
 C=\frac{1-v^2}{1+v^2},\quad S=\frac{2v}{1+v^2},\qquad
 c'=cC-sS,\quad s'=sC+cS.
\]

Thus `(c,s)` is the first frame direction and `(c',s')` the second; `v` is the
half-angle parameter for the angle between them. No transcendental quantities
are needed in the definition. In the isolating rectangle, all of `c,s,c',s',C,S`
are positive. Put

\[
 k=(1+c+s)/2,\quad k'=(1+c'+s')/2,\quad K=(1+C+S)/2,
 \qquad z=\frac{w-K+(1-r)S}{C}.
\]

The remaining center coordinates follow a sequence of positive square roots:

\[
\begin{aligned}
 a&=k'-rs',\\
 b&=\sqrt{q-(a+1/2)^2}-1/2,\\
 d&=\sqrt{q-(a+3/2)^2}-1/2,\\
 e&=\sqrt{q-(d-3/2)^2}-1/2,\\
 f&=\sqrt{q-(b-7/2)^2}-1/2,\\
 g&=1/2-\sqrt{q-(f-3/2)^2}.
\end{aligned}
\]

The two closure equations are

\[
\boxed{F_1(q,t)=e-1-k-((1-r)c-zs)=0},
\]
\[
\boxed{F_2(q,t)=s(f-1)-cg-k=0}.
\]

All square roots, divisions, and derivatives in these expressions are defined
on the entire closed isolating rectangle. This is checked by outward rational
interval bounds, including strict positivity of every denominator occurring in
a derivative.

## Square centers and frames

Write `u=(c,s)`, `j=(-s,c)`, `u'=(c',s')`, and `j'=(-s',c')`. Labels agree with
`RATIONAL_WITNESS.json`; its coordinates are the nearby, slightly expanded
rational witness, not the exact coordinates of this family.

| Label | Center | Frame directions |
| --- | --- | --- |
| 0 | `(a,b)` | coordinate axes |
| 1 | `(h,b−1)` | coordinate axes |
| 2 | `(a+1,d)` | coordinate axes |
| 3 | `(e,d−1)` | coordinate axes |
| 4 | `(e−1,b−2)` | coordinate axes |
| 5 | `(f,b−3)` | coordinate axes |
| 6 | `(f−1,g)` | coordinate axes |
| 7 | `−r u` | `u,j` |
| 8 | `(1−r)u+zj` | `u,j` |
| 9 | `−u'+w j'` | `u',j'` |
| 10 | `r j'` | `u',j'` |

The horizontal slider is

\[
H\le h\le a,\qquad H=\frac{k+1-r-s(b-1)}c.
\]

The certificate encloses `H` in `(0.3193235215,0.3193235305)` and `a` in
`(0.3975295040,0.3975295154)`, so this interval is nonempty. These displayed
rational enclosures are deliberately wider than the computed endpoint bounds.

## Derivation from the tight constraints

For a square with frame `(u_i,j_i)`, let its corner `(ε,η)` mean
`p_i+(εu_i+ηj_i)/2`. The ten tight disk constraints are:

| Square | Corner signs |
| --- | --- |
| 0 | `(+,+)` |
| 2 | `(+,+)` |
| 3 | `(+,-)` |
| 5 | `(+,-)` |
| 6 | `(-,-)` |
| 7 | `(-,-)` and `(-,+)` |
| 9 | `(-,+)` |
| 10 | `(-,+)` and `(+,+)` |

Square 7's two equal outer-corner norms force its center to have zero `j`
coordinate; choosing the negative `u` branch gives `p_7=−ru`. Square 10's
analogous two equal norms give `p_10=rj'` on the selected branch. The tight
separator from 9 to 10 in direction `u'` gives `p_9·u'=−1`; its tight corner
then gives `p_9=−u'+wj'` on the selected branch.

A tight separator from 7 to 9 in direction `j` becomes

\[
wC-S=K=(1+C+S)/2.
\]

In half-angle coordinates this is

\[
w v^2+3v+1-w=0.
\]

Since `w>1` here, its positive root is exactly the stable radical expression
for `v` above. The separator from 7 to 8 in direction `u` gives the `u`
coordinate `1−r`. The separator from 8 to 9 in direction `j'` is
`w+(1−r)S−zC=K`, giving the stated expression for `z`.

The fourteen tight pair constraints, for displacement `p_j−p_i`, are:

| Pair `(i,j)` | Signed direction | Total support half-width |
| --- | --- | --- |
| `(0,1)` | `−ey` | `1` |
| `(0,2)` | `ex` | `1` |
| `(0,10)` | `−ex` | `k'` |
| `(1,4)` | `−ey` | `1` |
| `(2,3)` | `−ey` | `1` |
| `(3,4)` | `−ex` | `1` |
| `(4,5)` | `−ey` | `1` |
| `(4,8)` | `−ex` | `k` |
| `(5,6)` | `−ex` | `1` |
| `(6,7)` | `j` | `k` |
| `(7,8)` | `u` | `1` |
| `(7,9)` | `j` | `K` |
| `(8,9)` | `j'` | `K` |
| `(9,10)` | `u'` | `1` |

Each row asserts that the projection of the displacement equals the displayed
support sum. Constraints `(4,8)` and `(6,7)` are precisely `F_1=0` and `F_2=0`.
The remaining twelve follow from the coordinate definitions and
`wC−S=K`. This also explains the right-hand chain of radical formulas rather
than treating the displayed centers as an unexplained numerical fit.

The two additional separator inequalities involving the slider reduce to

- `(1,2)` in direction `ex`: `a+1−h ≥ 1`, equivalent to `h≤a`;
- `(1,8)` in direction `−u`: `ch+s(b−1)−(1−r) ≥ k`, equivalent to `h≥H`.

They become tight at the respective endpoints. The fourteen preceding tight
constraints hold throughout the interval.

## Exact root isolation

Let

\[
x_0=(4.901206412408144,\ 0.2054740374066444),\qquad
B=x_0+[-10^{-9},10^{-9}]^2.
\]

All finite decimals here denote exact rationals. The following rational matrix
is used only as a preconditioner; its entries do not define the geometric
candidate:

\[
M=\begin{pmatrix}
0.41567770&0.45546983\\
0.82609008&-0.56097775
\end{pmatrix}.
\]

Its determinant is nonzero. `isolate_contact_root.py` checks the following
outward bounds on the derivative of the exact function `F=(F_1,F_2)` throughout
`B`:

| Entry | Rational enclosing interval |
| --- | --- |
| `∂F₁/∂q` | `[0.9204730,0.9204731]` |
| `∂F₁/∂t` | `[0.7473516,0.7473520]` |
| `∂F₂/∂q` | `[1.3554791,1.3554793]` |
| `∂F₂/∂t` | `[−0.6820595,−0.6820592]` |

It also checks `|F_i(x_0)|<10⁻¹⁵`. Multiplying this small rational interval
matrix by `M` establishes

\[
\sup_{x\in B}\|I-MDF(x)\|_\infty<10^{-6}.
\]

Define `T(x)=x−MF(x)`. Since `||M||∞<2`, every `x∈B` satisfies

\[
\|T(x)-x_0\|_\infty
\le\|MF(x_0)\|_\infty+10^{-6}\|x-x_0\|_\infty
<3\cdot10^{-15}<10^{-9}.
\]

Thus `T` maps the closed rectangle strictly into itself and contracts distances
by less than `10⁻⁶`. The contraction mapping theorem gives one and only one
fixed point in `B`. Invertibility of `M` makes a fixed point equivalent to
`F=0`. Define `(q_c,t_c)` to be this root. This is an exact specification; the
floating-point diagnostic did not establish existence.

The checker uses `Fraction` arithmetic for all bounds. To enclose `sqrt(x)`
for nonnegative rational `x=N/D`, it computes
`k=isqrt(floor(N·10⁷⁰/D))`, giving the exact enclosure
`[k/10³⁵,(k+1)/10³⁵]`. Interval arithmetic and differentiated interval
arithmetic then enclose the formulas and their first derivatives. Floating
point occurs only in human-readable diagnostic printing.

## Packing verification at the root

The ten tight vertex norms equal `q_c` by the radical definitions. The fourteen
tight separators follow from the displayed identities and `F=0`. The two
slider constraints follow from `H≤h≤a`.

For completeness, the checker evaluates every remaining inequality uniformly
on `B`, allowing square 1's horizontal coordinate to range from the lower
interval bound for `H` to the upper interval bound for `a`. It verifies:

- all 34 remaining vertex inequalities have squared-radius slack `>1/2`;
- all 39 remaining pair inequalities have separator slack `>1/100`.

Together the counts are `10+34=44` vertices and `14+2+39=55` pairs. The
separator directions for the 39 residual pairs are the explicit ones in
`RATIONAL_WITNESS.json`, whose complete pair coverage is checked. No
unlisted pair or boundary case is dropped. Convexity of the disk and the
support-separation argument in `EXACT_UPPER_BOUND.md` now prove an actual
packing for every `h` in the stated interval. Some corners have norm squared
exactly `q_c`, so the disk radius attained by this family is exactly `sqrt(q_c)`.

Run the reproducible exact calculation with:

```sh
python isolate_contact_root.py
```

It imports only standard-library modules, `contact_family.py`, and the JSON
owner list. Running Python with `-O` is rejected because the certificate uses
assertions. This is an exact computer-assisted mathematical certificate,
separate from a future Lean kernel proof.

## What this settles and what it does not

Within this selected branch and isolating rectangle, the two root variables
are fixed and `h` is a nontrivial free parameter. This gives a one-parameter
attaining subfamily. The derivative certificate also makes the root locally
nonsingular. It does not classify every realization of the same contact graph,
every packing with seven parallel squares, or every equality packing of the
unrestricted problem.

The unrestricted lower-bound gate remains open, as do the reduction from an
arbitrary packing to terminal classes and the proof that every global equality
case belongs to a complete listed family. The local root must not be used as
an assumed sharp constant in those arguments without supplying these gates.
