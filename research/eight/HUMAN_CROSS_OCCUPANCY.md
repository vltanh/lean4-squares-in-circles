# A parallel five-square cross cannot be extended to eight below radius two

This note closes the occupancy step left after sections 7--8 of
`HUMAN_GLOBAL_CYCLE_CLOSURE.md`. It is an analytic geometric argument.

**Theorem.** A packing of unit squares in `D_R`, with `R<2`, which contains
five parallel squares with centres

\[
 p,\quad p+(1,0),\quad p+(0,1),\quad
 p-(1,0),\quad p-(0,1)
\tag{1}
\]

contains at most seven squares in total.

Consequently an exterior positive-moment contact cycle in an eight-square
packing below radius two has at least five vertices. The four-cycle
rigidity theorem in `HUMAN_GLOBAL_CYCLE_CLOSURE.md` identifies any such
four-cycle with (1), and the present theorem excludes it.

The remaining unrestricted proof still has to control cycles of length at
least five and cycles through the central square. This result does not
assert the twin-transmitter contact pattern.

## 1. The central cross square is close to the disk origin

Use the common side frame of the five squares, with the disk origin still
at `(0,0)`. Write `p=(alpha,beta)` and `r=|p|`. By reflection and interchange
of coordinates, put `A=|alpha|>=B=|beta|`. One of the cross vertices has
squared norm

\[
 (A+3/2)^2+(B+1/2)^2
   =r^2+\frac52+3A+B<4.
\]

Since

\[
 (3A+B)^2-8(A^2+B^2)=(A-B)(A+7B)\ge0,
\]

we obtain

\[
 r<\sqrt{\frac72}-\sqrt2<\frac{23}{50}.
\tag{2}
\]

For the final rational comparison, `sqrt(7)>529/200` gives

\[
 \left(\sqrt{7/2}-\sqrt2\right)^2
   =\frac{11}{2}-2\sqrt7<\frac{21}{100}
   <\left(\frac{23}{50}\right)^2.
\]

The first comparison is verified by `529^2=279841<280000`.
In particular, `|alpha|,|beta|<1/2`, so the middle square `C` contains the
disk origin in its open interior. This does not need an extra hypothesis
on the cross.

## 2. An outward corner branch cannot cross the horizontal axis

Let `E` be the eastern arm, centred at `p+(1,0)`. Suppose an additional
square `S` is separated from `E` on a side normal of `S` pointing into
the northeast quadrant. Write this unit normal as

\[
 u=(c,s),\qquad c,s>0,\qquad c^2+s^2=1,
\]

and let its perpendicular side direction be `v=(-s,c)`. The lowest vertex
of `S` is

\[
 z_0=p_S-\frac{u+v}{2}.
\]

The northeast vertex of `E` is `p+(3/2,1/2)`. Since `z_0` is on the
near `u` face of `S`, separation implies

\[
 u\cdot z_0\ge u\cdot p+\frac32c+\frac12s.
\tag{3}
\]

We claim that `(z_0)_y>0`. Suppose instead that `(z_0)_y<=0`. The vertex
`w=z_0+u` belongs to `S`, so `|w|<2` and `w_y<=s`. The support of the disk
`D_2` truncated by `y<=s`, in direction `u`, is attained at

\[
 (\sqrt{3+c^2},s).
\]

Indeed the unconstrained disk support point is `2u`, whose height `2s`
exceeds `s`; equivalently, maximizing
`c sqrt(4-y^2)+s y` for `-2<=y<=s` gives the endpoint `y=s`.
Consequently

\[
 u\cdot z_0=u\cdot w-1
 \le c\sqrt{3+c^2}-c^2.
\]

Combining this with (3) yields

\[
 |p|\ge -u\cdot p
 \ge F(c):=\frac32c+\frac12\sqrt{1-c^2}
            -c\sqrt{3+c^2}+c^2.
\tag{4}
\]

We now prove the uniform inequality

\[
 F(c)\ge\frac{71}{152}>\frac{23}{50},
 \qquad 0\le c\le1.
\tag{5}
\]

### 2.1 The range `c>=s`

Since `sqrt(3+c^2)<=2`,

\[
 F(c)\ge c^2-\frac c2+\frac s2.
\]

For `c>=s`,

\[
 1+c-s(1+2c)=(c-s)^2+(c-s)\ge0.
\]

Together with `1-c=s^2/(1+c)`, this implies

\[
 s\ge(1-c)(1+2c).
\]

Thus `F(c)>=1/2`, proving more than (5) in this range.

### 2.2 The range `c<=s`

Now `c<=1/sqrt(2)<3/4` and `s>=1/sqrt(2)>2/3`. Hence

\[
 s=1-\frac{c^2}{1+s}\ge1-\frac35c^2,
\]

and concavity of the square root gives

\[
 \sqrt{3+c^2}
 \le\sqrt3+\frac{c^2}{2\sqrt3}
 <\frac74+\frac3{10}c^2.
\]

Substitution into (4) gives

\[
 \begin{aligned}
 F(c)&\ge\frac12-\frac c4+\frac7{10}c^2-\frac3{10}c^3\\
     &\ge\frac12-\frac c4+\frac{19}{40}c^2\\
     &\ge\frac12-\frac5{152}=\frac{71}{152}.
 \end{aligned}
\]

The last step is the exact minimum of that quadratic. This proves (5).
It contradicts (2), so the lowest vertex in the outward corner branch
satisfies `(z_0)_y>0`, as claimed.

## 3. Every extra square lies in its corresponding actual quadrant

Write `(a,b)=p_S-p` for the centre of an additional square relative to
the cross centre. Section 8 of `HUMAN_GLOBAL_CYCLE_CLOSURE.md` proves that
neither coordinate is zero. Consider the northeast case `a,b>0`.

For clarity, the relevant separating-axis alternatives are recalled here.
If the half-width of `S` on either cross axis is `H`, then `H>=1/2`.
A cross-axis separator from the eastern arm could put `S` above it,
with `b>=H+1/2`. Its lower and left separators contradict `a,b>0`.
Its outward right separator would put the whole square in

\[
 x\ge\alpha+3/2>1,
\]

which is impossible in `D_R`, `R<2`, because a unit square has horizontal
width at least one. Thus the eastern arm has only its upper cross-axis
separator available. Similarly the northern arm has only its right
cross-axis separator available.

If the upper eastern separator is available, the whole square satisfies

\[
 y\ge\beta+1/2>0.
\]

Otherwise the corner-assignment lemma in `HUMAN_STRUCTURAL_LEMMAS.md`
provides a side normal of `S` with signs matching its displacement from
the eastern arm. There are two cases.

* In the northeast case, section 2 proves that the lowest vertex has
  positive height.
* In the northwest case, `a<1`. Therefore the northern arm's right
  cross-axis separator is unavailable, and the northern arm must also
  use a corner separator owned by `S`.

In the second case, put the eastern northwest normal in the form

\[
 u=(-c,s),\qquad c,s>0,
\]

and put `v=(s,c)`. A southeast separator from the northern arm would be
`-u`. The two inequalities with normals `u` and `-u` would add to

\[
 c+s\ge1+c+s,
\]

which is impossible. Indeed each separation has right-hand side
`(1+c+s)/2`, whereas the difference between the northern and eastern
arm centres is `(-1,1)`. Consequently the northern separator is its
northeast one, with normal `v`.

Both `u` and `v` point upward, so the two near faces of `S` meet at its
lowest vertex `z_0`. Put

\[
 q_0=p+(1/2,1/2).
\]

The relevant support vertices of the eastern and northern arms are
`q_0` and `q_0+(0,1)`. The two separator inequalities therefore say

\[
 u\cdot z_0\ge u\cdot q_0,\qquad
 v\cdot z_0\ge v\cdot q_0+c.
\]

Since `(u,v)` is an orthonormal basis, for some `lambda,mu>=0` we have

\[
 z_0=q_0+\lambda u+(c+\mu)v.
\]

In particular,

\[
 (z_0)_y=\beta+\frac12+\lambda s+(c+\mu)c>0.
\]

Every case gives `min_S y>0`. Interchanging the two coordinates gives
`min_S x>0`. Thus an additional square whose centre is northeast of `p`
lies wholly in the **open northeast quadrant about the disk origin**.
Reflection proves the analogous assertion for each of the other three
relative centre quadrants.

This distinction matters: the conclusion concerns every point of the
square, not only the sign of its centre.

## 4. Capacity one in each actual quadrant

Here is a useful elementary fact. Every unit square contained in the open
box `(0,2)^2` contains `(1,1)` in its open interior.

To prove it, let the square's side frame make unsigned angle
`theta` with the axes and put `L=cos(theta)+sin(theta)`, with
`1<=L<=sqrt(2)`. Its half-width on both box axes is `L/2`, so its centre
`q` satisfies

\[
 |q_x-1|<1-L/2,\qquad |q_y-1|<1-L/2.
\]

For either of its unit side normals `n`,

\[
 |n\cdot(q-(1,1))|
 <L(1-L/2)
 =\frac12-\frac{(L-1)^2}{2}\le\frac12.
\]

This is exactly open containment of `(1,1)` in the square. Two such unit
squares cannot have disjoint interiors.

By section 3, every northeast extra square is in `(0,2)^2`, since it is
also in `D_R` with `R<2`. Hence there is at most one extra in that
quadrant. Reflection gives the same capacity for all four quadrants.

Finally, section 8 of `HUMAN_GLOBAL_CYCLE_CLOSURE.md` proves that opposite
relative quadrants cannot both contain extra squares. In its notation,
an extra in quadrant `(epsilon_x,epsilon_y)` forces

\[
 \epsilon_x\alpha+\epsilon_y\beta<2\sqrt2-3<0.
\]

The inequalities for opposite quadrants contradict one another. Thus at
most two quadrants, necessarily adjacent if there are two, can be occupied.
Each holds at most one extra square. The five-square cross therefore has
at most two extra squares, proving the theorem.

## 5. Consequence for the unrestricted contact graph

The four-cycle cut-area theorem in `HUMAN_GLOBAL_CYCLE_CLOSURE.md` shows
that a positive-moment cycle of four exterior squares winding around the
central unit square must be exactly the parallel cross (1). Sections
1--4 now exclude that configuration inside any eight-square packing with
`R<2`. Therefore

\[
 \boxed{\text{Every exterior positive-moment cycle has at least five
 vertices in such an eight-square packing.}}
\]

This is a restriction on arbitrary packings in the stated radius range.
It does not require the five-corner candidate scaffold or assumptions
about which squares touch the disk boundary.
