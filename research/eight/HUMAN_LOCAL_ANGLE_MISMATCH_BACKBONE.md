# Transfer from 11SquaresOptimal: exact local angle-mismatch penalties for the eight-square separator backbone

**2026-10-13. A worked, full-orientation LOCAL hand theorem.**
Motivated by the independent-angle mixed-support argument in
https://github.com/Queuingtheorydotcom/11SquaresOptimal
(paper/eleven-squares-synthesis.tex, section
"A mixed support inequality with independent angles").

**This is not the unrestricted sharp eight-square radius proof.**
It rigorously demonstrates that **five real support edges of the
eight-square construction admit a positive linear angular-mismatch
penalty**, with every square frame independently allowed to rotate,
*without physically rotating a packing into alignment*.
It identifies the exact missing global bridge as **capture/selection
of the correct directed separator families**, followed by a weighted
support dual controlling the remaining changes.

## 1. A pairwise independent-angle separator lemma

Let P,Q be genuine nonoverlapping unit squares, centers p,q, frames
with angles \(\alpha,\beta\), and fix a nominal unit normal \(n_0\)
and nominal frame angle \(\alpha_0\). Assume the two current
corresponding candidate separating axes are
\[
n_P=R_{\alpha-\alpha_0}n_0,\qquad
n_Q=R_{\beta-\alpha_0}n_0.
\]
In this paragraph both \(\alpha,\beta\) are framed
near the **same** nominal orientation \(\alpha_0\),
and n_0 is a true *side normal* of that frame.

Suppose true square separation occurs along at least one
of the **positively oriented** \(n_P,n_Q\) axes.
Put
\[
m=\tfrac12(\alpha+\beta)-\alpha_0,\quad
\delta=\tfrac12(\beta-\alpha),\quad
N=R_mn_0,\quad M=JN,
\]
\[
X=N\cdot(q-p),\qquad Y=M\cdot(q-p).
\]
Assume \(|\delta|<\pi/4\), so \(\cos\delta>0\).
Then the actual SAT support half-width sum on
either chosen candidate axis equals
\[
W=\tfrac12(1+\cos(2\delta)+|\sin(2\delta)|)
 =\cos\delta(\cos\delta+|\sin\delta|).
\]
The larger of the two projected directed center gaps equals
\[
\max\{n_P\cdot(q-p),n_Q\cdot(q-p)\}
 =X\cos\delta+|Y\sin\delta|.
\]
Nonoverlap in the assumed owner family therefore implies
\[
X\cos\delta+|Y\sin\delta|
 \ge \cos\delta(\cos\delta+|\sin\delta|).
\]
Divide by \(\cos\delta\) to obtain the exact
**independent-angle mismatch inequality**
\[
\boxed{X-\cos\delta
 \ge(\cos\delta-|Y|)|\tan\delta|.}              \tag{1}
\]

If \(|\delta|\le D\) and \(|Y|\le B\), where
\(\eta=1-D^2/2-B>0\), elementary
\(\cos\delta\ge1-D^2/2\) and
\(|\tan\delta|\ge|\delta|\) sharpen (1) to
\[
\boxed{X-\cos\delta
 \ge\tfrac{\eta}{2}|\alpha-\beta|.}            \tag{2}
\]
**This lemma itself does not assume any common frame.**
It requires a *justified true SAT owner family*,
a transverse-displacement bound, and a small angle difference.

## 2. The five actual candidate backbone edges

Use the completely rational full eight-square packing
in [ANALYTIC_RATIONAL_CONSTRUCTION.md](ANALYTIC_RATIONAL_CONSTRUCTION.md).
Its standard-frame square centers are
\[
\begin{aligned}
p_A&=(r-\tfrac12,\tfrac12-u),&
p_B&=(U-\tfrac12,\tfrac32-u),\\
p_T&=(U-\tfrac32,\tfrac{27}{20}),&
p_D&=(U-\tfrac52,\tfrac32-v),\\
p_E&=(\tfrac12-w,\tfrac12-v),
\end{aligned}
\]
and its tilted pair has \(p_G-p_H=e\) where
\(e=(255/257,32/257)\). All six other standard
squares (including the middle C, unused here)
have the horizontal/vertical frame.

For the following **five** directed square pairs,
fix the listed nominal true side normal n0.
Each base displacement has the form
\[
d_0=q_0-p_0=n_0+Y_0\,Jn_0,
\]
so its normal projection is exactly one,
with the following **exact rational transverse
components**:

| Pair directed from P to Q | Nominal side normal n0 | Exact Y0 |
| --- | --- | ---: |
| A → B | vertical (0,1) | \(24441/250000\) |
| T → B | horizontal (1,0) | \(-23/30\) |
| D → T | horizontal (1,0) | \(397767/1000000\) |
| E → D | vertical (0,1) | \(-111471/200000\) |
| H → G | tilted e=(255/257,32/257) | \(0\) |

These five actual projected contacts form
a connected **standard-frame orientation tree**
A--B--T--D--E and a separate tilted
two-square orientation edge H--G.
They intentionally leave the **relative
standard/tilted angle free**, because the
sharp candidate uses a genuine nonzero tilt.

The arithmetic gives
\[
\boxed{|Y_0|\le23/30<1,\qquad
       |d_0|^2=1+Y_0^2<9/4}                   \tag{3}
\]
for all five pairs (with equality
in the first bound only for T--B).
The exact-fraction companion
[verify_eight_angle_mismatch_backbone.py](verify_eight_angle_mismatch_backbone.py)
recomputes these statements from the
complete rational eight-square coordinates.

## 3. A concrete independent-frame neighborhood with a UNIFORM penalty

Consider ANY genuine packing of these eight unit-square
labels, allowing **all centers and square frames
to move independently**, in which, for the
seven labels A,B,T,D,E,H,G:

* each center has Euclidean distance at most
  \(\varepsilon=1/50\) from its rational
  base construction center;
* each square's frame angle differs by
  at most \(\varepsilon=1/50\) **radians**
  from its own base frame, with the same
  local mod-quarter-turn angle representative.

No central C or circle-contact topology is
assumed in this local statement. The square
pair interiors remain disjoint by hypothesis.

We prove that for **each of the five listed
pairs**, the genuine SAT separating axis is
necessarily one of the two **positively oriented
corresponding nominal side normals** \(n_P,n_Q\)
and its midpoint-frame support gap satisfies
the **strictly positive independent-frame penalty**
\[
\boxed{
g_{PQ}
:=N\cdot(q-p)-\cos\frac{\beta-\alpha}{2}
\ge\frac7{100}|\alpha-\beta|.
}                                                   \tag{4}
\]
Here \(\alpha,\beta\) are the corresponding
current frame angles and N is their
nominal-frame midpoint normal defined above.

### 3(a). True SAT ownership is forced locally, not assumed

Fix one edge. From the base displacement (3),
\(|d_0|<3/2\). The two independently moved
centers give \(|d-d_0|\le2\varepsilon\).
Each actual owner axis differs in direction
from its nominal n0 by at most epsilon,
so the standard unit-vector rotation bound
\[
|R_\theta v-v|\le|\theta|
\]
gives an actual **perpendicular owner axis** b
with
\[
|b\cdot d|
\le |(Jn_0)\cdot d_0|
     +2\varepsilon+\varepsilon|d_0|
<\frac{23}{30}+\frac7{100}
=\frac{251}{300}
<\frac{17}{20}<1.                              \tag{5}
\]
For **any** direction b, the summed
half-widths of two true unit squares
are at least one:
\[
H_P(b)+H_Q(b)\ge1.
\]
Therefore **no perpendicular owner axis
of either square can separate the pair**,
regardless of frame tilt or center movement.

The directed projection along either
corresponding nominal owner axis stays
**positive**:
\[
n_P\cdot d>1-\frac7{100}>0,\qquad
n_Q\cdot d>1-\frac7{100}>0,
\]
because the base normal displacement is exactly one.
Thus the *negative* directions \(-n_P,-n_Q\)
cannot be true directed separators either.

The genuine square SAT theorem guarantees
at least one of the four true side-normal
axis families separates the disjoint
interiors. The only remaining choices are
the two positively oriented desired axes
\(n_P,n_Q\). Their disjunction is now
**proved** throughout the entire chosen
seven-square pose neighborhood, not
guessed from the candidate's drawn
contacts.

### 3(b). A uniform rational mismatch reserve

Let N be the midpoint normal.
Its angular deviation from nominal n0
is at most epsilon. The exact same
rotation estimate gives
\[
|Y|\le|Y_0|+2\varepsilon+
  \varepsilon|d_0|
<\frac{251}{300}<\frac{17}{20}.                \tag{6}
\]
Because each two frame angles deviate
at most epsilon from their shared
nominal frame, the half-difference
obeys \(|\delta|\le\varepsilon=1/50\).
Thus
\[
\begin{aligned}
\eta&=1-\frac{\varepsilon^2}{2}
          -\frac{17}{20}
=1-\frac1{5000}-\frac{17}{20},\\
\frac{\eta}{2}-\frac7{100}
&=\boxed{\frac{49}{10000}>0}.
\end{aligned}
\]
Apply the independent-angle separator lemma
(2) with \(D=\varepsilon\), \(B=17/20\).
The strictly positive reserve proves (4).
It holds for every permitted independently
rotated frame in the stated neighborhood. QED.

## 4. The exact opening for the sharp eight-square problem

The **original sharp seven-square support
theorem** [HUMAN_SHARP_SEVEN_RING_SEPARATOR_CLASS.md](HUMAN_SHARP_SEVEN_RING_SEPARATOR_CLASS.md)
requires A and E to have the same standard
side frame, with the other frames mostly free.
Its missing unrestricted bridge had
attempted to **force exact A/E frame equality
from an arbitrary minimizer**, which is
more rigid than the 11SquaresOptimal
mixed-angle strategy requires.

The complete transfer shown here indicates
a more plausible comparison:

1. Extract the **correct directed support
   owner families** and enough center/frame
   bounds to guarantee (4), by a geometric
   capture theorem about *actual radius
   minimizers* or hypothetical
   radius-\(<\widehat R\) configurations.
2. Form one **weighted five-corner/seven-square
   support functional** \(S(\boldsymbol\theta,t)\)
   whose value at common standard-frame
   angles is the already proved sharp
   conditional five-corner inequality.
3. Use the five positive mismatch penalties
   (4), and exact derivative bounds of
   this weighted functional, to **contract
   the frame arguments along the standard
   tree A--B--T--D--E and tilted edge H--G**.
   The argument must compare scalar
   functions, **not physically rotate
   a purported packing**.
4. Leave one genuine **relative tilt
   parameter** between the standard
   cluster and tilted cluster, to be
   optimized by the existing sharp
   five-corner family theorem.
5. A global **capture of all minimizer
   alternatives** (or a distinct
   sharp inequality for uncaptured
   alternatives) is still required.

A **critical missing inequality** is the
positive dual margin needed to dominate
the derivatives of S along the five
angle-contraction edges.
The fact that each edge has a
positive penalty **does not by itself**
show the weighted sum can pay for all
angle derivatives. That quantitative
comparison is the next isolated
mathematical test, and failure of it
would tell us to use a different
dual support choice or a larger pose
region.

**This local lemma is not a global
sharp radius proof, not a proven
capture theorem, not a global
two-end alignment theorem, and not
a Lean formalization.**
It provides a concrete checked
transfer from the 11SquaresOptimal
method to a real, verified eight-square
support geometry, with an exact
rational orientation-mismatch reserve.
