# Appendix B. The critical gap: set-up and the easy axes

[Contents](README.md) · [← Appendix A](appendix-a.md) · [Appendix C →](appendix-c.md)

Appendices B, C and D prove the critical-gap proposition
([Proposition 9.17](seven.md#proposition-917-the-critical-gap)): for admissible states $(a, u)$ and $(A, v)$ and all
signs $s, t \in \lbrace 1, -1\rbrace$, the support sums of the canonical pair at
the gap $\frac\pi3$ satisfy $\sigma_k(\frac\pi3) \ge 0$ on every axis $k$, with
equality only if the two states with these signs form a contact. The proof is a
case analysis over *sectors*: an axis, a pair of signs, and the kinds of the two
labels. This appendix lays out the sectors (§B.1), collects the tools that
Appendices C and D share (§B.2 to §B.6), settles the four sectors that need no
condition on the labels (§B.7), reduces capped labels to active ones (§B.8), and
assembles the proof (§B.9). Appendix C treats the remaining sectors of the
inward axis and Appendix D those of the forward axis.

We use the notation of Chapter 9. A *state* is a pair $(a, u)$ with
$\frac12 \le a$ and $0 \le u \le a$, *admissible* if
$\varphi(a, u) = (a + \frac12)^2 + (u + \frac12)^2 \le \frac{13}4$
([Definition 9.4](seven.md#definition-94-states)); its remainder is $r(a, u) = 4 - 3a - 2u$
([Definition 9.4](seven.md#definition-94-states)). The label is
$\ell(a, u) = \min(\mathrm{axial}(u), \mathrm{side}(a, u), \frac\pi4)$ with
$\mathrm{axial}(u) = \frac54 u$ and
$\mathrm{side}(a, u) = \frac\pi6 + \frac13(u - \frac12) + \frac34(1 - a)$
([Definition 9.6](seven.md#definition-96-labels-and-markers)). It is *axial*, *side* or *capped* when it equals the first,
second or third term, and *active* when it is axial or side; since a minimum of
three numbers is one of them, every label is axial, side or capped. The support
function of the axis-parallel unit square centred at $(x, y)$ is
$h(x, y, z) = x\cos z + y\sin z + \frac12(|\cos z| + |\sin z|)$
([Definition 9.10](seven.md#definition-910-support-function)).

In the canonical pair of two states $(a, u)$ and $(A, v)$ with signs $s, t$ at
the gap $g$ ([Definition 9.12](seven.md#definition-912-canonical-pair-and-support-sums)), the square $S = Q(a, su)$ is the *source* and
the square $T$, whose frame is turned by the relative phase
$d = g + s\,\ell(a, u) - t\,\ell(A, v)$ and which sits at $(A, tv)$ in that
frame, is the *target*. Accordingly $(a, u)$, $s$ and $\ell = \ell(a, u)$ are
the source state, sign and label, and $(A, v)$, $t$ and $\ell' = \ell(A, v)$ the
target ones. The support sums are

```math
\sigma_k(g) = h\left(a, su, k\tfrac\pi2\right) + h\left(A, tv, k\tfrac\pi2 + \pi - d\right)
= \max_{\overline S}\,\langle \cdot, n_k\rangle - \min_{\overline T}\,\langle \cdot, n_k\rangle ,
\qquad n_k = u\left(k\tfrac\pi2\right),
```

and in the chart of $S$ the normal $n_0$ points away from the disk centre (the
*outward* axis), $n_2$ towards it (*inward*), $n_1$ in the direction of
increasing angle, towards the marker of $T$ (*forward*), and $n_3$ the other way
(*backward*).

## B.1 The plan

### Definition B.1 (the gap property)

Let $(a, u)$ and $(A, v)$ be admissible states, $s, t \in \lbrace 1, -1\rbrace$
signs and $k \in \lbrace 0, 1, 2, 3\rbrace$ an axis. The two states with the
signs $s, t$ have the *gap property on the axis $k$* if
$\sigma_k(\frac\pi3) \ge 0$, and $\sigma_k(\frac\pi3) = 0$ only if they form a
contact ([Definition 9.15](seven.md#definition-915-contacts)). As above, a label is *active* if it is axial
or side.

So the critical-gap proposition ([Proposition 9.17](seven.md#proposition-917-the-critical-gap)) says that any two
admissible states, with any signs, have the gap property on every axis.

*Lean: [`Seven.PairProperty`](../../SquaresInCircles/Seven/Contacts.lean#L69),
[`Seven.ActiveLabel`](../../SquaresInCircles/Seven/Contacts.lean#L65).*

### Lemma B.2 (zeros at contacts)

Let $(a, u)$ and $(A, v)$ be admissible states.

1. If $r(a, u) = 0$, then $(a, u) = (1, \frac12)$, the side state.
2. If $v = 0$, then $(A, v)$ is an axial state:
   $\frac12 \le A \le \sqrt3 - \frac12$.
3. $\ell(1, \frac12) = \frac\pi6$, and every axial state has label $0$.
4. If $\sigma_k(\frac\pi3) > 0$ for the signs $s, t$, then the two states with
   these signs have the gap property on the axis $k$.
5. Let $t$ be a sign, $k$ an axis and $c > 0$. Suppose that the label of
   $(A, v)$ is axial, put $e = \ell(a, u) - t\,\ell(A, v) - \frac\pi6$, and
   suppose that for the signs $(1, t)$

   ```math
   \tfrac2{15}\, r(a, u) + c\,|e| \le \sigma_k\left(\tfrac\pi3\right) .
   ```

   Then the two states with the signs $(1, t)$ have the gap property on the axis
   $k$, and $\sigma_k(\frac\pi3) = 0$ only if $(a, u)$ is the side state and
   $(A, v)$ is axial.

*Proof.* Parts (1), (2) and (3) are parts (2), (3) and (1) of [Lemma 9.16](seven.md#lemma-916-contacts), and
part (5) is its part (5), stated with the gap property of Definition B.1.
Part (4) holds because a positive number is nonnegative and not zero.
$\square$

*Lean:
[`Seven.PairProperty.of_pos`](../../SquaresInCircles/Seven/Contacts.lean#L73),
[`Seven.PairProperty.of_side_axial`](../../SquaresInCircles/Seven/Contacts.lean#L80),
[`Seven.remainder_zero`](../../SquaresInCircles/Seven/Contacts.lean#L24),
[`Seven.axial_of_transverse_zero`](../../SquaresInCircles/Seven/Contacts.lean#L31),
[`Seven.side_label`](../../SquaresInCircles/Seven/Contacts.lean#L34),
[`Seven.axial_label`](../../SquaresInCircles/Seven/Contacts.lean#L41).*

![Four copies of the same canonical pair: a blue source square S with its centre to the right of the disk centre o and a green target square T turned by about 71 degrees above it, overlapping S at a corner, with dashed rays from o to the two markers on a faint unit circle. In each copy a grey line in the direction of one normal carries the blue shadow of S and the green shadow of T, and an orange bracket marks the support sum: on the outward and backward axes it spans both shadows, on the forward and inward axes it is the overlap of the shadows](figures/appb-pair-axes.svg)

*Figure B.1.* A canonical pair at the gap $\frac\pi3$, with the source state
$(0.95, 0.35)$, the target state $(1, 0.2)$ and both signs $1$. In the panel of
the axis $k$ the shadows of $S$ (blue) and $T$ (green) on the line of $n_k$ are
drawn beside the squares, and the orange bracket has the length
$\sigma_k(\frac\pi3)$: it runs from the lowest point of $T$ to the highest point
of $S$ along $n_k$. The sum would be negative if the shadows were disjoint with
$T$ ahead of $S$ along $n_k$.

The sectors are listed in the table below. The labels $\ell$ and $\ell'$ are
those of the source and the target; *any* means that the row holds for all
admissible states, whatever their labels. A row marked *positive* proves
$\sigma_k(\frac\pi3) > 0$; the other rows prove the gap property and name the
only contact at which the sum can vanish (the contacts of
[Definition 9.15](seven.md#definition-915-contacts), numbered (1) to (3) as there: two side states with
signs $(-1, 1)$; a side state and an axial state with source sign $1$; an axial
state and a side state with target sign $-1$).

| axis | signs $(s, t)$ | labels $\ell$, $\ell'$ | result | statement |
| --- | --- | --- | --- | --- |
| $0$, outward | all | any, any | positive | Proposition B.26 |
| $3$, backward | all | any, any | positive | Proposition B.27 |
| $2$, inward | $(-1, 1)$, $(-1, -1)$ | any, any | positive | Proposition B.28 |
| $2$, inward | $(1, 1)$ | axial, axial | positive | ([Proposition C.6](appendix-c.md#proposition-c6-two-axial-labels)) |
| $2$, inward | $(1, 1)$ | side, axial | zero only at contact (2) | ([Proposition C.7](appendix-c.md#proposition-c7-side-source-axial-target)) |
| $2$, inward | $(1, 1)$ | any, side | positive | ([Proposition C.12](appendix-c.md#proposition-c12-side-target)) |
| $2$, inward | $(1, -1)$ | active, active | zero only at contact (2) | ([Theorem C.32](appendix-c.md#theorem-c32-opposite-signs-with-active-labels)) |
| $1$, forward | $(1, 1)$ | any, any | positive | Proposition B.29 |
| $1$, forward | $(1, -1)$ | any, active | zero only at contact (3) | ([Proposition D.7](appendix-d.md#proposition-d7-target-sign-negative)) |
| $1$, forward | $(-1, -1)$ | axial, active | zero only at contact (3) | ([Proposition D.7](appendix-d.md#proposition-d7-target-sign-negative)) |
| $1$, forward | $(-1, -1)$ | side, active | positive | ([Proposition D.26](appendix-d.md#proposition-d26-both-signs-negative)) |
| $1$, forward | $(-1, 1)$ | active, active | zero only at contact (1) | ([Proposition D.16](appendix-d.md#proposition-d16-opposite-signs)) |

The rows cover every sector in which both labels are active (Proposition B.32),
and Proposition B.31 reduces capped labels to active ones: a capped state is a
convex combination of the three vertices of a triangle, at which the labels are
active, and every support sum is affine in a state of constant label.

## B.2 Support sums in closed form

### Lemma B.3 (Cauchy–Schwarz on the disk)

Let $X, Y$ be real numbers with $X^2 + Y^2 \le \frac{13}4$, and let $p, r, c$ be
real numbers with $c \ge 0$.

1. $(pX + rY)^2 \le \frac{13}4(p^2 + r^2)$.
2. If $\frac{13}4(p^2 + r^2) \le c^2$, then $pX + rY \ge -c$. If
   $\frac{13}4(p^2 + r^2) < c^2$, then $pX + rY > -c$.

For an admissible state $(A, v)$ the point $(X, Y) = (A + \frac12, v + \frac12)$
satisfies $X^2 + Y^2 = \varphi(A, v) \le \frac{13}4$, so the lemma bounds linear
forms in $A + \frac12$ and $v + \frac12$ from below.

*Proof.* (1) By Lagrange's identity,
$(pX + rY)^2 + (pY - rX)^2 = (p^2 + r^2)(X^2 + Y^2) \le \frac{13}4(p^2 + r^2)$.
(2) By (1), $|pX + rY| \le \sqrt{\frac{13}4(p^2 + r^2)}$, which is at most $c$,
or less than $c$, respectively. $\square$

*Lean: [`dot_ge`](../../SquaresInCircles/Common/DiskSupport.lean#L30),
[`dot_gt`](../../SquaresInCircles/Common/DiskSupport.lean#L34),
[`dot_sq_le`](../../SquaresInCircles/Common/DiskSupport.lean#L24).*

### Lemma B.4 (lower bounds for the support)

1. Let $a, b$ be real numbers such that $(a, |b|)$ is an admissible state. Then
   $h(a, b, z) > -\frac{37}{50}$ for every real $z$.
2. Let $(a, u)$ be admissible and $s$ a sign. Then $(a, |su|) = (a, u)$ is
   admissible, and for every real $x$ with
   $|x - s\,\ell(a, u)| \le \frac12$ and every real $z$,

   ```math
   \cos(z - x) \le h(a, su, z) .
   ```

Part (1) says that the square $Q(a, b)$ has a point beyond the line
$\langle\cdot, u(z)\rangle = -\frac{37}{50}$ in every direction $u(z)$, because
its centre lies within $\sqrt3 - \frac12 < \frac{31}{25}$ of the origin.
Part (2) says that the support of $Q(a, su)$ is at least that of each point
$u(x) = (\cos x, \sin x)$ of the marker arc about the direction
$s\,\ell(a, u)$.

*Proof.* Part (1) is [Lemma 9.11](seven.md#lemma-911-the-support-function) (3). In part (2), $|su| = u$, and the
inequality is Lemma 9.11 (2). $\square$

*Lean: [`Seven.support_lower`](../../SquaresInCircles/Seven/Support.lean#L20),
[`Seven.sign_admissible`](../../SquaresInCircles/Seven/PairModel.lean#L42),
[`Seven.marker_arc_support`](../../SquaresInCircles/Seven/PairModel.lean#L48).*

### Lemma B.5 (support sums in closed form)

Let $(a, u)$ and $(A, v)$ be states, $s, t$ signs and $g$ real, and let
$d = g + s\,\ell(a, u) - t\,\ell(A, v)$.

1. The four support sums are

   ```math
   \begin{aligned}
   \sigma_0(g) &= a + \tfrac12 + h(A, tv, \pi - d), &
   \sigma_1(g) &= \tfrac12 + su + h\left(A, tv, \tfrac{3\pi}2 - d\right),\\
   \sigma_2(g) &= \tfrac12 - a + h(A, tv, 2\pi - d), &
   \sigma_3(g) &= \tfrac12 - su + h\left(A, tv, \tfrac{5\pi}2 - d\right).
   \end{aligned}
   ```

2. For all real $x, y, w$,

   ```math
   \begin{aligned}
   h\left(x, y, \tfrac{3\pi}2 - w\right) &= -x\sin w - y\cos w + \tfrac12(|\sin w| + |\cos w|),\\
   h(x, y, 2\pi - w) &= x\cos w - y\sin w + \tfrac12(|\cos w| + |\sin w|).
   \end{aligned}
   ```

3. Let $c = (c_1, c_2) = (A\cos d - tv\sin d,\ A\sin d + tv\cos d)$ and
   $W = \frac12(1 + |\cos d| + |\sin d|)$. Then

   ```math
   \sigma_0(g) = W - (c_1 - a), \quad \sigma_1(g) = W - (c_2 - su), \quad
   \sigma_2(g) = W + (c_1 - a), \quad \sigma_3(g) = W + (c_2 - su).
   ```

In (3), $c$ is the centre of $T$ in the chart of $S$, since $T$ sits at
$(A, tv)$ in the frame turned by $d$, and $(a, su)$ is the centre of $S$. The
number $W$ is the sum of the half-widths of $S$ and $T$ in the directions $n_k$:
$\frac12$ for $S$ and $\frac12(|\cos d| + |\sin d|)$ for $T$. So $\sigma_k(g)$
is $W$ minus the offset of the centre of $T$ from that of $S$ along $n_k$, as
Figure B.1 shows.

*Proof.* (1) For $\theta = k\frac\pi2$ one of $|\cos\theta|$, $|\sin\theta|$ is
$1$ and the other $0$, so
$h(a, su, \theta) = a\cos\theta + su\sin\theta + \frac12$, which is
$a + \frac12$, $\frac12 + su$, $\frac12 - a$, $\frac12 - su$ for
$k = 0, 1, 2, 3$. The second arguments $k\frac\pi2 + \pi - d$ are $\pi - d$,
$\frac{3\pi}2 - d$, $2\pi - d$ and $\frac{5\pi}2 - d$.

(2) $\cos(\frac{3\pi}2 - w) = -\sin w$, $\sin(\frac{3\pi}2 - w) = -\cos w$,
$\cos(2\pi - w) = \cos w$ and $\sin(2\pi - w) = -\sin w$; the absolute values do
not see the signs.

(3) We have $\cos(\pi - d) = -\cos d$ and $\sin(\pi - d) = \sin d$, and, since
$\frac{5\pi}2 - d = 2\pi + (\frac\pi2 - d)$, $\cos(\frac{5\pi}2 - d) = \sin d$
and $\sin(\frac{5\pi}2 - d) = \cos d$. With these and part (2) for $w = d$, part
(1) becomes

```math
\begin{aligned}
\sigma_0(g) &= a + \tfrac12 - A\cos d + tv\sin d + \tfrac12(|\cos d| + |\sin d|) = W - (c_1 - a),\\
\sigma_1(g) &= \tfrac12 + su - A\sin d - tv\cos d + \tfrac12(|\sin d| + |\cos d|) = W - (c_2 - su),\\
\sigma_2(g) &= \tfrac12 - a + A\cos d - tv\sin d + \tfrac12(|\cos d| + |\sin d|) = W + (c_1 - a),\\
\sigma_3(g) &= \tfrac12 - su + A\sin d + tv\cos d + \tfrac12(|\sin d| + |\cos d|) = W + (c_2 - su).
\end{aligned}
```

$\square$

*Lean:
[`Seven.pairSupport_zero`](../../SquaresInCircles/Seven/PairModel.lean#L77),
[`Seven.pairSupport_one`](../../SquaresInCircles/Seven/PairModel.lean#L83),
[`Seven.pairSupport_two`](../../SquaresInCircles/Seven/PairModel.lean#L90),
[`Seven.pairSupport_three`](../../SquaresInCircles/Seven/PairModel.lean#L97),
[`Seven.support_three_half_sub`](../../SquaresInCircles/Seven/PairModel.lean#L63),
[`Seven.support_two_pi_sub`](../../SquaresInCircles/Seven/PairModel.lean#L71),
[`Seven.pair_support_axis_values`](../../SquaresInCircles/Seven/PairModel.lean#L140),
[`Seven.centerDX`](../../SquaresInCircles/Seven/PairModel.lean#L134),
[`Seven.centerDY`](../../SquaresInCircles/Seven/PairModel.lean#L137),
[`angularWidth`](../../SquaresInCircles/Common/SeparatingAxes.lean#L250).*

### Lemma B.6 (the inward sum with a positive source sign)

Let $(a, u)$ and $(A, v)$ be admissible, let $t$ be a sign, and put
$e = \ell(a, u) - t\,\ell(A, v) - \frac\pi6$. Then
$-\frac\pi2 \le e \le \frac\pi2$, and for the signs $(1, t)$

```math
\sigma_2\left(\tfrac\pi3\right) = \tfrac12 - a - A\sin e + \tfrac12|\sin e| + \left(\tfrac12 - tv\right)\cos e .
```

*Proof.* Here $d = \frac\pi3 + \ell(a, u) - t\,\ell(A, v) = \frac\pi2 + e$, so
$2\pi - d = \frac{3\pi}2 - e$, and Lemma B.5 (1) and (2) give

```math
\sigma_2\left(\tfrac\pi3\right) = \tfrac12 - a - A\sin e - tv\cos e + \tfrac12(|\sin e| + |\cos e|) .
```

Both labels lie in $[0, \frac\pi4]$ ([Lemma 9.7](seven.md#lemma-97-the-label)), so
$e \in [-\frac{5\pi}{12}, \frac\pi{12}]$ if $t = 1$ and
$e \in [-\frac\pi6, \frac\pi3]$ if $t = -1$. In both cases $\cos e \ge 0$, so
$|\cos e| = \cos e$. $\square$

*Lean:
[`Seven.pairSupport_inward`](../../SquaresInCircles/Seven/PairModel.lean#L108).*

*Remark (the turns of the sectors).* In each sector Appendices C and D write
$\sigma_k(\frac\pi3)$ through a *turn*, the relative phase
$d = \frac\pi3 + s\ell - t\ell'$ shifted so that it vanishes, or is small, at
the contacts. With $\ell = \ell(a, u)$ and $\ell' = \ell(A, v)$, Lemma B.5 (3)
gives the following closed forms; in each row $\sin d$ and $\cos d$ are written
through the turn (for instance $\sin d = \cos z$ and $\cos d = \sin z$ in the
second row).

| axis, signs | turn | range of the turn | $\sigma_k(\frac\pi3)$ |
| --- | --- | --- | --- |
| inward, $s = 1$ | $e = \ell - t\ell' - \frac\pi6 = d - \frac\pi2$ | $[-\frac{5\pi}{12}, \frac\pi3]$ | $\frac12 - a - A\sin e - tv\cos e + \frac12(\lvert\sin e\rvert + \lvert\cos e\rvert)$ |
| forward, $s = t = 1$ | $z = \frac\pi6 - \ell + \ell' = \frac\pi2 - d$ | $[-\frac\pi{12}, \frac{5\pi}{12}]$ | $\frac12 + u - A\cos z - v\sin z + \frac12(\lvert\cos z\rvert + \lvert\sin z\rvert)$ |
| forward, $t = -1$ | $e = s\ell + \ell' - \frac\pi6 = d - \frac\pi2$ | $[-\frac{5\pi}{12}, \frac\pi3]$ | $\frac12 + su - A\cos e - v\sin e + \frac12(\lvert\sin e\rvert + \lvert\cos e\rvert)$ |
| forward, $(s, t) = (-1, 1)$ | $w = \ell + \ell' - \frac\pi3 = -d$ | $[-\frac\pi3, \frac\pi6]$ | $\frac12 - u + A\sin w - v\cos w + \frac12(\lvert\sin w\rvert + \lvert\cos w\rvert)$ |
| forward, $(s, t) = (-1, -1)$ | $d = \frac\pi3 - \ell + \ell'$ | $[\frac\pi{12}, \frac{7\pi}{12}]$ | $\frac12 - u - A\sin d + v\cos d + \frac12(\lvert\sin d\rvert + \lvert\cos d\rvert)$ |

The first row is Lemma B.6; with $t = -1$ it reads
$\frac12 - a - A\sin e + \frac12|\sin e| + (\frac12 + v)\cos e$ with
$e = \ell + \ell' - \frac\pi6 \in [-\frac\pi6, \frac\pi3]$.

## B.3 The label regions and their boundary

Two of the three terms of the label agree along a line:

```math
12\left(\mathrm{side}(a, u) - \mathrm{axial}(u)\right) = 2\pi + 7 - 9a - 11u, \qquad
12\left(\mathrm{side}(a, u) - \tfrac\pi4\right) = 7 - \pi - 9a + 4u ,
```

and $\mathrm{axial}(u) = \frac\pi4$ exactly when $u = \frac\pi5$. So the label
of a state is axial where $9a + 11u \le 2\pi + 7$ and $u \le \frac\pi5$; side
where $9a + 11u \ge 2\pi + 7$ and $9a - 4u \ge 7 - \pi$; and capped where
$u \ge \frac\pi5$ and $9a - 4u \le 7 - \pi$. We call the line
$9a + 11u = 2\pi + 7$ the *tie line*. Inside the admissible region, bounded by
the lines $a = \frac12$, $u = 0$, $u = a$ and the circle $\varphi = \frac{13}4$,
these conditions cut out the three regions of Figure B.2. The tie line meets the
circle at the *transition state* $(a_0, u_0)$, and the diagonal $u = a$ meets it
at the *diagonal corner* $(r_d, r_d)$ (Definition B.9).

![The admissible states in the (a, u)-plane: the region between the lines a = 1/2, u = 0 and u = a and the circle phi = 13/4, split into a large blue axial region at the bottom and left, a green side region between a purple tie line and the circle at the upper right, and a small orange capped triangle at the top left against the diagonal. The tie line runs from the transition state (a0, u0) on the circle up to the vertex V1 of the triangle; the side state (1, 1/2) lies on the circle in the side region, the diagonal corner (rd, rd) at the top, and the axial states (a, 0) form the bottom edge](figures/appb-regions.svg)

*Figure B.2.* The label regions. The label is axial in the blue region, side in
the green one and capped in the orange triangle $V_0V_1V_2$ of Lemma B.30. The
tie line (purple) separates the axial region from the side region and meets the
circle $\varphi = \frac{13}4$ at the transition state
$(a_0, u_0) \approx (1.1198, 0.2914)$. The side region is bounded by the tie
line, the circle up to the diagonal corner
$(r_d, r_d) \approx (0.7748, 0.7748)$, the diagonal, and the edge $V_1V_2$ where
the side label is $\frac\pi4$. The contacts of Chapter 9 involve the side state
$(1, \frac12)$ and the axial states $(a, 0)$ on the bottom edge.

### Lemma B.7 (the admissible region)

Let $(a, u)$ be admissible. Then $a \le \sqrt3 - \frac12$ and
$a + u < \frac{31}{20}$. Moreover $1.73 < \sqrt3 < 1.733$.

*Proof.* This is part of [Lemma 9.5](seven.md#lemma-95-admissible-states) (2), since $1.73 = \frac{173}{100}$ and
$1.733 = \frac{1733}{1000}$. $\square$

*Lean:
[`Seven.Admissible.a_le_sqrt_three_sub_half`](../../SquaresInCircles/Seven/Labels.lean#L53),
[`Seven.Admissible.sum_lt`](../../SquaresInCircles/Seven/Labels.lean#L60),
[`Seven.sqrt_three_bounds`](../../SquaresInCircles/Seven/Support.lean#L14).*

### Lemma B.8 (axial and side labels)

Let $(a, u)$ be admissible and $\ell = \ell(a, u)$.

1. If the label is axial, then $9a + 11u \le 2\pi + 7$ and
   $a + u < \frac{113}{80}$.
2. If the label is side, then $\frac9{25} < \ell$, $\frac7{10} < a < \frac98$,
   and $\frac95\left(\ell - \frac\pi6\right)^2 \le r(a, u)$.
3. In every case $a \le 1 + \frac{2\pi}{15} - \frac45\ell$.

*Proof.* Parts (1) and (2) are parts (2) and (1) of [Lemma 9.8](seven.md#lemma-98-side-and-axial-labels), and part (3) is
[Lemma 9.7](seven.md#lemma-97-the-label) (3). $\square$

*Lean: [`Seven.axial_tie_line`](../../SquaresInCircles/Seven/Labels.lean#L153),
[`Seven.axial_sum_lt`](../../SquaresInCircles/Seven/Labels.lean#L162),
[`Seven.side_selected_label_gt`](../../SquaresInCircles/Seven/Labels.lean#L122),
[`Seven.side_selected_a_gt`](../../SquaresInCircles/Seven/Labels.lean#L145),
[`Seven.side_selected_a_lt`](../../SquaresInCircles/Seven/Labels.lean#L134),
[`Seven.side_remainder_quadratic`](../../SquaresInCircles/Seven/Labels.lean#L172),
[`Seven.Admissible.radial_label_bound`](../../SquaresInCircles/Seven/Labels.lean#L101).*

### Definition B.9 (boundary curves and special states)

1. The *circle* over $u$ is
   $\gamma(u) = \sqrt{\frac{13}4 - (u + \frac12)^2} - \frac12$, for
   $(u + \frac12)^2 \le \frac{13}4$; the state $(\gamma(u), u)$ lies on
   $\varphi = \frac{13}4$.
2. The *tie line* over $u$ is $\lambda(u) = \frac19(2\pi + 7 - 11u)$, and the
   *top of the axial region* over $u$ is $\mu(u) = \min(\gamma(u), \lambda(u))$.
3. For a label value $\tau$, the *tie state* of label $\tau$ is
   $(\alpha(\tau), \frac45\tau)$ with
   $\alpha(\tau) = \lambda(\frac45\tau) = \frac{2\pi + 7}9 - \frac{44}{45}\tau$,
   and the *diagonal state* of label $\tau$ is $(\delta(\tau), \delta(\tau))$
   with $\delta(\tau) = \frac15(2\pi + 7 - 12\tau)$.
4. The *transition state* $(a_0, u_0)$ and its label $s_0$: with $M = 2\pi + 17$
   and $J = \sqrt{\frac{1313}2 - M^2}$,

   ```math
   X_0 = \tfrac1{202}(9M + 11J), \quad Y_0 = \tfrac1{202}(11M - 9J), \quad
   a_0 = X_0 - \tfrac12, \quad u_0 = Y_0 - \tfrac12, \quad s_0 = \tfrac54 u_0 .
   ```

5. The *diagonal corner* $(r_d, r_d)$ and its label $t_d$:
   $r_d = \sqrt{\frac{13}8} - \frac12$ and
   $t_d = \frac\pi6 + \frac7{12} - \frac5{12}r_d$.

In the coordinates $X = a + \frac12$, $Y = u + \frac12$ the circle
$\varphi = \frac{13}4$ is $X^2 + Y^2 = \frac{13}4$ and the tie line is
$9X + 11Y = M$. The points of this line are $\frac M{202}(9, 11) + y\,(11, -9)$,
at squared distance $\frac{M^2}{202} + 202y^2$ from the origin, so the line
meets the circle where $y = \pm\frac J{202}$; $(X_0, Y_0)$ is the point with
$y = \frac J{202}$. The diagonal $u = a$ meets the circle where
$2(a + \frac12)^2 = \frac{13}4$, at $a = r_d$. The tie state and the diagonal
state have the side label $\tau$: indeed
$12\,\mathrm{side}(x, x) = 2\pi + 7 - 5x$, so
$\mathrm{side}(\delta(\tau), \delta(\tau)) = \tau$ and $t_d$ is the side label
of $(r_d, r_d)$, and Proposition B.16 (5) below gives
$\mathrm{side}(\alpha(\tau), \frac45\tau) = \tau = \mathrm{axial}(\frac45\tau)$.

*Lean:
[`Seven.Boundary.circle`](../../SquaresInCircles/Seven/LabelBoundary.lean#L33),
[`Seven.Boundary.axialLine`](../../SquaresInCircles/Seven/LabelBoundary.lean#L34),
[`Seven.Boundary.axialTop`](../../SquaresInCircles/Seven/LabelBoundary.lean#L35),
[`Seven.Boundary.tieA`](../../SquaresInCircles/Seven/LabelBoundary.lean#L36),
[`Seven.Boundary.diagonal`](../../SquaresInCircles/Seven/LabelBoundary.lean#L37),
[`Seven.Boundary.M`](../../SquaresInCircles/Seven/LabelBoundary.lean#L15),
[`Seven.Boundary.J`](../../SquaresInCircles/Seven/LabelBoundary.lean#L16),
[`Seven.Boundary.X0`](../../SquaresInCircles/Seven/LabelBoundary.lean#L17),
[`Seven.Boundary.Y0`](../../SquaresInCircles/Seven/LabelBoundary.lean#L18),
[`Seven.Boundary.a0`](../../SquaresInCircles/Seven/LabelBoundary.lean#L19),
[`Seven.Boundary.u0`](../../SquaresInCircles/Seven/LabelBoundary.lean#L20),
[`Seven.Boundary.s0`](../../SquaresInCircles/Seven/LabelBoundary.lean#L21),
[`Seven.Boundary.rd`](../../SquaresInCircles/Seven/LabelBoundary.lean#L22),
[`Seven.Boundary.td`](../../SquaresInCircles/Seven/LabelBoundary.lean#L23).*

### Lemma B.10 (the transition state)

1. $\frac{1313}2 - M^2 > 0$, so $J$ is well defined, and
   $10.69547 < J < 10.69549$.
2. $X_0^2 + Y_0^2 = \frac{13}4$, $9a_0 + 11u_0 = 2\pi + 7$, and
   $\alpha(s_0) = a_0$.
3. $1.11979 < a_0 < 1.11980$ and $0.29136 < u_0 < 0.29137$. Hence
   $\frac{11}{10} < a_0 < \frac98$, $\frac{29}{100} < u_0 < \frac3{10}$ and
   $\frac9{25} < s_0 < \frac25$.
4. $(a_0, u_0)$ is admissible, and
   $\ell(a_0, u_0) = \mathrm{axial}(u_0) = \mathrm{side}(a_0, u_0) = s_0$.

*Proof.* (1) From $3.141592 < \pi < 3.141593$ we get
$23.283184 < M < 23.283186$, hence

```math
\begin{aligned}
\tfrac{1313}2 - M^2 &> 656.5 - 23.283186^2 = 114.393249689404 > 114.3930785209 = 10.69547^2,\\
\tfrac{1313}2 - M^2 &< 656.5 - 23.283184^2 = 114.393342822144 < 114.3935063401 = 10.69549^2 .
\end{aligned}
```

(2) Expanding, and using $M^2 + J^2 = \frac{1313}2$,

```math
(9M + 11J)^2 + (11M - 9J)^2 = 202\left(M^2 + J^2\right) = 202^2\cdot\tfrac{13}4,
\qquad 9X_0 + 11Y_0 = \tfrac1{202}(81M + 121M) = M .
```

The first identity is $X_0^2 + Y_0^2 = \frac{13}4$, and the second gives
$9a_0 + 11u_0 = M - 10 = 2\pi + 7$. Then
$\alpha(s_0) = \frac{2\pi + 7}9 - \frac{44}{45}\cdot\frac54 u_0$, which is
$\frac19(2\pi + 7 - 11u_0) = a_0$.

(3) By (1) and the bounds on $M$, $9M + 11J$ lies between
$9(23.283184) + 11(10.69547) = 327.198826$ and
$9(23.283186) + 11(10.69549) = 327.199064$, and $11M - 9J$ between
$11(23.283184) - 9(10.69549) = 159.855614$ and
$11(23.283186) - 9(10.69547) = 159.855816$. Since $202(1.61979) = 327.19758$,
$202(1.6198) = 327.1996$, $202(0.79136) = 159.85472$ and
$202(0.79137) = 159.85674$, we get $1.61979 < X_0 < 1.6198$ and
$0.79136 < Y_0 < 0.79137$. The coarse bounds follow, with
$s_0 = 1.25u_0 \in (0.3642, 0.36422)$.

(4) By (3), $0 \le u_0 \le a_0$ and $a_0 \ge \frac12$, and
$\varphi(a_0, u_0) = X_0^2 + Y_0^2 = \frac{13}4$. By (2) and the identity at the
start of this section, $\mathrm{side}(a_0, u_0) = \mathrm{axial}(u_0) = s_0$,
and $s_0 < \frac25 < \frac\pi4$. $\square$

*Lean:
[`Seven.Boundary.J_sq`](../../SquaresInCircles/Seven/LabelBoundary.lean#L42),
[`Seven.Boundary.J_bounds`](../../SquaresInCircles/Seven/LabelBoundary.lean#L47),
[`Seven.Boundary.transition_circle`](../../SquaresInCircles/Seven/LabelBoundary.lean#L68),
[`Seven.Boundary.transition_line`](../../SquaresInCircles/Seven/LabelBoundary.lean#L73),
[`Seven.Boundary.tieA_s0`](../../SquaresInCircles/Seven/LabelBoundary.lean#L77),
[`Seven.Boundary.transition_bounds`](../../SquaresInCircles/Seven/LabelBoundary.lean#L53),
[`Seven.Boundary.transition_coarse`](../../SquaresInCircles/Seven/LabelBoundary.lean#L60),
[`Seven.Boundary.transition_admissible`](../../SquaresInCircles/Seven/LabelBoundary.lean#L82),
[`Seven.Boundary.transition_labels`](../../SquaresInCircles/Seven/LabelBoundary.lean#L89).*

### Lemma B.11 (the diagonal corner)

1. $(r_d + \frac12)^2 = \frac{13}8$ and $0.77475 < r_d < 0.77476$.
2. $\delta(t_d) = r_d$, and $\frac{18}{25} < t_d < \frac\pi4$; indeed
   $\frac15(7 - \pi) < r_d$.

*Proof.* (1) The identity is the definition, and
$1.27475^2 = 1.6249875625 < \frac{13}8 < 1.6250130576 = 1.27476^2$. (2)
$12t_d = 2\pi + 7 - 5r_d$, so $\delta(t_d) = \frac15(2\pi + 7 - 12t_d) = r_d$.
Next, $t_d$ exceeds $\frac{3.141592}6 + \frac7{12} - \frac5{12}(0.77476)$, which
is more than $0.7841 > \frac{18}{25}$. Finally $t_d < \frac\pi4$ is equivalent
to $7 - 5r_d < \pi$, and
$\frac15(7 - \pi) < \frac15(7 - 3.141592) = 0.7716816 < r_d$. $\square$

*Lean:
[`Seven.Boundary.rd_sq`](../../SquaresInCircles/Seven/LabelBoundary.lean#L104),
[`Seven.Boundary.rd_bounds`](../../SquaresInCircles/Seven/LabelBoundary.lean#L98),
[`Seven.Boundary.td_bounds`](../../SquaresInCircles/Seven/LabelBoundary.lean#L108),
[`Seven.Boundary.diagonal_td`](../../SquaresInCircles/Seven/LabelBoundary.lean#L113).*

### Lemma B.12 (the circle over the u-axis)

Let $0 \le u \le v \le r_d$.

1. $\frac{13}4 - (u + \frac12)^2 \ge \frac{13}8$, so $\gamma(u)$ is defined;
   $(\gamma(u) + \frac12)^2 + (u + \frac12)^2 = \frac{13}4$; $u \le \gamma(u)$;
   and $(\gamma(u), u)$ is admissible.
2. $\gamma(v) \le \gamma(u)$ and $\gamma(u) - \gamma(v) \le v - u$.
3. $\gamma(u_0) = a_0$. If $u \le u_0$, then $\gamma(u) \le \lambda(u)$, so
   $\mu(u) = \gamma(u)$; if $u \ge u_0$, then $\lambda(u) \le \gamma(u)$, so
   $\mu(u) = \lambda(u)$.
4. If $v \le u_0$, then $\gamma(u) - \gamma(v) \le \frac12(v - u)$.
5. If $(a, w)$ is an admissible state, then $(w + \frac12)^2 < \frac{13}4$ and
   $a \le \gamma(w)$.

So the axial region lies below the graph of $\mu$, which follows the circle up
to $u_0$ and the tie line beyond (Figure B.2).

*Proof.* (1) Since
$(r_d + \frac12)^2 - (u + \frac12)^2 = (r_d - u)(r_d + u + 1) \ge 0$, we have
$(u + \frac12)^2 \le (r_d + \frac12)^2 = \frac{13}8$, hence the first claim, and
the identity is the definition of $\gamma$. Then
$(\gamma(u) + \frac12)^2 \ge \frac{13}8 \ge (u + \frac12)^2$ gives
$u \le \gamma(u)$, and $\gamma(u) + \frac12 \ge \sqrt{13/8} > 1$ gives
$\gamma(u) > \frac12$. With $\varphi(\gamma(u), u) = \frac{13}4$ this makes
$(\gamma(u), u)$ admissible.

(2) By (1),

```math
\left(\gamma(u) - \gamma(v)\right)\left(\gamma(u) + \gamma(v) + 1\right)
= \left(\gamma(u) + \tfrac12\right)^2 - \left(\gamma(v) + \tfrac12\right)^2
= (v - u)(u + v + 1) \ge 0 ,
```

and $\gamma(u) + \gamma(v) + 1 \ge u + v + 1 > 0$. So

```math
0 \le \gamma(u) - \gamma(v) = \frac{(v - u)(u + v + 1)}{\gamma(u) + \gamma(v) + 1} \le v - u .
```

(3) By Lemma B.10, $(a_0 + \frac12)^2 + (u_0 + \frac12)^2 = \frac{13}4$ with
$a_0 + \frac12 > 0$ and $0 \le u_0 \le r_d$, so $\gamma(u_0) = a_0$; and
$9a_0 + 11u_0 = 2\pi + 7$ gives $\lambda(u) = a_0 + \frac{11}9(u_0 - u)$. For
$u \le u_0$, (2) gives $\gamma(u) \le a_0 + (u_0 - u) \le \lambda(u)$. For
$u_0 \le u \le r_d$, (2) gives
$\gamma(u) \ge a_0 - (u - u_0) \ge a_0 - \frac{11}9(u - u_0) = \lambda(u)$.

(4) By (2) and (3), $\gamma(u), \gamma(v) \ge \gamma(u_0) = a_0$, so
$\gamma(u) + \gamma(v) + 1 \ge 2a_0 + 1 > 3.23958$, while
$2(u + v + 1) \le 4u_0 + 2 < 3.16548$ (Lemma B.10). The quotient in the proof of
(2) is therefore at most $\frac12(v - u)$.

(5) $(a + \frac12)^2 = \varphi(a, w) - (w + \frac12)^2$ is positive and at most
$\frac{13}4 - (w + \frac12)^2$, and $a + \frac12 > 0$; take square roots.
$\square$

*Lean:
[`Seven.Boundary.circle_radicand_pos`](../../SquaresInCircles/Seven/BoundarySegments.lean#L17),
[`Seven.Boundary.circle_eq`](../../SquaresInCircles/Seven/BoundarySegments.lean#L25),
[`Seven.Boundary.circle_ge_coordinate`](../../SquaresInCircles/Seven/BoundarySegments.lean#L31),
[`Seven.Boundary.circle_state`](../../SquaresInCircles/Seven/BoundarySegments.lean#L40),
[`Seven.Boundary.circle_order`](../../SquaresInCircles/Seven/BoundarySegments.lean#L51),
[`Seven.Boundary.circle_u0`](../../SquaresInCircles/Seven/BoundarySegments.lean#L71),
[`Seven.Boundary.circle_switch_left`](../../SquaresInCircles/Seven/BoundarySegments.lean#L79),
[`Seven.Boundary.circle_switch_right`](../../SquaresInCircles/Seven/BoundarySegments.lean#L88),
[`Seven.Boundary.axialTop_left`](../../SquaresInCircles/Seven/BoundarySegments.lean#L97),
[`Seven.Boundary.axialTop_right`](../../SquaresInCircles/Seven/BoundarySegments.lean#L100),
[`Seven.Boundary.circle_displacement_half`](../../SquaresInCircles/Seven/BoundarySegments.lean#L353),
[`Seven.Boundary.a_le_circle`](../../SquaresInCircles/Seven/BoundarySegments.lean#L103).*

### Definition B.13 (the circle parametrised by the side label)

Let $N = \frac{97}{144}$. For $s_0 \le \tau \le t_d$ put

```math
D(\tau) = \tfrac\pi6 + \tfrac{19}{24} - \tau, \qquad
Z(\tau) = \sqrt{\tfrac{1261}{576} - D(\tau)^2}, \qquad
X(\tau) = \tfrac1N\left(\tfrac34 D(\tau) + \tfrac13 Z(\tau)\right), \qquad
Y(\tau) = \tfrac1N\left(-\tfrac13 D(\tau) + \tfrac34 Z(\tau)\right),
```

where $\frac{1261}{576} = \frac{13}4 N$. The *top* of the side label $\tau$ is
the state $(\hat a(\tau), \hat u(\tau))$ with

```math
\left(\hat a(\tau), \hat u(\tau)\right) = \left(X(\tau) - \tfrac12,\ Y(\tau) - \tfrac12\right) \text{ for } s_0 \le \tau \le t_d, \qquad
\left(\hat a(\tau), \hat u(\tau)\right) = \left(\delta(\tau), \delta(\tau)\right) \text{ for } t_d < \tau \le \tfrac\pi4 .
```

In the coordinates $X = a + \frac12$, $Y = u + \frac12$ the side label is
$\mathrm{side}(a, u) = \frac\pi6 + \frac{19}{24} - (\frac34 X - \frac13 Y)$. The
vectors $(\frac34, -\frac13)$ and $(\frac13, \frac34)$ are orthogonal, both of
squared length $N$, so $\frac34 X - \frac13 Y$ and $\frac13 X + \frac34 Y$ are
$\sqrt N$ times the coordinates of $(X, Y)$ along the unit vectors in their
directions (Figure B.3). So the line of side label $\tau$ is
$\frac34 X - \frac13 Y = D(\tau)$, and it meets the circle
$X^2 + Y^2 = \frac{13}4$ where
$(\frac13 X + \frac34 Y)^2 = \frac{13}4 N - D(\tau)^2$; the point
$(X(\tau), Y(\tau))$ is the intersection with
$\frac13 X + \frac34 Y = Z(\tau) > 0$.

*Lean:
[`Seven.Boundary.N`](../../SquaresInCircles/Seven/LabelBoundary.lean#L25),
[`Seven.Boundary.D`](../../SquaresInCircles/Seven/LabelBoundary.lean#L26),
[`Seven.Boundary.Z`](../../SquaresInCircles/Seven/LabelBoundary.lean#L27),
[`Seven.Boundary.X`](../../SquaresInCircles/Seven/LabelBoundary.lean#L28),
[`Seven.Boundary.Y`](../../SquaresInCircles/Seven/LabelBoundary.lean#L29),
[`Seven.Boundary.sideA`](../../SquaresInCircles/Seven/LabelBoundary.lean#L30),
[`Seven.Boundary.sideU`](../../SquaresInCircles/Seven/LabelBoundary.lean#L31),
[`Seven.Boundary.sideTopA`](../../SquaresInCircles/Seven/LabelBoundary.lean#L40),
[`Seven.Boundary.sideTopU`](../../SquaresInCircles/Seven/LabelBoundary.lean#L39).*

![The quarter circle X squared plus Y squared equals 13/4 in the (X, Y)-plane with the diagonal X = Y; from the origin, two short arrows along (3/4, -1/3) and (1/3, 3/4); an orange segment from the origin along the first direction of length D/root N to the foot of a purple line of constant side label, and a blue segment along that line of length Z/root N up to the point (X(tau), Y(tau)) on the circle; a thick green arc of the circle from the transition point (X0, Y0) up to the diagonal point (rd + 1/2, rd + 1/2)](figures/appb-parametrisation.svg)

*Figure B.3.* The parametrisation of Definition B.13 at $\tau = 0.6$, in the
coordinates $X = a + \frac12$, $Y = u + \frac12$. The line of side label $\tau$
(purple) is perpendicular to $(\frac34, -\frac13)$ at the distance
$D(\tau)/\sqrt N$ from the origin, and the point $(X(\tau), Y(\tau))$ lies on it
at the distance $Z(\tau)/\sqrt N$ from the foot. As $\tau$ increases from $s_0$
to $t_d$, the line moves towards the origin and the point runs along the circle
from $(X_0, Y_0)$ to $(r_d + \frac12, r_d + \frac12)$ (green arc).

### Lemma B.14 (the parametrisation)

Let $s_0 \le \tau \le t_d$ and write $D, Z, X, Y$ for their values at $\tau$.

1. $\frac12 < D < 1$ and $Z > 0$; $X^2 + Y^2 = \frac{13}4$,
   $\frac34 X - \frac13 Y = D$ and $\frac13 X + \frac34 Y = Z$; and
   $\mathrm{side}(X - \frac12, Y - \frac12) = \tau$.
2. $D(s_0) = \frac34 X_0 - \frac13 Y_0$, $X(s_0) = X_0$ and $Y(s_0) = Y_0$;
   $D(t_d) = \frac5{12}(r_d + \frac12)$ and $X(t_d) = Y(t_d) = r_d + \frac12$.
3. $0 < Y_0 \le Y \le X$, $\frac54 < X \le X_0$, and $1 < Z < \frac75$.
4. The functions $D, Z, X, Y$ are differentiable on $[s_0, t_d]$, with
   $D' = -1$, $Z' = \frac DZ$, $X' = -\frac YZ$, $Y' = \frac XZ$ and
   $\left(\frac XZ\right)' = -\frac{39}{16Z^3}$.

*Proof.* (1) $D$ decreases in $\tau$. By Lemmas B.10 and B.11,
$D(t_d) = \frac5{12}(r_d + \frac12) > \frac5{12}(1.27475) > 0.5311$ and
$D(s_0) < \frac{3.141593}6 + \frac{19}{24} - 0.3642 < 0.9511$. So
$D^2 < 1 < \frac{1261}{576}$ and $Z > 0$. The two linear identities follow by
substituting the definitions of $X$ and $Y$ (the coefficients combine through
$\frac9{16} + \frac19 = N$), and then Lagrange's identity gives

```math
N\left(X^2 + Y^2\right) = \left(\tfrac34 X - \tfrac13 Y\right)^2 + \left(\tfrac13 X + \tfrac34 Y\right)^2 = D^2 + Z^2 = \tfrac{13}4 N .
```

Finally $\mathrm{side}(X - \frac12, Y - \frac12)$ is
$\frac\pi6 + \frac{19}{24} - D = \tau$.

(2) By Lemma B.10 (4), $\mathrm{side}(a_0, u_0) = s_0$, which by the formula for
the side label above means $D(s_0) = \frac34 X_0 - \frac13 Y_0$. By Lagrange's
identity,
$Z(s_0)^2 = N(X_0^2 + Y_0^2) - D(s_0)^2 = (\frac13 X_0 + \frac34 Y_0)^2$, and
$\frac13 X_0 + \frac34 Y_0 > 0$, so $Z(s_0) = \frac13 X_0 + \frac34 Y_0$ and

```math
X(s_0) = \tfrac1N\left(\left(\tfrac9{16} + \tfrac19\right)X_0 + \left(-\tfrac14 + \tfrac14\right)Y_0\right) = X_0,
\qquad
Y(s_0) = \tfrac1N\left(\left(-\tfrac14 + \tfrac14\right)X_0 + \left(\tfrac19 + \tfrac9{16}\right)Y_0\right) = Y_0 .
```

At $t_d$, using $(r_d + \frac12)^2 = \frac{13}8$,

```math
D(t_d) = \tfrac{19}{24} - \tfrac7{12} + \tfrac5{12}r_d = \tfrac5{12}\left(r_d + \tfrac12\right),
\qquad
Z(t_d)^2 = \tfrac{1261}{576} - \tfrac{25}{144}\cdot\tfrac{13}8 = \tfrac{2197}{1152} = \left(\tfrac{13}{12}\left(r_d + \tfrac12\right)\right)^2 ,
```

so $Z(t_d) = \frac{13}{12}(r_d + \frac12)$; and since
$\frac34\cdot\frac5{12} + \frac13\cdot\frac{13}{12} = \frac{97}{144} = N$ and
$-\frac13\cdot\frac5{12} + \frac34\cdot\frac{13}{12} = \frac{97}{144} = N$,
$X(t_d) = Y(t_d) = r_d + \frac12$.

(3) As $\tau$ increases, $D$ decreases and stays positive, so $Z$ increases;
hence $Y = \frac1N(-\frac13 D + \frac34 Z)$ increases, and
$Y \ge Y(s_0) = Y_0 > 0$. Next $X - Y = \frac1{12N}(13D - 5Z)$, and $5Z \le 13D$
is equivalent to $25(\frac{1261}{576} - D^2) \le 169D^2$, that is, to
$D^2 \ge \frac{325}{1152} = D(t_d)^2$, which holds since $D \ge D(t_d) > 0$. So
$Y \le X$. Then $2X^2 \ge X^2 + Y^2 = \frac{13}4$ gives
$X^2 \ge \frac{13}8 > \frac{25}{16}$, and $X^2 = \frac{13}4 - Y^2$ is at most
$\frac{13}4 - Y_0^2 = X_0^2$, so $X \le X_0$. For $Z$, first
$Z = \frac13 X + \frac34 Y$ exceeds
$\frac5{12} + \frac34\cdot\frac{79}{100} = \frac{1211}{1200} > 1$. Second,
$(X + Y)^2 \le 2(X^2 + Y^2) = \frac{13}2 < (\frac{51}{20})^2$, so

```math
Z = \tfrac{13}{24}(X + Y) - \tfrac5{24}(X - Y) \le \tfrac{13}{24}(X + Y) < \tfrac{13}{24}\cdot\tfrac{51}{20} = \tfrac{221}{160} < \tfrac75 .
```

(4) $Z$ is differentiable because its radicand is positive, and the chain rule
gives

```math
Z' = -\frac{DD'}Z = \frac DZ, \qquad
X' = \frac1N\left(-\frac34 + \frac D{3Z}\right) = -\frac{\frac34 Z - \frac13 D}{NZ} = -\frac YZ, \qquad
Y' = \frac1N\left(\frac13 + \frac{3D}{4Z}\right) = \frac{\frac13 Z + \frac34 D}{NZ} = \frac XZ .
```

Finally $\left(\frac XZ\right)' = \frac{X'Z - XZ'}{Z^2} = -\frac{YZ + XD}{Z^3}$,
and by (1),

```math
YZ + XD = Y\left(\tfrac13 X + \tfrac34 Y\right) + X\left(\tfrac34 X - \tfrac13 Y\right) = \tfrac34\left(X^2 + Y^2\right) = \tfrac{39}{16} .
```

$\square$

*Lean:
[`Seven.Boundary.D_range`](../../SquaresInCircles/Seven/LabelBoundary.lean#L126),
[`Seven.Boundary.radicand_pos`](../../SquaresInCircles/Seven/LabelBoundary.lean#L134),
[`Seven.Boundary.Z_pos`](../../SquaresInCircles/Seven/LabelBoundary.lean#L140),
[`Seven.Boundary.Z_sq`](../../SquaresInCircles/Seven/LabelBoundary.lean#L143),
[`Seven.Boundary.circle_identities`](../../SquaresInCircles/Seven/LabelBoundary.lean#L147),
[`Seven.Boundary.circle_label`](../../SquaresInCircles/Seven/LabelBoundary.lean#L156),
[`Seven.Boundary.D_s0`](../../SquaresInCircles/Seven/LabelBoundary.lean#L121),
[`Seven.Boundary.side_at_transition`](../../SquaresInCircles/Seven/LabelBoundary.lean#L162),
[`Seven.Boundary.D_td`](../../SquaresInCircles/Seven/LabelBoundary.lean#L117),
[`Seven.Boundary.side_at_diagonal`](../../SquaresInCircles/Seven/LabelBoundary.lean#L181),
[`Seven.Boundary.circle_bounds`](../../SquaresInCircles/Seven/LabelBoundary.lean#L195),
[`Seven.Boundary.hasDerivAt_D`](../../SquaresInCircles/Seven/LabelBoundary.lean#L252),
[`Seven.Boundary.hasDerivAt_Z`](../../SquaresInCircles/Seven/LabelBoundary.lean#L257),
[`Seven.Boundary.hasDerivAt_X`](../../SquaresInCircles/Seven/LabelBoundary.lean#L268),
[`Seven.Boundary.hasDerivAt_Y`](../../SquaresInCircles/Seven/LabelBoundary.lean#L280),
[`Seven.Boundary.hasDerivAt_Y_prime`](../../SquaresInCircles/Seven/LabelBoundary.lean#L292).*

## B.4 Segments of constant label

A support sum at the gap $\frac\pi3$ depends on a state through its coordinates
and its label. At a fixed label it is affine in the state, so it is extreme at
the ends of the set of admissible states with that label. For an axial label
$\tau$ this set is the horizontal segment $u = \frac45\tau$,
$\frac12 \le a \le \mu(\frac45\tau)$ (Proposition B.15). For a side label $\tau$
it is a segment of slope $\frac94$ in the $(a, u)$-plane, from the tie state of
label $\tau$ up to the top $(\hat a(\tau), \hat u(\tau))$ (Proposition B.16 and
Figure B.4).

### Proposition B.15 (the axial region)

1. If $(a, u)$ is admissible and its label is axial, then $a \le \mu(u)$.
2. If $0 \le u \le \frac\pi5$, the state $(\mu(u), u)$ is admissible and its
   label is axial, equal to $\frac54 u$.
3. If $0 \le u \le v \le \frac\pi5$, then $\mu(v) \le \mu(u)$ and
   $\mu(u) - \mu(v) \le \frac{11}9(v - u)$.

*Proof.* (1) By Lemma B.12 (5), $a \le \gamma(u)$, and by Lemma B.8 (1),
$9a + 11u \le 2\pi + 7$, that is, $a \le \lambda(u)$.

(2) Since $\frac\pi5 < \frac{22}{35} < 0.77475 < r_d$, Lemma B.12 (1) applies:
$(\gamma(u), u)$ is admissible, $u \le \gamma(u)$ and $\gamma(u) > \frac12$.
Next $u \le \lambda(u)$, because $20u \le 4\pi < 2\pi + 7$; and
$\lambda(u) \ge \frac12$, because $11u \le \frac{11\pi}5 = 2\pi + \frac\pi5$ and
$\frac\pi5 < \frac52$. So $\mu(u) \ge u$ and $\mu(u) \ge \frac12$, and from
$\frac12 \le \mu(u) \le \gamma(u)$ we get
$\varphi(\mu(u), u) \le \varphi(\gamma(u), u) = \frac{13}4$: the state
$(\mu(u), u)$ is admissible. Its label is axial: $\mu(u) \le \lambda(u)$ means
$9\mu(u) + 11u \le 2\pi + 7$, that is,
$\mathrm{axial}(u) \le \mathrm{side}(\mu(u), u)$; and
$\mathrm{axial}(u) = \frac54 u \le \frac\pi4$.

(3) By Lemma B.12 (2), $\gamma$ is nonincreasing on $[0, r_d]$, and so is
$\lambda$; hence so is their minimum $\mu$. If $\mu(v) = \gamma(v)$, then by
Lemma B.12 (2)
$\mu(u) \le \gamma(u) \le \gamma(v) + (v - u) \le \mu(v) + \frac{11}9(v - u)$.
If $\mu(v) = \lambda(v)$, then
$\mu(u) \le \lambda(u) = \lambda(v) + \frac{11}9(v - u)$. $\square$

*Lean:
[`Seven.Boundary.axial_upper`](../../SquaresInCircles/Seven/BoundarySegments.lean#L113),
[`Seven.Boundary.axialTop_state`](../../SquaresInCircles/Seven/BoundarySegments.lean#L120),
[`Seven.Boundary.axialTop_antitone`](../../SquaresInCircles/Seven/BoundarySegments.lean#L329),
[`Seven.Boundary.axialTop_displacement`](../../SquaresInCircles/Seven/BoundarySegments.lean#L337).*

### Proposition B.16 (segments of constant side label)

1. Let $(a, u)$ be admissible with a side label $\tau = \mathrm{side}(a, u)$.
   Then $u_0 \le u$, $a \le a_0$ and $s_0 \le \tau \le \frac\pi4$.
2. In (1), $a = \alpha(\tau) + \frac49(u - \frac45\tau)$,
   $\frac45\tau \le u \le \hat u(\tau)$ and $a \le \hat a(\tau)$.
3. For $s_0 \le \tau \le \frac\pi4$ the tie state $(\alpha(\tau), \frac45\tau)$
   is admissible, and its label is $\tau$, equal to both
   $\mathrm{axial}(\frac45\tau)$ and $\mathrm{side}(\alpha(\tau), \frac45\tau)$.
4. For $s_0 \le \tau \le \frac\pi4$ the top $(\hat a(\tau), \hat u(\tau))$ is
   admissible, with the side label $\tau$. For $\tau \le t_d$ it lies on the
   circle $\varphi = \frac{13}4$, and for $\tau \ge t_d$ on the diagonal.
5. For all real $a', u', \tau$ with $\mathrm{side}(a', u') = \tau$,
   $a' = \alpha(\tau) + \frac49(u' - \frac45\tau)$.
6. For $s_0 \le \tau \le \tau' \le t_d$,
   $\hat a(\tau) - \hat a(\tau') \le \frac{12}{13}(\tau' - \tau)$.

*Proof.* (5) Solving $\mathrm{side}(a', u') = \tau$ for $a'$ gives
$a' = \frac43(\frac\pi6 + \frac7{12} + \frac13 u' - \tau)$, that is,
$a' = \frac{2\pi + 7}9 + \frac49 u' - \frac43\tau$; and
$\alpha(\tau) - \frac{16}{45}\tau = \frac{2\pi + 7}9 - \frac43\tau$.

(1) Since the label is side, $\mathrm{side}(a, u) \le \mathrm{axial}(u)$, that
is, $9a + 11u \ge 2\pi + 7 = 9a_0 + 11u_0$. Suppose $u < u_0$. Then
$a - a_0 \ge \frac{11}9(u_0 - u) > 0$. Expanding $\varphi$ about $(a_0, u_0)$,
where it equals $X_0^2 + Y_0^2 = \frac{13}4$,

```math
\varphi(a, u) - \tfrac{13}4 = 2X_0(a - a_0) - 2Y_0(u_0 - u) + (a - a_0)^2 + (u - u_0)^2
\ge (u_0 - u)\left(\tfrac{22}9 X_0 - 2Y_0\right) > 0 ,
```

because $\frac{22}9 X_0 > \frac{22}9(1.61979) > 3.95 > 2Y_0$ (Lemma B.10); this
contradicts admissibility. So $u \ge u_0$, and then
$(a + \frac12)^2 \le \frac{13}4 - (u + \frac12)^2$ is at most
$\frac{13}4 - (u_0 + \frac12)^2 = (a_0 + \frac12)^2$, so $a \le a_0$. Finally
$\tau - s_0 = \mathrm{side}(a, u) - \mathrm{side}(a_0, u_0)$ equals
$\frac13(u - u_0) + \frac34(a_0 - a) \ge 0$, and
$\tau = \ell(a, u) \le \frac\pi4$.

(3) Let $w = \frac45\tau$. Then $u_0 = \frac45 s_0 \le w \le \frac\pi5 < r_d$,
so $\mu(w) = \lambda(w) = \alpha(\tau)$ by Lemma B.12 (3). By Proposition B.15
(2), $(\alpha(\tau), w)$ is admissible with the axial label $\frac54 w = \tau$,
and by (5) its side label is $\tau$ too.

(4) First let $\tau \le t_d$ and write $X, Y, Z$ for their values at $\tau$. By
Lemma B.14, $\hat u = Y - \frac12 \ge u_0 > 0$, $\hat u \le \hat a$ since
$Y \le X$, $\hat a > \frac34$ since $X > \frac54$, and
$\varphi(\hat a, \hat u) = X^2 + Y^2 = \frac{13}4$: the top is admissible and on
the circle. Its side label is $\tau \le t_d < \frac\pi4$. It remains to see
$\tau \le \mathrm{axial}(\hat u)$, that is, $9\hat a + 11\hat u \ge 2\pi + 7$,
that is, $\lambda(\hat u) \le \hat a$. Since $Y \le X$,
$2Y^2 \le X^2 + Y^2 = \frac{13}4$, so
$\hat u + \frac12 = Y \le \sqrt{13/8} = r_d + \frac12$. So
$u_0 \le \hat u \le r_d$, and $\gamma(\hat u) = \hat a$ because
$(\hat a + \frac12)^2 = \frac{13}4 - (\hat u + \frac12)^2$ with
$\hat a + \frac12 > 0$. Lemma B.12 (3) gives
$\lambda(\hat u) \le \gamma(\hat u) = \hat a$.

Now let $t_d \le \tau \le \frac\pi4$ and $x = \delta(\tau)$, so that
$\mathrm{side}(x, x) = \tau$ (Definition B.9). Then $x \le \delta(t_d) = r_d$,
and $x > \frac12$ because $12\tau \le 3\pi < 2\pi + \frac92$. So
$\varphi(x, x) = 2(x + \frac12)^2 \le 2(r_d + \frac12)^2 = \frac{13}4$ and
$(x, x)$ is admissible, on the diagonal. Its side label $\tau$ is at most
$\frac\pi4$, and at most $\mathrm{axial}(x) = \frac54 x$ because
$16\tau \le 4\pi < 2\pi + 7$ (which is $4\tau \le 2\pi + 7 - 12\tau = 5x$). At
$\tau = t_d$ both descriptions give the diagonal corner (Lemma B.14 (2)).

(2) The identity is (5), and $u \ge \frac45\tau$ because
$\tau = \ell(a, u) \le \mathrm{axial}(u)$. For the upper bound, first let
$\tau \le t_d$. By (4) and (5), the top $(\hat a, \hat u)$ lies on the same line
$a' = \alpha(\tau) + \frac49(u' - \frac45\tau)$ as $(a, u)$. If $u > \hat u$,
then $a - \hat a = \frac49(u - \hat u) > 0$ and

```math
\varphi(a, u) - \varphi(\hat a, \hat u) = (a - \hat a)(a + \hat a + 1) + (u - \hat u)(u + \hat u + 1) > 0 ,
```

so $\varphi(a, u) > \frac{13}4$, which is impossible. Next let $\tau > t_d$.
From $u \le a = \alpha(\tau) + \frac49 u - \frac{16}{45}\tau$ we get
$\frac59 u \le \frac{2\pi + 7}9 - \frac43\tau$, that is,
$u \le \delta(\tau) = \hat u(\tau)$. In both cases $(a, u)$ and the top lie on
the line of (5), of positive slope, so
$a - \hat a(\tau) = \frac49(u - \hat u(\tau)) \le 0$.

(6) On $[\tau, \tau']$ the function
$x \mapsto \hat a(x) + \frac{12}{13}x = X(x) - \frac12 + \frac{12}{13}x$ has the
derivative $\frac{12}{13} - \frac YZ$ (Lemma B.14 (4)), which is nonnegative
because $13Y \le 12Z = 4X + 9Y$ by $Y \le X$. So the function is nondecreasing,
and its values at $\tau$ and $\tau'$ give the claim. $\square$

*Lean:
[`Seven.Boundary.side_state_transition_bounds`](../../SquaresInCircles/Seven/BoundarySegments.lean#L143),
[`Seven.Boundary.side_segment`](../../SquaresInCircles/Seven/BoundarySegments.lean#L290),
[`Seven.Boundary.side_radial_upper`](../../SquaresInCircles/Seven/BoundarySegments.lean#L399),
[`Seven.Boundary.tie_state`](../../SquaresInCircles/Seven/BoundarySegments.lean#L251),
[`Seven.Boundary.sideTop_state`](../../SquaresInCircles/Seven/BoundarySegments.lean#L241),
[`Seven.Boundary.circle_state_at_label`](../../SquaresInCircles/Seven/BoundarySegments.lean#L182),
[`Seven.Boundary.diagonal_state`](../../SquaresInCircles/Seven/BoundarySegments.lean#L219),
[`Seven.Boundary.tie_of_side`](../../SquaresInCircles/Seven/BoundarySegments.lean#L285),
[`Seven.Boundary.sideA_displacement`](../../SquaresInCircles/Seven/BoundarySegments.lean#L376).*

![A zoom on the side region in the (a, u)-plane: the green region between the purple tie line at the bottom left, the circle phi = 13/4 at the right and the diagonal at the top left, with the orange capped triangle at its left corner. Green segments of slope 9/4 cross it from the tie line to the circle, labelled by their side labels 0.42, 0.48, pi/6, 0.6, 0.66, 0.72; the segment of label pi/6 ends at the side state (1, 1/2), two further segments end on the diagonal, and the orange segment of label pi/4 is the edge V1 V2 of the capped triangle. The transition state (a0, u0) is the lower right corner and the diagonal corner (rd, rd) the top](figures/appb-segments.svg)

*Figure B.4.* The side region is swept by the segments of constant side label
(Proposition B.16), from the transition state, where the segment of label $s_0$
degenerates to a point, to the edge $V_1V_2$ of label $\frac\pi4$. Each segment
runs from its tie state on the tie line (purple dots) to its top (black dots),
on the circle for $\tau \le t_d$ and on the diagonal for $\tau \ge t_d$. The
segment of label $\frac\pi6$ ends at the side state $(1, \frac12)$.

### Lemma B.17 (the slope along the tie line)

Let $s_0 \le \tau \le \frac\pi4$, and let $x$ be real with $\cos x > 0$,
$\sin x \ge 0$ and $\sin x \le \frac94\cos x$. Then

```math
\left(\tfrac{43}{90} - \tfrac45\tau\right)\sin x + \left(\tfrac{13}{10} - \alpha(\tau)\right)\cos x > 0 .
```

For a constant $c$, the left side at $x = c + \tau$ is the derivative in $\tau$
of

```math
-\left(\alpha(\tau) - \tfrac12\right)\sin(c + \tau) + \left(\tfrac45\tau + \tfrac12\right)\cos(c + \tau) ,
```

the support $-(A - \frac12)\sin x + (v + \frac12)\cos x$ of a target $(A, v)$
that moves along the tie line with its label.

*Proof.* Since $\alpha' = -\frac{44}{45}$, the derivative above is

```math
\tfrac{44}{45}\sin x - \left(\alpha(\tau) - \tfrac12\right)\cos x + \tfrac45\cos x - \left(\tfrac45\tau + \tfrac12\right)\sin x ,
```

which is the left side. Since $\alpha$ decreases, Lemma B.10 gives
$\alpha(\tau) \le \alpha(s_0) = a_0 < \frac98$, so
$\frac{13}{10} - \alpha(\tau) > \frac7{40}$. If
$\frac{43}{90} - \frac45\tau \ge 0$, the first term is nonnegative and the
second positive. Otherwise, multiplying $\sin x \le \frac94\cos x$ by the
negative number $\frac{43}{90} - \frac45\tau$, the first term is at least
$\frac94(\frac{43}{90} - \frac45\tau)\cos x$, and the sum is at least

```math
\left(\tfrac{13}{10} - \alpha(\tau) + \tfrac94\left(\tfrac{43}{90} - \tfrac45\tau\right)\right)\cos x
= \left(\tfrac{115}{72} - \tfrac{2\pi}9 - \tfrac{37}{45}\tau\right)\cos x
\ge \left(\tfrac{115}{72} - \tfrac{77\pi}{180}\right)\cos x > \tfrac{91}{360}\cos x > 0 ,
```

using $\tau \le \frac\pi4$ and $\pi < \frac{22}7$. $\square$

*Lean:
[`Seven.Boundary.tie_slope_pos`](../../SquaresInCircles/Seven/BoundarySegments.lean#L269).*

## B.5 Profiles along the boundary

Where a sector is reduced to the boundary of the label regions, what remains is
a function of one label. This section proves three such bounds that Appendices C
and D use: along the side boundary with the target at the transition state, at
the diagonal corner, and along the diagonal. By the Remark after Lemma B.6, the
expression in Lemma B.18 (4) is the support sum $\sigma_1(\frac\pi3)$ for the
signs $(-1, -1)$ with the target at the transition state, and the value in Lemma
B.19 is $\sigma_2(\frac\pi3)$ for the signs $(1, -1)$ with the source at the
diagonal corner and the target at the transition state.

We use the Taylor brackets of [Lemma A.8](appendix-a.md#lemma-a8-polynomial-brackets): for
$0 \le l \le x \le h \le \frac\pi2$,

```math
l - \tfrac{l^3}6 + \tfrac{l^5}{120} - \tfrac{l^7}{5040} \le \sin x \le h - \tfrac{h^3}6 + \tfrac{h^5}{120},
\qquad
1 - \tfrac{h^2}2 + \tfrac{h^4}{24} - \tfrac{h^6}{720} \le \cos x \le 1 - \tfrac{l^2}2 + \tfrac{l^4}{24} .
```

### Lemma B.18 (the transition profile)

For $s_0 \le \tau \le \frac\pi4$ let $\theta(\tau) = \frac\pi3 - \tau + s_0$,
and put

```math
F(\tau) = 1 - Y(\tau) - \left(a_0 - \tfrac12\right)\sin\theta(\tau) + Y_0\cos\theta(\tau) \quad (s_0 \le \tau \le t_d),
\qquad
G(\tau) = \tfrac12 - \delta(\tau) - \left(a_0 - \tfrac12\right)\sin\theta(\tau) + Y_0\cos\theta(\tau) \quad (t_d \le \tau \le \tfrac\pi4).
```

1. $F(\frac{18}{25}) > \frac1{10000}$ and $|F'(\frac{18}{25})| < \frac1{150}$.
2. $F''(\tau) > \frac38$ for $\frac25 \le \tau \le t_d$, and $F(\tau) > 0$
   there.
3. $G$ is nondecreasing on $[t_d, \frac\pi4]$, $G(t_d) = F(t_d)$, and
   $G(\tau) > 0$ there.
4. If $(a, u)$ is admissible with a side label $\ell = \ell(a, u) \ge \frac25$,
   then

   ```math
   \tfrac12 - u - \left(a_0 - \tfrac12\right)\sin\left(\tfrac\pi3 - \ell + s_0\right) + Y_0\cos\left(\tfrac\pi3 - \ell + s_0\right) > 0 .
   ```

Since $\frac12 - \hat u(\tau)$ is $1 - Y(\tau)$ for $\tau \le t_d$ and
$\frac12 - \delta(\tau)$ for $\tau \ge t_d$, $F$ and $G$ are the expression of
(4) with the source at the top of its segment. Their minimum is small, about
$5\cdot 10^{-4}$ near $\tau = 0.72$ (Figure B.5).

*Proof.* By Lemma B.14 (4), $F$ is twice differentiable on $[s_0, t_d]$ with

```math
F' = -\frac XZ + \left(a_0 - \tfrac12\right)\cos\theta + Y_0\sin\theta, \qquad
F'' = \frac{39}{16Z^3} + \left(a_0 - \tfrac12\right)\sin\theta - Y_0\cos\theta ,
```

since $\theta' = -1$.

(1) Let $\tau = \frac{18}{25}$. We use $3.1415 < \pi < 3.1416$, the bounds
$a_0 - \frac12 \in (0.61979, 0.6198)$, $Y_0 \in (0.79136, 0.79137)$ and
$s_0 \in (0.3642, 0.36422)$ of Lemma B.10, and $N = \frac{97}{144}$.

- $D = \frac\pi6 + \frac{43}{600} \in (0.59525, 0.59527)$.
- $Z^2 = \frac{1261}{576} - D^2$ lies between
  $\frac{1261}{576} - 0.59527^2 > 1.834889$ and
  $\frac{1261}{576} - 0.59525^2 < 1.834914$; as $1.3545^2 = 1.83467025$ and
  $1.3547^2 = 1.83521209$, $1.3545 < Z < 1.3547$.
- $X = \frac1N(\frac34 D + \frac13 Z)$ lies in $(1.33302, 1.33315)$, so
  $1.3330 < X < 1.3332$; and $Y = \frac1N(-\frac13 D + \frac34 Z) < 1.21377$.
- $\theta = \frac\pi3 - \frac{18}{25} + s_0$ lies in $(0.69136, 0.69142)$,
  inside $[0.6913, 0.6915]$, so the Taylor brackets with $l = 0.6913$ and
  $h = 0.6915$ give $0.63753 < \sin\theta < 0.63771$ and
  $0.77028 < \cos\theta < 0.77057$.
- $\frac XZ$ lies between $\frac{1.3330}{1.3547} > 0.98398$ and
  $\frac{1.3332}{1.3545} < 0.98428$.

Hence

```math
\begin{aligned}
F\left(\tfrac{18}{25}\right) &> 1 - 1.21377 - 0.6198\cdot 0.63771 + 0.79136\cdot 0.77028 = 0.0005461228 > \tfrac1{10000},\\
F'\left(\tfrac{18}{25}\right) &< -0.98398 + 0.6198\cdot 0.77057 + 0.79137\cdot 0.63771 = -0.0017161513 ,\\
F'\left(\tfrac{18}{25}\right) &> -0.98428 + 0.61979\cdot 0.77028 + 0.79136\cdot 0.63753 = -0.002352418 ,
\end{aligned}
```

and both bounds on $F'$ lie in $(-\frac1{150}, \frac1{150})$.

(2) For $\frac25 \le \tau \le t_d$, Lemma B.14 (3) gives $Z < \frac75$, so
$\frac{39}{16Z^3} > \frac{39}{16}\cdot\frac{125}{343}$, and this is
$\frac{4875}{5488} > \frac78$. The angle $\theta$ lies in
$(\frac\pi6, \frac\pi2)$: it is at least
$\frac\pi3 - t_d + s_0 > 0.6272 > \frac\pi6$ and at most
$\frac\pi3 - \frac25 + s_0 < 1.0115 < \frac\pi2$ (Lemmas B.10, B.11). So
$\sin\theta \ge \frac12$ and $0 \le \cos\theta \le 1$, and with
$a_0 - \frac12 > \frac35$ and $Y_0 < \frac45$,
$F'' > \frac78 + \frac35\cdot\frac12 - \frac45 = \frac38$. Now apply
[Lemma A.3](appendix-a.md#lemma-a3-positivity-from-curvature) on $[\frac25, t_d]$ with the curvature bound
$\kappa = \frac38$ at the point $\tau^* = \frac{18}{25}$, which lies in the
interval because $t_d > \frac{18}{25}$: by (1),
$F'(\tau^*)^2 < \frac1{22500} < \frac3{40000} < 2\kappa F(\tau^*)$, so $F > 0$
on $[\frac25, t_d]$. Indeed, for every $\tau$ in the interval,

```math
F(\tau) \ge F(\tau^*) + F'(\tau^*)(\tau - \tau^*) + \tfrac\kappa2(\tau - \tau^*)^2
\ge F(\tau^*) - \frac{F'(\tau^*)^2}{2\kappa} > 0 .
```

(3) For $t_d \le \tau \le \frac\pi4$, the angle $\theta$ lies in
$[0, \frac\pi2]$ (it is at least $\frac\pi3 - \frac\pi4 + s_0 > 0$ and at most
$\frac\pi3 - t_d + s_0 < \frac\pi2$), and
$G' = \frac{12}5 + (a_0 - \frac12)\cos\theta + Y_0\sin\theta \ge 0$. Since
$\delta(t_d) = r_d = Y(t_d) - \frac12$ (Lemmas B.11 and B.14 (2)),
$\frac12 - \delta(t_d) = 1 - Y(t_d)$ and $G(t_d) = F(t_d) > 0$ by (2). So
$G(\tau) \ge G(t_d) > 0$.

(4) By Proposition B.16 (2), $u \le \hat u(\ell)$. If $\ell \le t_d$, then
$\frac12 - u \ge 1 - Y(\ell)$ and the expression is at least $F(\ell) > 0$ by
(2), since $\ell \ge \frac25$. If $\ell > t_d$, then
$\frac12 - u \ge \frac12 - \delta(\ell)$ and the expression is at least
$G(\ell) > 0$ by (3). $\square$

*Lean:
[`Seven.Boundary.transition_actual_pos`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L205),
[`Seven.Boundary.transitionF`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L92),
[`Seven.Boundary.transitionF_pos`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L152),
[`Seven.Boundary.transitionDiagonalF`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L167),
[`Seven.Boundary.transitionDiagonalF_pos`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L170),
[`Seven.Boundary.test_point`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L30),
[`Seven.Boundary.transition_curvature`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L122),
[`Seven.Boundary.hasDerivAt_transitionF`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L104),
[`Seven.Boundary.hasDerivAt_transitionFD`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L113).*

### Lemma B.19 (the diagonal junction)

Let $\theta_d = t_d + s_0 - \frac\pi6$. Then $0.6246 < \theta_d < 0.6248$ and

```math
\tfrac12 - r_d - \left(a_0 - \tfrac12\right)\sin\theta_d + Y_0\cos\theta_d > 0 .
```

*Proof.* $\theta_d = \frac7{12} - \frac5{12}r_d + s_0$, which by Lemmas B.10 and
B.11 lies between $\frac7{12} - \frac5{12}(0.77476) + 0.3642 > 0.62471$ and
$\frac7{12} - \frac5{12}(0.77475) + 0.36422 < 0.62475$. The Taylor brackets with
$h = 0.6248$ give

```math
0 \le \sin\theta_d \le 0.6248 - \tfrac{0.6248^3}6 + \tfrac{0.6248^5}{120} < 0.584944,
\qquad
\cos\theta_d \ge 1 - \tfrac{0.6248^2}2 + \tfrac{0.6248^4}{24} - \tfrac{0.6248^6}{720} > 0.811078 .
```

So the expression exceeds
$\frac12 - 0.77476 - 0.6198\cdot 0.584944 + 0.79136\cdot 0.811078$, which is
more than $0.0045$. $\square$

*Lean:
[`Seven.Boundary.diagonalAngle`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L21),
[`Seven.Boundary.diagonalValue`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L22),
[`Seven.Boundary.diagonal_angle_bounds`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L71),
[`Seven.Boundary.diagonal_value_pos`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L77).*

### Lemma B.20 (the diagonal profile)

1. $\frac{51}{40}\sin x + \frac{11}{40}\cos x > \frac65$ for
   $\frac\pi3 \le x \le \frac{7\pi}{12} - \frac25$.
2. The function

   ```math
   K(\ell) = \tfrac65\left(\tfrac\pi6 - \ell\right) + \tfrac{51}{40}\cos\left(\tfrac{7\pi}{12} - \ell\right) - \tfrac{11}{40}\sin\left(\tfrac{7\pi}{12} - \ell\right)
   ```

   is nondecreasing on $[\frac25, \frac\pi4]$, and $K(\ell) > \frac{361}{8000}$
   there; in particular $K > 0$.

*Proof.* (1) By [Lemma A.5](appendix-a.md#lemma-a5-concave-trigonometric-sums), the function
$\frac{51}{40}\sin x + \frac{11}{40}\cos x$ is concave on $[0, \frac\pi2]$,
which contains the interval (since $\frac\pi{12} < \frac25$), so it suffices to
check the two ends. At $x = \frac\pi3$ it is $\frac1{80}(51\sqrt3 + 11)$, more
than $\frac1{80}(51(1.73) + 11) = \frac{9923}{8000} > \frac65$. The right end
$x_1 = \frac{7\pi}{12} - \frac25$ lies in $(\frac75, \frac\pi2)$, so
$\cos x_1 \ge 0$ and
$\sin x_1 \ge \sin\frac75 \ge \frac75 - \frac16(\frac75)^3$, and the value is at
least
$\frac{51}{40}(\frac75 - \frac{343}{750}) = \frac{12019}{10000} > \frac65$.

(2) The derivative is

```math
K'(\ell) = -\tfrac65 + \tfrac{51}{40}\sin\left(\tfrac{7\pi}{12} - \ell\right) + \tfrac{11}{40}\cos\left(\tfrac{7\pi}{12} - \ell\right),
```

and for $\frac25 \le \ell \le \frac\pi4$ the angle $\frac{7\pi}{12} - \ell$ lies
in $[\frac\pi3, \frac{7\pi}{12} - \frac25]$, so $K' > 0$ by (1). At
$\ell = \frac25$ put $\epsilon = \frac25 - \frac\pi{12}$, so that
$\frac{7\pi}{12} - \frac25 = \frac\pi2 - \epsilon$ and
$\frac{29}{210} < \epsilon < \frac3{20}$ (by $3 < \pi < \frac{22}7$). Then
$\sin(\frac\pi2 - \epsilon) \le 1$ and

```math
\cos\left(\tfrac\pi2 - \epsilon\right) = \sin\epsilon \ge \epsilon - \tfrac{\epsilon^3}6 > \tfrac{29}{210} - \tfrac16\left(\tfrac3{20}\right)^3 > \tfrac{27}{200},
\qquad
K\left(\tfrac25\right) > \tfrac\pi5 - \tfrac{12}{25} + \tfrac{51}{40}\cdot\tfrac{27}{200} - \tfrac{11}{40} ,
```

which with $\pi > 3.14$ exceeds
$0.628 - 0.48 + 0.172125 - 0.275 = \frac{361}{8000}$. $\square$

*Lean:
[`Seven.Boundary.diagonalK`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L219),
[`Seven.Boundary.diagonalK_pos`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L238),
[`Seven.Boundary.diagonalSlope_gt`](../../SquaresInCircles/Seven/BoundaryProfiles.lean#L223).*

![Two graphs. Left: the transition profile F on the interval from 2/5 to td, a convex blue curve falling from about 0.053 to a minimum just above 0 near 18/25 and rising slightly, continued by a short green piece on the tiny interval from td to pi/4, above a dashed orange parabola that touches the curve at the black dot of abscissa 18/25. Right: the profile K on the interval from 2/5 to pi/4, an increasing blue curve from about 0.052 to 0.085, above a dashed orange level line at 361/8000](figures/appb-profiles.svg)

*Figure B.5.* Left: the transition profile of Lemma B.18. The curvature bound
$F'' > \frac38$ puts $F$ above the parabola of curvature $\frac38$ through its
value and slope at $\frac{18}{25}$ (dashed), whose minimum is positive; beyond
$t_d$ the profile $G$ (green) increases. Right: the profile $K$ of Lemma B.20,
increasing from a value above $\frac{361}{8000}$.

## B.6 The target support on the axial boundary

On the forward axis with the signs $(-1, -1)$ the support sum is
$\frac12 - u - A\sin d + v\cos d + \frac12(|\sin d| + |\cos d|)$ with
$d = \frac\pi3 - \ell + \ell'$ (the Remark after Lemma B.6). When
$\sin d, \cos d \ge 0$ the part that depends on the target is
$-(A - \frac12)\sin d + (v + \frac12)\cos d$, and Appendix D bounds it below by
moving the target to the boundary of the label regions. This section studies
that function along the upper boundary of the axial region: the circular piece
from $(\sqrt3 - \frac12, 0)$ to the transition state, where it decreases, and
the tie line beyond, where it increases up to a switch label.

### Definition B.21 (targets on the boundary)

For labels $\ell, \ell'$ put $d = \frac\pi3 - \ell + \ell'$ and define

```math
\begin{aligned}
\xi(\ell') &= \sqrt{\tfrac{13}4 - \left(\tfrac12 + \tfrac45\ell'\right)^2}, \qquad \eta(\ell') = \tfrac12 + \tfrac45\ell',\\
C(\ell, \ell') &= -\left(\xi(\ell') - 1\right)\sin d + \eta(\ell')\cos d,\\
L(\ell, \ell') &= -\left(\alpha(\ell') - \tfrac12\right)\sin d + \left(\tfrac45\ell' + \tfrac12\right)\cos d,\\
H(\ell, \ell') &= -\left(\hat a(\ell') - \tfrac12\right)\sin d + \left(\hat u(\ell') + \tfrac12\right)\cos d,
\end{aligned}
```

the last for $s_0 \le \ell' \le \frac\pi4$. Let $\omega = \arctan\frac94$, and
call $\omega - \frac\pi3 + \ell$ the *switch label* of $\ell$.

For $0 \le \ell' \le s_0$ the state
$(\xi(\ell') - \frac12, \eta(\ell') - \frac12)$ is
$(\gamma(\frac45\ell'), \frac45\ell')$, the point of the circular piece of the
axial boundary with the axial label $\ell'$ (Lemma B.12 (3) and Proposition B.15
(2)), so $C(\ell, \ell')$ is the target part above for that target. Likewise $L$
is the target part at the tie state of label $\ell'$, and $H$ at the top of the
side label $\ell'$. At the switch label, $d = \omega$.

*Lean:
[`Seven.Boundary.axialX`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L15),
[`Seven.Boundary.axialY`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L16),
[`Seven.Boundary.circleTarget`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L24),
[`Seven.Boundary.lineTarget`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L26),
[`Seven.Boundary.vertexTarget`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L28),
[`Seven.Boundary.switchAngle`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L31),
[`Seven.Boundary.switchLabel`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L32).*

### Lemma B.22 (a derivative ratio)

Let $0 \le \ell' \le s_0$, and write $\xi, \eta$ for $\xi(\ell'), \eta(\ell')$.

1. $\frac85 < \xi < \frac74$, $\frac12 \le \eta \le Y_0$ and
   $\xi^2 + \eta^2 = \frac{13}4$.
2. $\xi$ and $\eta$ are differentiable, with $\xi' = -\frac45\cdot\frac\eta\xi$
   and $\eta' = \frac45$.
3. The function $\rho = \frac{\xi(\frac95 - \xi)}{\eta(\xi - \frac45)}$ is
   nonnegative, and $\rho(0) < 2 - \sqrt3$.
4. The derivative of $\rho$ is

   ```math
   \rho' = \frac{4\left(25\xi^4 - 65\xi^3 + 25\xi^2\eta^2 + 36\xi^2 - 40\xi\eta^2 + 36\eta^2\right)}{5\xi\eta^2(5\xi - 4)^2} ,
   \qquad
   1 - \rho' = \frac{P(\xi)}{5\xi(5\xi - 4)^2(13 - 4\xi^2)} ,
   ```

   where the quintic

   ```math
   P(X) = -500X^5 + 800X^4 + 1705X^3 - 3900X^2 + 3120X - 1872
   ```

   is positive on $[\frac85, \frac74]$. In particular $\rho' < 1$.
5. $(2 - \sqrt3)\cos x \le \sin x$ for $\frac\pi{12} \le x \le \frac\pi2$.

The number $2 - \sqrt3$ is $\tan\frac\pi{12}$ (see the proof of (5)), so (3)
and (5) give $\rho(0) < \tan x$ for $\frac\pi{12} \le x < \frac\pi2$.
Proposition B.23 uses this with $x$ the angle $d$ of the target support at
$\ell' = 0$, and then (4) to keep $\rho$ below $\tan d$ as $\ell'$ grows
(Figure B.6).

*Proof.* (1) Let $w = \frac45\ell' \in [0, u_0]$ (as $s_0 = \frac54 u_0$). Then
$\xi = \gamma(w) + \frac12$ and $\eta = w + \frac12$, so
$\xi^2 + \eta^2 = \frac{13}4$ (Lemma B.12 (1)) and
$\frac12 \le \eta \le u_0 + \frac12 = Y_0$. By Lemma B.12 (2) and (3),
$\gamma(w) \ge \gamma(u_0) = a_0$, so $\xi \ge a_0 + \frac12 > \frac85$; and
since $(\gamma(w), w)$ is admissible, Lemma B.7 gives
$\xi \le \sqrt3 < 1.733 < \frac74$.

(2) The radicand $\frac{13}4 - \eta^2 = \xi^2$ is positive, and the chain rule
gives $\xi' = -\frac{\eta\eta'}\xi = -\frac45\cdot\frac\eta\xi$.

(3) Since $\frac45 < \xi < \frac74 < \frac95$ and $\eta > 0$, $\rho \ge 0$. At
$\ell' = 0$, $\xi = \sqrt3$ and $\eta = \frac12$; multiplying the numerator and
the denominator of $\rho(0)$ by $5$, and using
$(2 - \sqrt3)(5\sqrt3 - 4) = 14\sqrt3 - 23$,

```math
\rho(0) = \frac{2\sqrt3\left(\frac95 - \sqrt3\right)}{\sqrt3 - \frac45} = \frac{18\sqrt3 - 30}{5\sqrt3 - 4},
\qquad
2 - \sqrt3 - \rho(0) = \frac{(14\sqrt3 - 23) - (18\sqrt3 - 30)}{5\sqrt3 - 4} = \frac{7 - 4\sqrt3}{5\sqrt3 - 4} .
```

Both $7 - 4\sqrt3$ and $5\sqrt3 - 4$ are positive, as $(4\sqrt3)^2 = 48 < 49$
and $(5\sqrt3)^2 = 75 > 16$. So $\rho(0) < 2 - \sqrt3$; numerically
$\rho(0) \approx 0.2525$ and $2 - \sqrt3 \approx 0.2679$.

(4) The formula for $\rho'$ follows from the quotient rule with (2): the
numerator $\xi(\frac95 - \xi)$ of $\rho$ has derivative $\xi'(\frac95 - 2\xi)$
and the denominator $\eta(\xi - \frac45)$ has derivative
$\frac45(\xi - \frac45) + \eta\xi'$. Substituting $\xi' = -\frac{4\eta}{5\xi}$
and expanding,

```math
\xi'\left(\tfrac95 - 2\xi\right)\eta\left(\xi - \tfrac45\right) - \xi\left(\tfrac95 - \xi\right)\left(\tfrac45\left(\xi - \tfrac45\right) + \eta\xi'\right)
= \frac{4\left(25\xi^4 - 65\xi^3 + 25\xi^2\eta^2 + 36\xi^2 - 40\xi\eta^2 + 36\eta^2\right)}{125\xi} ,
```

and dividing by the squared denominator
$\eta^2(\xi - \frac45)^2 = \frac1{25}\eta^2(5\xi - 4)^2$ gives the displayed
quotient. To compare $\rho'$ with $1$, substitute
$\eta^2 = \frac{13}4 - \xi^2$ in that quotient: its numerator becomes
$4(-25\xi^3 + \frac{325}4\xi^2 - 130\xi + 117)$ and its denominator
$\frac54\xi(5\xi - 4)^2(13 - 4\xi^2)$, so

```math
\rho' = \frac{16\left(-25\xi^3 + \frac{325}4\xi^2 - 130\xi + 117\right)}{5\xi(5\xi - 4)^2(13 - 4\xi^2)} .
```

The formula for $1 - \rho'$ follows, because

```math
\begin{aligned}
5X(5X - 4)^2(13 - 4X^2) &= -500X^5 + 800X^4 + 1305X^3 - 2600X^2 + 1040X,\\
16\left(-25X^3 + \tfrac{325}4X^2 - 130X + 117\right) &= -400X^3 + 1300X^2 - 2080X + 1872 ,
\end{aligned}
```

and the first right side minus the second is $P(X)$. The denominator
$5\xi(5\xi - 4)^2(13 - 4\xi^2)$ is positive, since $\xi > \frac85$ and
$13 - 4\xi^2 = 4\eta^2 > 0$.

It remains to show that $P > 0$ on $[\frac85, \frac74]$, which contains $\xi$
by (1). The quintic is concave there (Figure B.6): its derivatives are

```math
P'(X) = -2500X^4 + 3200X^3 + 5115X^2 - 7800X + 3120, \qquad
P''(X) = -10000X^3 + 9600X^2 + 10230X - 7800 ,
```

and expanding the cubic $P''$ about $\frac85$,

```math
P''\left(\tfrac85 + t\right) = -7816 - 35850t - 38400t^2 - 10000t^3 ,
```

which is negative for $t \ge 0$. At the ends of the interval

```math
P\left(\tfrac85\right) = \tfrac{2992}{25}, \qquad P\left(\tfrac74\right) = \tfrac{20113}{256} ,
```

both positive. By [Lemma A.4](appendix-a.md#lemma-a4-positivity-from-concavity), applied to $P$ with its derivatives
$P'$ and $P''$, $P > 0$ on $[\frac85, \frac74]$; its proof shows more: $P$ lies
above its chord, so $P \ge \frac{20113}{256}$ there. Hence $1 - \rho' > 0$.

(5) Since $\frac\pi{12} = \frac\pi3 - \frac\pi4$, the subtraction formulas give

```math
\sin\tfrac\pi{12} = \tfrac{\sqrt3}2\cdot\tfrac{\sqrt2}2 - \tfrac12\cdot\tfrac{\sqrt2}2 = \tfrac{\sqrt2}4\left(\sqrt3 - 1\right),
\qquad
\cos\tfrac\pi{12} = \tfrac12\cdot\tfrac{\sqrt2}2 + \tfrac{\sqrt3}2\cdot\tfrac{\sqrt2}2 = \tfrac{\sqrt2}4\left(\sqrt3 + 1\right),
```

and $(2 - \sqrt3)(\sqrt3 + 1) = \sqrt3 - 1$, so
$\sin\frac\pi{12} = (2 - \sqrt3)\cos\frac\pi{12}$: that is,
$\tan\frac\pi{12} = 2 - \sqrt3$. For $\frac\pi{12} \le x \le \frac\pi2$ we have
$0 \le x - \frac\pi{12} \le \pi$, so

```math
0 \le \sin\left(x - \tfrac\pi{12}\right) = \sin x\cos\tfrac\pi{12} - \cos x\sin\tfrac\pi{12}
= \cos\tfrac\pi{12}\left(\sin x - (2 - \sqrt3)\cos x\right) ,
```

and $\cos\frac\pi{12} > 0$. $\square$

*Lean:
[`Seven.Boundary.axial_circle_bounds`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L34),
[`Seven.Boundary.hasDerivAt_axialX`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L57),
[`Seven.Boundary.hasDerivAt_axialY`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L52),
[`Seven.Boundary.ratio`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L17),
[`Seven.Boundary.ratio_nonneg`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L128),
[`Seven.Boundary.ratio_zero_lt`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L136),
[`Seven.Boundary.ratioD`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L19),
[`Seven.Boundary.hasDerivAt_ratio`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L68),
[`Seven.Boundary.ratio_numerator_pos`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L87),
[`Seven.Boundary.ratio_derivative_lt_one`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L105),
[`Seven.Boundary.tan_twelfth_le`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L147).*

![Two graphs. Left: the quintic P on the interval from 8/5 to 7/4, a concave blue arch from 2992/25, about 120, at 8/5 up to about 132 and down to 20113/256, about 79, at 7/4, continued in grey beyond both ends, above the orange chord joining its two end points and far above the axis. Right: on the interval from 0 to s0, the increasing blue ratio rho, from rho(0), about 0.25, to about 0.45, below the orange curve tan d for the source label pi/4, which starts just above it at 2 - root 3, about 0.27, and rises to about 0.72](figures/appb-ratio.svg)

*Figure B.6.* Lemma B.22. (a) The quintic $P$ (blue) is concave on
$[\frac85, \frac74]$, so it lies above its chord (orange) through the positive
end values $P(\frac85) = \frac{2992}{25}$ and $P(\frac74) = \frac{20113}{256}$.
(b) The ratio $\rho$ (blue) and $\tan d$ (orange) on $[0, s_0]$ for the source
label $\ell = \frac\pi4$, where the angle $d = \frac\pi{12} + \ell'$ is
smallest. At $\ell' = 0$, $\rho(0) \approx 0.2525$ lies just below
$\tan\frac\pi{12} = 2 - \sqrt3 \approx 0.2679$, and $\rho$ stays below
$\tan d$; this is $E > 0$ in the proof of Proposition B.23. For a smaller
source label, $d$ and $\tan d$ are larger.

### Proposition B.23 (the circular piece)

Let $\frac25 \le \ell \le \frac\pi4$. Then $\ell' \mapsto C(\ell, \ell')$ is
nonincreasing on $[0, s_0]$, and

```math
C(\ell, s_0) = L(\ell, s_0) = -\left(a_0 - \tfrac12\right)\sin\left(\tfrac\pi3 - \ell + s_0\right) + Y_0\cos\left(\tfrac\pi3 - \ell + s_0\right) .
```

*Proof.* For $0 \le \ell' \le s_0$ the angle $d = \frac\pi3 - \ell + \ell'$
satisfies $\frac\pi{12} \le d < \frac\pi2$: the lower bound because
$\ell \le \frac\pi4$, the upper because
$d \le \frac\pi3 - \frac25 + s_0 < 1.0115$. So $\sin d, \cos d \ge 0$. By Lemma
B.22 (2), since $d' = 1$,

```math
\frac{\partial C}{\partial\ell'} = \tfrac45\cdot\tfrac\eta\xi\sin d - (\xi - 1)\cos d + \tfrac45\cos d - \eta\sin d
= -\frac{\eta\left(\xi - \frac45\right)}\xi\,E, \qquad E = \sin d - \rho\cos d .
```

The factor $\frac\eta\xi(\xi - \frac45)$ is positive, so it suffices that
$E > 0$. By Lemma B.22 (3) and (4), $E' = (1 - \rho')\cos d + \rho\sin d \ge 0$,
so $E$ is nondecreasing on $[0, s_0]$
([Lemma A.1](appendix-a.md#lemma-a1-monotonicity-from-the-derivative) (1)). At $\ell' = 0$ the angle is
$d_0 = \frac\pi3 - \ell$, which lies in $[\frac\pi{12}, \frac\pi2)$, so
$\cos d_0 > 0$, and Lemma B.22 (5) gives $\sin d_0 \ge (2 - \sqrt3)\cos d_0$.
With $\rho(0) < 2 - \sqrt3$ (Lemma B.22 (3)),

```math
E(0) = \sin d_0 - \rho(0)\cos d_0 \ge \left(2 - \sqrt3 - \rho(0)\right)\cos d_0 > 0 .
```

So $E \ge E(0) > 0$ on $[0, s_0]$; as $\cos d > 0$, this says that $\rho$ stays
below $\tan d$ (Figure B.6 (b)).

At $\ell' = s_0$: $\xi(s_0) = \gamma(u_0) + \frac12 = a_0 + \frac12$ and
$\eta(s_0) = Y_0$ (Lemma B.12 (3)), and $\alpha(s_0) = a_0$ and
$\frac45 s_0 + \frac12 = Y_0$ (Lemma B.10), which gives the two values.
$\square$

*Lean:
[`Seven.Boundary.circleTarget_decreases`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L160),
[`Seven.Boundary.circleTarget_transition`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L216),
[`Seven.Boundary.lineTarget_transition`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L230).*

### Lemma B.24 (the switch angle)

$0 < \omega < \frac\pi2$ and $\cos\omega - \frac49\sin\omega = 0$. For
$0 \le x \le \frac\pi2$, $\cos x - \frac49\sin x \ge 0$ if and only if
$x \le \omega$.

*Proof.* $\tan\omega = \frac94 > 0$ gives the range and
$\sin\omega = \frac94\cos\omega$. On $[0, \frac\pi2]$ the function
$\cos x - \frac49\sin x$ is strictly decreasing, as $\cos$ decreases and $\sin$
increases there, and it vanishes at $\omega$. $\square$

*Lean:
[`Seven.Boundary.switch_range`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L236),
[`Seven.Boundary.switch_zero`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L239),
[`Seven.Boundary.switch_iff`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L244).*

### Proposition B.25 (the straight piece)

Let $\frac25 \le \ell \le \frac\pi4$ and $s_0 \le \ell' \le \frac\pi4$ with
$\ell' \le \omega - \frac\pi3 + \ell$. Then $y \mapsto L(\ell, y)$ is increasing
on $[s_0, \ell']$, with a positive derivative, and so
$C(\ell, s_0) = L(\ell, s_0) \le L(\ell, \ell')$.

*Proof.* For $s_0 \le y \le \ell'$ let $x = \frac\pi3 - \ell + y$. Then
$0 < x < \frac\pi2$, since $x \ge \frac\pi3 - \frac\pi4 + s_0 > 0$ and
$x \le \frac\pi3 - \frac25 + \frac\pi4 < 1.433$; and $x \le \omega$, since
$y \le \omega - \frac\pi3 + \ell$. By Lemma B.24, $\sin x \le \frac94\cos x$,
and $\cos x > 0$, $\sin x \ge 0$. By Lemma B.17 with $\tau = y$ and
$c = \frac\pi3 - \ell$, the derivative of $L(\ell, \cdot)$ at $y$ is positive.
With Proposition B.23 this gives the claim. $\square$

*Lean:
[`Seven.Boundary.lineTarget_derivative_positive`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L263),
[`Seven.Boundary.lineTarget_low_min`](../../SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean#L276).*

![Graphs of the target support against the target label for four source labels 2/5, 0.55, 0.7 and pi/4, in four colours. Each curve decreases slowly (solid) from the target label 0 to s0, where it has a corner marked by a dot, and then increases (dashed) along the tie line up to the switch label or pi/4](figures/appb-targets.svg)

*Figure B.7.* The target part of the forward sum with the signs $(-1, -1)$, for
a target on the upper boundary of the axial region: $C(\ell, \ell')$ on the
circular piece $0 \le \ell' \le s_0$ (solid, Proposition B.23) and
$L(\ell, \ell')$ on the tie line from $s_0$ up to the switch label or
$\frac\pi4$ (dashed, Proposition B.25). For each source label $\ell$ the minimum
is at the transition state, $\ell' = s_0$.

## B.7 The easy sectors

Four sectors hold for all labels and give positive sums (Figure B.8). On the
outward axis the far edge of $S$ is out of reach of $T$; on the backward axis
$T$ contains its marker point, which lies beyond the lower edge of $S$; on the
inward axis with a negative source sign the marker arc of $T$ reaches past the
near edge of $S$; and on the forward axis with positive signs a Cauchy–Schwarz
bound on the disk $\varphi \le \frac{13}4$ suffices.

![Four panels, each with the disk centre o, a faint unit circle and a blue source square S and a green target square T of a canonical pair at the gap pi/3. (a) Outward axis: the side square Q(1, 1/2) and the square Q(0, 1) above it; a dashed circle of radius 31/25 about o contains the centre of T, an orange dashed line x = 37/50 and a blue dashed line x = a + 1/2 through the far edge of S, and an orange bracket from the leftmost point of T to that edge. (b) Backward axis with source sign 1: the same squares; the marker point of T on the unit circle above o, and an orange segment from it down to the dashed line y = u - 1/2 of the lower edge of S. (c) Inward axis with source sign -1: the side column, S below the axis and T above it; the marker arc of T drawn thick on the unit circle, and an orange segment from the dashed near-edge line x = a - 1/2 of S to the lower end of the arc. (d) Forward axis with both signs 1: the pair of Figure B.1 with the shadows of S and T on a vertical line and an orange bracket over their overlap](figures/appb-easy.svg)

*Figure B.8.* The easy sectors. (a) Proposition B.26: $T$ has a point to the
left of $x = \frac{37}{50}$, since its centre lies in the dashed disk of radius
$\frac{31}{25}$, while $S$ reaches $x = a + \frac12 \ge 1$. (b) Proposition
B.27: the marker point of $T$ lies in $T$, above the lower edge of $S$; the
orange segment is a lower bound for $\sigma_3(\frac\pi3)$. (c) Proposition B.28:
the end of the marker arc of $T$ nearest to the axis lies to the right of the
near edge of $S$; the orange segment is a lower bound for $\sigma_2(\frac\pi3)$.
(d) Proposition B.29: the shadows on the forward axis overlap. In (a) to (c) the
pairs are contacts of the second and first kinds; the propositions hold for all
admissible states.

### Proposition B.26 (the outward axis)

Let $(a, u)$ and $(A, v)$ be admissible and $s, t$ signs. Then
$\sigma_0(\frac\pi3) > 0$.

*Proof.* By Lemma B.5 (1),
$\sigma_0(\frac\pi3) = a + \frac12 + h(A, tv, \pi - d)$. Since
$(A, |tv|) = (A, v)$ is admissible, Lemma B.4 (1) gives
$h(A, tv, \pi - d) > -\frac{37}{50}$, and $a \ge \frac12$. So
$\sigma_0(\frac\pi3) > 1 - \frac{37}{50} = \frac{13}{50}$. $\square$

*Lean:
[`Seven.fixed_gap_outward`](../../SquaresInCircles/Seven/EasySectors.lean#L19).*

### Proposition B.27 (the backward axis)

Let $(a, u)$ and $(A, v)$ be admissible and $s, t$ signs. Then
$\sigma_3(\frac\pi3) > 0$.

*Proof.* By Lemma B.5 (1), $\sigma_3(\frac\pi3) = \frac12 - su + h(A, tv, z)$
with $z = \frac{5\pi}2 - d = \frac{5\pi}2 - \frac\pi3 - s\ell + t\ell'$, where
$\ell = \ell(a, u)$ and $\ell' = \ell(A, v)$. Apply Lemma B.4 (2) to the target
with $x = t\ell'$, its marker: since
$z - x = 2\pi + \frac\pi2 - (\frac\pi3 + s\ell)$,

```math
\sigma_3\left(\tfrac\pi3\right) \ge \tfrac12 - su + \cos(z - x) = \tfrac12 - su + \sin\left(\tfrac\pi3 + s\ell\right) .
```

If $s = 1$, then $\sin(\frac\pi3 + \ell) = \cos(\frac\pi6 - \ell)$ is at least
$1 - \frac12(\frac\pi6 - \ell)^2$, and
$|\frac\pi6 - \ell| \le \frac\pi6 < \frac35$ because $0 \le \ell \le \frac\pi4$
([Lemma 9.7](seven.md#lemma-97-the-label)); so
$\sin(\frac\pi3 + \ell) > 1 - \frac9{50} = \frac{41}{50}$. With
$u < \frac{31}{40}$ ([Lemma 9.5](seven.md#lemma-95-admissible-states)), $\sigma_3(\frac\pi3)$ exceeds
$\frac12 - \frac{31}{40} + \frac{41}{50} = \frac{109}{200}$.
If $s = -1$, then $\frac\pi3 - \ell \in [\frac\pi{12}, \frac\pi3]$, so
$\sin(\frac\pi3 - \ell) \ge 0$ and
$\sigma_3(\frac\pi3) \ge \frac12 + u \ge \frac12$. $\square$

*Lean:
[`Seven.fixed_gap_backward`](../../SquaresInCircles/Seven/EasySectors.lean#L28).*

### Proposition B.28 (the inward axis with a negative source sign)

Let $(a, u)$ and $(A, v)$ be admissible and $t$ a sign. Then, for the signs
$(-1, t)$, $\sigma_2(\frac\pi3) > 0$.

*Proof.* Here $d = \frac\pi3 - \ell - t\ell'$ with $\ell = \ell(a, u)$,
$\ell' = \ell(A, v)$, and by Lemma B.5 (1),
$\sigma_2(\frac\pi3) = \frac12 - a + h(A, tv, z)$ with
$z = 2\pi - \frac\pi3 + \ell + t\ell'$. Apply Lemma B.4 (2) with
$x = t\ell' - \frac12$, the end of the marker arc of the target on the side of
the source: $z - x = 2\pi - y$ with $y = \frac\pi3 - \ell - \frac12$, so

```math
\sigma_2\left(\tfrac\pi3\right) \ge \tfrac12 - a + \cos y .
```

Since $0 \le \ell \le \frac\pi4$ and $3.14 < \pi < 3.1416$, $y$ lies between
$\frac\pi{12} - \frac12 > -0.24$ and $\frac\pi3 - \frac12 < 0.548$, so
$y^2 < \frac49$ and
$\cos y \ge 1 - \frac{y^2}2 > \frac79$. By Lemma B.7,
$a \le \sqrt3 - \frac12 < 1.233$. Hence
$\sigma_2(\frac\pi3) > \frac12 - 1.233 + \frac79 = \frac{403}{9000}$. $\square$

*Lean:
[`Seven.fixed_gap_inward_negative`](../../SquaresInCircles/Seven/EasySectors.lean#L56).*

### Proposition B.29 (the forward axis with positive signs)

Let $(a, u)$ and $(A, v)$ be admissible. Then, for the signs $(1, 1)$,
$\sigma_1(\frac\pi3) > 0$.

*Proof.* Let $\ell = \ell(a, u)$, $\ell' = \ell(A, v)$ and
$z = \frac\pi6 - \ell + \ell'$. By the Remark after Lemma B.6 (second row),

```math
\sigma_1\left(\tfrac\pi3\right) = \tfrac12 + u - A\cos z - v\sin z + \tfrac12(|\cos z| + |\sin z|)
= \tfrac12 + u + h(A, v, \pi + z) .
```

Recall $u \ge \frac45\ell$, because $\ell \le \mathrm{axial}(u)$.

1. *If $\ell \ge \frac5{16}$*, then $u \ge \frac14$, and Lemma B.4 (1) gives
   $\sigma_1(\frac\pi3) > \frac12 + \frac14 - \frac{37}{50} = \frac1{100}$.

2. *If $\ell < \frac5{16}$*, then, using $\pi > 3.14$,
   $\frac{21}{100} < \frac\pi6 - \frac5{16} < z$ and
   $z \le \frac\pi6 + \frac\pi4 < \frac\pi2$, so $\cos z, \sin z \ge 0$ and the
   absolute values in the closed form can be dropped.

3. *If moreover $z \ge \frac\pi4$*, then $\sin z \ge \cos z$. With $A - v \ge 0$
   and $A + v < \frac{31}{20}$ (Lemma B.7),

   ```math
   A\cos z + v\sin z = \tfrac12\left((A + v)(\cos z + \sin z) - (A - v)(\sin z - \cos z)\right)
   \le \tfrac{31}{40}(\cos z + \sin z),
   ```

   and $(\cos z + \sin z)^2 = 1 + 2\sin z\cos z \le 2 < \frac94$. So

   ```math
   \sigma_1\left(\tfrac\pi3\right) \ge \tfrac12 + u - \tfrac{11}{40}(\cos z + \sin z) > \tfrac12 - \tfrac{11}{40}\cdot\tfrac32 = \tfrac7{80} .
   ```

4. *If instead $z < \frac\pi4$*, apply Lemma B.3 to
   $(X, Y) = (A + \frac12, v + \frac12)$ with $p = -\cos z$, $r = -\sin z$ and
   $c = \frac{181}{100}$, which is allowed since
   $\frac{13}4 \le (\frac{181}{100})^2 = 3.2761$:
   $-(A + \frac12)\cos z - (v + \frac12)\sin z \ge -\frac{181}{100}$. Hence

   ```math
   \sigma_1\left(\tfrac\pi3\right) = \tfrac12 + u - \left(A + \tfrac12\right)\cos z - \left(v + \tfrac12\right)\sin z + \cos z + \sin z
   \ge \tfrac12 + u - \tfrac{181}{100} + \cos z + \sin z .
   ```

   The function $\cos + \sin$ is nondecreasing on $[0, \frac\pi4]$, where its
   derivative $\cos - \sin$ is nonnegative, and
   $0 < \frac\pi6 - \ell \le z < \frac\pi4$. So with $x = \frac\pi6 - \ell$ and
   $u \ge \frac45\ell = \frac{2\pi}{15} - \frac45 x$,

   ```math
   \sigma_1\left(\tfrac\pi3\right) \ge \tfrac12 + \tfrac{2\pi}{15} - \tfrac{181}{100} + k(x), \qquad
   k(x) = -\tfrac45 x + \sin x + \cos x ,
   ```

   where $\frac{21}{100} < x \le \frac\pi6$. By [Lemma A.5](appendix-a.md#lemma-a5-concave-trigonometric-sums), $k$
   is concave on $[0, \frac\pi2]$, so on $[\frac{21}{100}, \frac\pi6]$ it
   exceeds $m = \frac{131}{100} - \frac{2\pi}{15}$ as soon as it does at both
   ends. At $\frac{21}{100}$, by $\sin x \ge x - \frac{x^3}6$ and
   $\cos x \ge 1 - \frac{x^2}2$,

   ```math
   k\left(\tfrac{21}{100}\right) \ge -0.168 + \left(0.21 - \tfrac{0.21^3}6\right) + \left(1 - \tfrac{0.21^2}2\right) = 1.0184065 ,
   ```

   while $m < 1.31 - \frac{2(3.14)}{15} < 0.8914$. At $\frac\pi6$,
   $k(\frac\pi6) = -\frac{2\pi}{15} + \frac12 + \frac{\sqrt3}2 > m$ because
   $\sqrt3 > 1.73 > \frac{81}{50}$. So $k(x) > m$, that is,
   $\sigma_1(\frac\pi3) > 0$. $\square$

*Lean:
[`Seven.fixed_gap_forward_positive`](../../SquaresInCircles/Seven/EasySectors.lean#L76),
[`cos_add_sin_mono`](../../SquaresInCircles/Common/Trigonometry.lean#L79).*

## B.8 The capped labels

A label equal to $\frac\pi4$ is the same for every capped state, so a support
sum at a capped state is an affine function of that state. The capped states
fill the triangle of Figure B.9, whose vertices are admissible with active
labels; an affine function on the triangle is at least its least value at a
vertex. This reduces the capped labels to active ones.

### Lemma B.30 (the capped triangle)

Let

```math
V_0 = \left(\tfrac\pi5, \tfrac\pi5\right), \qquad
V_1 = \left(\tfrac19\left(7 - \tfrac\pi5\right), \tfrac\pi5\right), \qquad
V_2 = \left(\tfrac15(7 - \pi), \tfrac15(7 - \pi)\right) .
```

1. Each $V_i$ is an admissible state with label $\frac\pi4$, which is axial at
   $V_0$ and $V_1$ and side at $V_2$. In particular each $V_i$ has an active
   label.
2. Let $(a, u)$ be admissible with $\ell(a, u) = \frac\pi4$. Then the weights
   $w_0 = 7 - \pi - 9a + 4u$, $w_1 = 9(a - u)$ and $w_2 = 5u - \pi$ are
   nonnegative, $w_0 + w_1 + w_2 = 7 - 2\pi > 0$, and
   $w_0V_0 + w_1V_1 + w_2V_2 = (7 - 2\pi)(a, u)$.
3. In (2), for all real $p, q, r$ there is an $i$ with
   $p + q a_i + r u_i \le p + q a + r u$, where $V_i = (a_i, u_i)$.

*Proof.* (1) From $3.14 < \pi < \frac{22}7$: $0.628 < \frac\pi5 < 0.6286$,
$0.7079 < \frac19(7 - \frac\pi5) < 0.708$ and
$0.7714 < \frac15(7 - \pi) < 0.772$. So every coordinate of every $V_i$ lies in
$[\frac12, \frac{193}{250})$, the second coordinate is at most the first, and
$\varphi(V_i) < 2(\frac{193}{250} + \frac12)^2 = \frac{50562}{15625}$, which is
less than $\frac{13}4$. The labels follow from the identities at the start of
§B.3:

| vertex | $\mathrm{axial} - \frac\pi4$ | $\mathrm{side} - \frac\pi4$ |
| --- | --- | --- |
| $V_0$ | $0$ | $\frac7{12} - \frac\pi6 > 0$ |
| $V_1$ | $0$ | $0$ |
| $V_2$ | $\frac74 - \frac\pi2 > 0$ | $0$ |

(2) $\ell(a, u) = \frac\pi4$ means $\mathrm{axial}(u) \ge \frac\pi4$, that is,
$w_2 \ge 0$, and $\mathrm{side}(a, u) \ge \frac\pi4$, that is, $w_0 \ge 0$
(§B.3); and $w_1 \ge 0$ because $u \le a$. The sum is
$7 - \pi - 9a + 4u + 9a - 9u + 5u - \pi = 7 - 2\pi$. Expanding the weighted sum
of the vertices coordinate by coordinate,

```math
\begin{aligned}
\tfrac\pi5 w_0 + \tfrac19\left(7 - \tfrac\pi5\right)w_1 + \tfrac{7 - \pi}5 w_2
&= \tfrac\pi5(7 - \pi - 9a + 4u) + \left(7 - \tfrac\pi5\right)(a - u) + \tfrac{7 - \pi}5(5u - \pi) = (7 - 2\pi)a,\\
\tfrac\pi5 w_0 + \tfrac\pi5 w_1 + \tfrac{7 - \pi}5 w_2
&= \tfrac\pi5(7 - \pi - 5u) + \tfrac{7 - \pi}5(5u - \pi) = (7 - 2\pi)u .
\end{aligned}
```

(3) Let $f(x, y) = p + qx + ry$, and choose $i$ with $f(V_i)$ least. Since $f$
is affine and the weights are nonnegative, (2) gives

```math
(7 - 2\pi)f(V_i) = \sum_j w_j f(V_i) \le \sum_j w_j f(V_j) = (7 - 2\pi) f(a, u) ,
```

and $7 - 2\pi > 0$. $\square$

*Lean: [`Seven.capVertex`](../../SquaresInCircles/Seven/FixedGap.lean#L51),
[`Seven.capVertex_admissible`](../../SquaresInCircles/Seven/FixedGap.lean#L54),
[`Seven.capVertex_label`](../../SquaresInCircles/Seven/FixedGap.lean#L66),
[`Seven.capVertex_active`](../../SquaresInCircles/Seven/FixedGap.lean#L72),
[`Seven.cap_vertex_le`](../../SquaresInCircles/Seven/FixedGap.lean#L91),
[`Seven.exists_le_weighted_sum`](../../SquaresInCircles/Seven/FixedGap.lean#L81).*

![A zoom on the capped triangle in the (a, u)-plane: the orange triangle with vertices V0 on the diagonal u = a at the lower left, V1 on the line u = pi/5 to its right, and V2 on the diagonal at the top; the dashed lines u = pi/5 and 9a - 4u = 7 - pi through its edges, the purple tie line through V1, the grey half-plane u > a above the diagonal where there are no states, the words axial below the triangle and side to its right, and a capped state (a, u) inside joined to the three vertices by dashed segments](figures/appb-capped.svg)

*Figure B.9.* The capped triangle $V_0V_1V_2$ of Lemma B.30. Its edges lie on
the line $u = \frac\pi5$, where $\mathrm{axial}(u) = \frac\pi4$, on the line
$9a - 4u = 7 - \pi$, where $\mathrm{side}(a, u) = \frac\pi4$, and on the
diagonal. A capped state $(a, u)$ is the convex combination of the vertices with
the weights $w_i/(7 - 2\pi)$.

### Proposition B.31 (reduction to active labels)

Suppose that any two admissible states with active labels, with any signs, have
the gap property on every axis. Then any two admissible states, with any signs,
have the gap property on every axis.

*Proof.* Fix signs $s, t$ and an axis $k$, and put $\theta = k\frac\pi2$.

1. *A capped target.* Let $(a, u)$ be admissible and suppose that the gap
   property holds for $(a, u)$ and each $V_i$. Let $(A, v)$ be admissible with
   $\ell(A, v) = \frac\pi4$. Put
   $\psi = \theta + \pi - \frac\pi3 - s\ell(a, u) + t\frac\pi4$. For every state
   $(x, y)$ of label $\frac\pi4$ the support sum of $(a, u)$ and $(x, y)$ is

   ```math
   \sigma_k\left(\tfrac\pi3\right) = h(a, su, \theta) + h(x, ty, \psi)
   = \left(h(a, su, \theta) + \tfrac12(|\cos\psi| + |\sin\psi|)\right) + x\cos\psi + y\,t\sin\psi ,
   ```

   an affine function of $(x, y)$ with the same coefficients for $(A, v)$ and
   for each $V_i$. By Lemma B.30 (3) there is an $i$ at which it is at most its
   value at $(A, v)$. So the sum for $(A, v)$ is at least the sum for $V_i$,
   which is nonnegative. If the sum for $(A, v)$ were zero, the sum for $V_i$
   would be zero too, and by hypothesis $(a, u)$ and $V_i$ would form a contact;
   but no state of a contact has the label $\frac\pi4$
   ([Lemma 9.16](seven.md#lemma-916-contacts)), while $\ell(V_i) = \frac\pi4$. So the sum
   for $(A, v)$ is positive, and the gap property holds.

2. *A capped source.* In the same way, let $(A, v)$ be admissible, suppose that
   the gap property holds for each $V_i$ and $(A, v)$, and let $(a, u)$ be
   admissible with $\ell(a, u) = \frac\pi4$. For every state $(x, y)$ of label
   $\frac\pi4$,

   ```math
   \sigma_k\left(\tfrac\pi3\right) = h(x, sy, \theta) + h\left(A, tv, \theta + \pi - \tfrac\pi3 - s\tfrac\pi4 + t\ell(A, v)\right),
   \qquad h(x, sy, \theta) = x\cos\theta + y\,s\sin\theta + \tfrac12(|\cos\theta| + |\sin\theta|),
   ```

   again affine in $(x, y)$, and the argument of step 1 applies.

3. *Conclusion.* Let $(a, u)$ and $(A, v)$ be admissible. If $\ell(a, u)$ is
   active: when $\ell(A, v)$ is active the hypothesis applies; otherwise
   $\ell(A, v) = \frac\pi4$, the hypothesis applies to $(a, u)$ and each $V_i$
   (Lemma B.30 (1)), and step 1 concludes. If $\ell(a, u)$ is not active, then
   $\ell(a, u) = \frac\pi4$; by the first case each $V_i$ and $(A, v)$ have the
   gap property, and step 2 concludes. $\square$

*Lean:
[`Seven.fixed_gap_of_active_cases`](../../SquaresInCircles/Seven/FixedGap.lean#L144),
[`Seven.pairProperty_cap_first`](../../SquaresInCircles/Seven/FixedGap.lean#L112),
[`Seven.pairProperty_cap_second`](../../SquaresInCircles/Seven/FixedGap.lean#L128).*

## B.9 Proof of Proposition 9.17

### Proposition B.32 (active labels)

Let $(a, u)$ and $(A, v)$ be admissible states with active labels, $s, t$ signs
and $k$ an axis. Then the two states with the signs $s, t$ have the gap property
on the axis $k$.

*Proof.* We go through the axes and signs; the cases are the rows of the table
of §B.1. A positive sum gives the gap property by Lemma B.2 (4).

- $k = 0$: Proposition B.26.
- $k = 3$: Proposition B.27.
- $k = 2$, $s = -1$: Proposition B.28.
- $k = 2$, $(s, t) = (1, 1)$: if the target label is side,
  [Proposition C.12](appendix-c.md#proposition-c12-side-target); if it is axial and the source label is
  axial, [Proposition C.6](appendix-c.md#proposition-c6-two-axial-labels); if it is axial and the source label
  is side, [Proposition C.7](appendix-c.md#proposition-c7-side-source-axial-target).
- $k = 2$, $(s, t) = (1, -1)$: ([Theorem C.32](appendix-c.md#theorem-c32-opposite-signs-with-active-labels)).
- $k = 1$, $(s, t) = (1, 1)$: Proposition B.29.
- $k = 1$, $(s, t) = (1, -1)$: ([Proposition D.7](appendix-d.md#proposition-d7-target-sign-negative)), with
  the source sign $1$ and an active target label.
- $k = 1$, $(s, t) = (-1, 1)$: ([Proposition D.16](appendix-d.md#proposition-d16-opposite-signs)).
- $k = 1$, $(s, t) = (-1, -1)$: if the source label is axial,
  [Proposition D.7](appendix-d.md#proposition-d7-target-sign-negative) with the source sign $-1$; if it
  is side, [Proposition D.26](appendix-d.md#proposition-d26-both-signs-negative).

Every active label is axial or side, so the cases are exhaustive. $\square$

*Lean:
[`Seven.fixed_gap_active`](../../SquaresInCircles/Seven/FixedGap.lean#L27).*

*Proof of [Proposition 9.17](seven.md#proposition-917-the-critical-gap).* By Proposition B.32 the hypothesis of
Proposition B.31 holds, so any two admissible states, with any signs, have the
gap property on every axis (Definition B.1): $\sigma_k(\frac\pi3) \ge 0$, and
$\sigma_k(\frac\pi3) = 0$ only if the two states with these signs form a
contact. $\square$
