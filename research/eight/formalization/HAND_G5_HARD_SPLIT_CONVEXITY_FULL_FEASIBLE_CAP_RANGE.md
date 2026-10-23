# Convex splitting on the full feasible hard-quarter cap range

## 1. A scalar lemma uniform in the actual radius

Put `Q=9789/2500`. Let q and D satisfy

\[
 0<q\le Q,\qquad D\ge\frac35,
 \qquad q\ge(D+1)^2+\frac14.
\tag{1}
\]

In particular `D<183/200<19/20`. For `0<=theta<=7/10`, write

\[
 c=\cos\theta,\quad s=\sin\theta,\quad C=D+c,
 \quad w=\sqrt{q-C^2},
\]
\[
 L=cw-sC,\qquad X=cC+sw,\qquad k=w-s.
\tag{2}
\]

**Scalar theorem.** The cap L is well defined, strictly decreasing,
and strictly convex on the entire interval `[0,7/10]`. No assumption
that L stays positive is needed. The statement uses the actual q;
there is no substitution of Q for q in the cap.

First, (1) gives

\[
 w^2\ge q-(D+1)^2\ge\frac14,
 \qquad
 w^2-s^2\ge q-(D+1)^2\ge\frac14.
\tag{3}
\]

Thus `w>0`, `k>0`, `C>0`, and `X>0`. Direct differentiation gives

\[
 w'=Cs/w,\qquad k'=-L/w,
 \qquad X'=Lk/w,\qquad L'=-Xk/w<0.
\tag{4}
\]

Two exactly equivalent forms of its second derivative are

\[
 L''=\frac{Lw(X-k^2)+XkCs}{w^3}
     =\frac{X(cw^2-Cs^2)-Lwk^2}{w^3}.
\tag{5}
\]

We verify the two positive factors needed to use these formulas.

### The factor `X-k^2` is uniformly positive

The exact identity is

\[
 X-k^2=D^2+3D+2-q
            +3s\left(w-s-\frac{Ds}{1+c}\right).
\tag{6}
\]

The bracket is positive. In fact

\[
\begin{split}
 w^2-\left(\frac{s(C+1)}{1+c}\right)^2
 &=\frac{q-2D(D+1)-1+c(q-2D-1)}{1+c}\\
 &\ge\frac14-D^2\frac{1-c}{1+c}
 \ge\frac14-\frac{(19/20)^2}{7}
 =\frac{339}{2800}>0.
\end{split}
\tag{7}
\]

Here `c>=3/4`, and the first inequality uses the feasible-cap lower
bound in (1). Since `s(C+1)/(1+c)=s+Ds/(1+c)`, positive
squaring proves the claim about the bracket. Equations (1),(6) then
give

\[
 X-k^2\ge\left(\frac35\right)^2
          +3\left(\frac35\right)+2-Q
          =\frac{611}{2500}>0.
\tag{8}
\]

### The factor `cw^2-Cs^2` is uniformly positive

Another exact identity, followed by (1), is

\[
\begin{split}
 cw^2-Cs^2
 &=c(q-D^2-1)-D(1+c^2)\\
 &\ge\frac c4-D(1-c)^2
 \ge\frac3{16}-\frac{19}{20}\frac1{16}
 =\frac{41}{320}>0.
\end{split}
\tag{9}
\]

If `L>0`, the first formula in (5), with (8), is strictly positive.
If `L<=0`, the second formula, with (9), is strictly positive.
This proves the scalar theorem on the whole interval.

The sign split in this last paragraph is an algebraic argument on
one continuous cap. It is not an angular subdivision or a sampled
verification.

## 2. Actual hard-quarter paths satisfy the scalar hypotheses

Consider the original signs

\[
 (y_H,y_G,y_A,y_B,y_T,y_D)
 =(b_H,-b_G,b_A,-b_B,b_T,-b_D),\qquad b_i\ge0,
\]

the original own-frame sorting `a_i>=b_i`, and their corner bounds

\[
 (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q.
\tag{10}
\]

For A and B, retain separate ceilings

\[
 (a_A+1/2)^2+(b_A+1/2)^2\le q_A\le q,\qquad
 (a_B+1/2)^2+(b_B+1/2)^2\le q_B\le q.
\tag{10a}
\]

One may take each ceiling to be that point's actual squared corner
value. In particular a strict A or B loss below the common radius q
is retained in its own ceiling, rather than erased by enlarging it
to q.

Assume all three zero edges are aligned. Retain either original
transverse witness on HG, AB, TD, original GA axis 0, and original
BT axis 2. Let

\[
 \theta_H=\theta_G=t,\quad\theta_A=\theta_B=0,
 \quad\theta_T=\theta_D=-u,
 \qquad t,u\ge0,\quad\alpha=t+u\le7/10.
\tag{11}
\]

Keep the actual E center, its frame, and its two original neighboring
constraints fixed. They need no special boundary condition for the
split argument.

Use the unchanged actual G and T transverse coordinates:

\[
 D_A=b_G+\frac12,\qquad D_B=b_T+\frac12.
\tag{12}
\]

Since `b_H,b_D<.9`, the zero edges give `b_G,b_T>.1`, and
therefore `D_A,D_B>3/5`. The two original quarter projections are

\[
 a_A\cos t-b_A\sin t\ge W(t)+b_G,
 \qquad a_B\cos u-b_B\sin u\ge W(u)+b_T,
\]
\[
 W(z)=\frac{1+\cos z+\sin z}{2}.
\tag{13}
\]

They imply `a_A>=1+b_G` and `a_B>=1+b_T`. The original circles
thus give the remaining scalar hypotheses:

\[
 q_A\ge(D_A+1)^2+\frac14,
 \qquad q_B\ge(D_B+1)^2+\frac14.
\tag{14}
\]

Let `L_A,L_B` be (2) with the respective parameters
`(q_A,D_A)` and `(q_B,D_B)`. The original
quarter witnesses and circle caps give

\[
 Z_A:=b_A+\frac12\le L_A(t),\qquad
 Z_B:=b_B+\frac12\le L_B(u).
\tag{15}
\]

The original AB witness gives `Z_A+Z_B>=2`. Consequently

\[
                    L_A(t)+L_B(u)\ge2.
\tag{16}
\]

Replacing the actual parameters in (12) by `1.5-b_H` and
`1.5-b_D` gives the weaker H/D-endpoint version of this necessary
inequality. Keeping (12) is stronger and will preserve G and T
as well as H and D in the construction below.

## 3. One endpoint split has at least as much cap room

For fixed `q_A,q_B,D_A,D_B` and the fixed total span alpha,
define

\[
 \Psi(v)=L_A(v)+L_B(\alpha-v),\qquad 0\le v\le\alpha.
\]

The scalar theorem gives `Psi''>0`. Equations (11),(16) therefore
imply

\[
 2\le\Psi(t)\le
 \max\{L_A(0)+L_B(\alpha),\ L_A(\alpha)+L_B(0)\}.
\tag{17}
\]

If `t,u>0`, the last inequality is strict. This is the full
feasible-cap extension of the E-zero split lemma: arbitrary actual
E data and the entire feasible transverse range are allowed.

Choose a maximizing endpoint and denote its two tilts by

\[
 (t',u')=(0,\alpha)\quad\hbox{or}\quad(\alpha,0).
\tag{18}
\]

No original vertex was changed to prove (17).

## 4. The endpoint construction preserves five original vertices

The comparison has a concrete realization in the stated necessary
edge system. Keep the original H, G, T, D and E centers and frames.
Put the new common A/B frame at G's frame for `(0,alpha)`, or at
T's frame for `(alpha,0)`. Give A and B the own-frame corner vectors

\[
 (X_A(t'),L_A(t')),\qquad (X_B(u'),L_B(u')).
\tag{19}
\]

The squared corner values are exactly `q_A` and `q_B`, respectively.
Thus each remains at or below the common actual radius q, and any
strict loss already present in one ceiling is preserved. Each cap is less
than `233/200=1.165`, since

\[
 L_i(v)\le L_i(0)
 =\sqrt{q_i-(D_i+1)^2}
 \le\sqrt{Q-(8/5)^2}<233/200.
\]

Their sum is at least two by (17). Thus each cap exceeds
`167/200=.835`, and each new transverse magnitude exceeds `.335`.
The contact identity

\[
 (X_i-1)\cos v-L_i\sin v=D_i
\]

gives `X_i>=D_i+1>1.6`, so the new primaries exceed `1.1` and
sorting is strict. In particular the primary threshold `7/12` is
strictly satisfied. The new GA0 and BT2 constraints in (13) are
equalities with the unchanged original G and T centers. The aligned
AB constraint holds by (17), and both original transverse AB
witnesses are available.

HG, TD, DE and EH are unchanged. Therefore every corner, sorting,
sign, frame and original neighboring-SAT condition explicitly stated
in Sections 2--4 is preserved. In particular H, D, E, their two
mixed contacts and the total H-to-D frame span are all unchanged.

If the original split is interior (`t,u>0`), (17) leaves strict AB
slack. By continuity, the same construction can then use corner
values `q_A-eta` and `q_B-eta` for some `eta>0`, while all five
other centers remain fixed. Every endpoint cap exceeds `.835`,
so its feasible-cap lower bound has a strict margin; both radicands
and the scalar hypotheses persist under a sufficiently small common
decrease. Strict signs, sorting and the hard contacts persist as
well. Thus an interior split creates a strict loss at both anchors,
and every split preserves any strict loss inherited in either
separate ceiling.

## 5. The same theorem needs only the five-anchor composite system

G and T need not exist for the weaker endpoint formulation. Instead,
keep only H, A, B, D and E, their nonnegative own-frame coordinates,
the sorting and circle assumptions (10)--(10a), and the frames

\[
 \theta_H=t,\quad\theta_A=\theta_B=0,\quad\theta_D=-u,
 \qquad t,u\ge0,\quad t+u=\alpha\le7/10.
\tag{20}
\]

Retain E and its two mixed inequalities with H and D without
alteration. Assume the composite hard inequalities

\[
\begin{split}
 b_H+a_A\cos t-b_A\sin t&\ge1+W(t),\\
 a_B\cos u-b_B\sin u+b_D&\ge1+W(u),\\
 b_A+b_B&\ge1.
\end{split}
\tag{21}
\]

These are exactly the necessary five-anchor inequalities obtained
by adding HG to GA and BT to TD at aligned outer zero edges and
then eliminating the two shared transverse coordinates. This
corollary assumes (21) directly and makes no assertion that omitted
G or T centers can be reconstructed.

Set

\[
 D_A=\frac32-b_H,\qquad D_B=\frac32-b_D.
\tag{22}
\]

The sorted H and D circles give `b_H,b_D<.9`, hence `D_A,D_B>.6`.
Since `W>=1` and the coordinates are nonnegative, (21) gives
`a_A>=2-b_H=D_A+1/2` and `a_B>=2-b_D=D_B+1/2`. Consequently

\[
 (D_A+1)^2+\tfrac14\le q_A\le Q,\qquad
 (D_B+1)^2+\tfrac14\le q_B\le Q.
\tag{23}
\]

In particular `D_A,D_B<.915`. Equations (21), in corner
coordinates, are precisely

\[
 (X_A-1)\cos t-Z_A\sin t\ge D_A,\qquad
 (X_B-1)\cos u-Z_B\sin u\ge D_B,
 \qquad Z_A+Z_B\ge2.
\tag{24}
\]

Thus (15)--(19) and all of Sections 3--4 apply verbatim with
the separate cap parameters `(q_A,D_A)` and `(q_B,D_B)`.
At the chosen endpoint put A and B at the common H frame or the
common D frame, leaving H, D, E and all their coordinates and frames
fixed. The two composite hard inequalities become equalities,
the AB sum holds, and the new A/B coordinates are strictly sorted
with primaries above `1.1` and tangents between `.335` and `.665`.
Their squared corner values remain `q_A,q_B`, or can both be
decreased strictly when the original split is interior.

This proves the full endpoint-split theorem, including preservation
of any inherited strict A/B corner loss, directly for the five-anchor
necessary system (21).

## 6. Dependency and mismatch boundary

This is a radius-preserving endpoint construction in the specified
necessary edge system. It is not an assertion that arbitrary
candidate cycles have these owners, signs or zero alignments. Any
additional nonneighbor packing or physical-order hypotheses of a
downstream theorem must be verified separately.

If the retained E frame is `theta_E=-u+delta`, with
`delta,epsilon>=0` and `delta+epsilon=alpha`, both delta and epsilon
are unchanged in the construction because H, D and E frames are
fixed. The forward mismatch changes from `u+delta` to
`alpha+delta` or `delta`. Thus a retained bad-mismatch condition
cannot be dropped silently. For a radius lower bound, one may use a
descendant without the original bad-mismatch restriction when the
downstream theorem applies to the preserved edge system.

No table, numerical minimizer, contact assumption on an original
center, or fixed-ceiling substitution is a premise of the proof.
