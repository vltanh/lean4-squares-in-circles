# E-zero deletes every remaining large-transverse negative outer error

## 1. A local comparison with the same A circle

Put
\[
 Q=\frac{9789}{2500},\quad K=\frac{13}{12},\quad
 W(z)=\frac{1+\cos z+\sin z}{2},
\]
\[
 v=\sqrt{Q-1/4}-1,\qquad C_0=\sqrt{Q/2}-\frac12,
\]
\[
 h(z)=\sqrt{Q-[1+\tfrac12\cos z-v\sin z]^2}-\frac12,
 \qquad B(z)=\min\{C_0,h(z)\}.
\tag{1}
\]
The function h is increasing on `[0,7/10]`. It reaches C_0 at
a unique point `z_C` with
\[
 0<z_C<\frac{11}{100}.
\tag{2}
\]
The exact derivative estimates proved in Sections 3--4 of
`HAND_G4_ALIGNED_ZERO_E_ZERO_BRANCH_EXCLUSION.md` give
\[
 h'(z)<\frac{1063}{1000},\qquad
 h''(z)<-\frac{23}{25}
 \quad(0\le z\le11/100).
\tag{3}
\]
That proof uses one whole-interval polynomial comparison and
positive squaring. No numerical extremum or subdivision is used
by the present lemma.

Suppose H and A have nonnegative sorted coordinates, with
\[
 (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q,
 \qquad a_i\ge b_i\ge0,
 \qquad b_A\ge\frac12.
\tag{4}
\]
Let `t,e,epsilon>=0`, with each at most `7/10`, and assume the
negative-core composite and the E-zero cap
\[
\begin{aligned}
 b_H&\ge\frac12+C\cos e+K\sin e,\\
 C&=1-(a_A-\tfrac12)\cos t+(b_A+\tfrac12)\sin t,\\
 b_H&\le B(\epsilon).
\end{aligned}
\tag{5}
\]
The first inequality is exactly the same-G HG0--GA0 necessary
inequality obtained using the true core bound `a_G>=7/12`.
The last follows from the unchanged E-zero EH1 contact and its
same containing circle, as in the cited note.

**Local deletion lemma.** Equations (4)--(5) imply
\[
 \epsilon\ge e,\qquad
 B(\epsilon-e)+a_A\cos t-b_A\sin t\ge1+W(t).
\tag{6}
\]
If e is positive, both comparisons needed for the second
inequality have strict room. The actual A coordinates and their
circle value have not changed. The statement is a comparison of
necessary caps; it need not construct an H center at a new frame.

## 2. The initial H requirement lies strictly above h(0)

Let
\[
 R=\sqrt{Q-1},\qquad H_0=\frac12+C,
 \qquad H_e(r)=\frac12+C\cos r+K\sin r.
\tag{7}
\]
Because `b_A>=1/2`, the A circle gives `a_A<=R-1/2`.
Also `a_A-1/2>=0`, `cos t<=1` and `sin t>=0`. Hence
\[
 C\ge2-R>0,\qquad H_0\ge\frac52-R>h(0).
\tag{8}
\]
For the strict final comparison, `Q<2257/576` gives
`R<41/24`. Consequently
\[
 (3-R)^2-(Q-9/4)=\frac{41}{4}-6R>0,
\]
and both sides compared by positive squaring are positive.

Feasibility in (5), `C_0<9/10`, and `cos e>=3/4` imply
\[
 C\cos e\le C_0-\frac12-K\sin e<\frac25,
 \qquad 0<C<\frac8{15}.
\tag{9}
\]
For every `0<=r<=e`, using `sin r<=13/20` and
`cos r>=3/4`,
\[
 H_e'(r)=K\cos r-C\sin r
 >\frac{13}{12}\frac34-\frac8{15}\frac{13}{20}
 =\frac{559}{1200}>0.
\tag{10}
\]
Thus `H_0<=H_e(r)<=H_e(e)<=C_0` on this interval.
By (2), (8), and the strict increase of h there is a unique
\[
                 z_0\in(0,z_C],\qquad h(z_0)=H_0.
\tag{11}
\]
If e is positive, (10) makes `H_0<C_0`, so `z_0<z_C`.

## 3. One strict curvature comparison deletes e

The assertion is immediate when e is zero. Suppose now `e>0`,
and on `0<=r<=min{e,z_C-z_0}` put
\[
                       J(r)=H_e(r)-h(z_0+r).
\tag{12}
\]
At zero,
\[
 J(0)=0,
 \qquad J'(0)=K-h'(z_0)
 >\frac{13}{12}-\frac{1063}{1000}
 =\frac{61}{3000}>0.
\tag{13}
\]
Throughout this interval, (3), (10), and `H_e(r)<=C_0<9/10`
give
\[
 J''(r)=-(H_e(r)-\tfrac12)-h''(z_0+r)
 >-\frac25+\frac{23}{25}=\frac{13}{25}>0.
\tag{14}
\]
In particular J is strictly positive at every positive r in
its domain.

If `e>=z_C-z_0`, evaluate this comparison at
`r=z_C-z_0>0`. It gives `H_e(r)>h(z_C)=C_0`, contradicting
(10). Therefore
\[
 e<z_C-z_0,
 \qquad H_e(e)>h(z_0+e).
\tag{15}
\]
Since `z_0+e<z_C`, monotonicity and the definition of B show
that `epsilon<=z_0+e` would imply
\[
 B(\epsilon)\le h(z_0+e)<H_e(e),
\]
contrary to (5). Hence
\[
 \epsilon>z_0+e>e,
 \qquad B(\epsilon-e)>h(z_0)=H_0.
\tag{16}
\]
Finally, by the definition of C,
\[
 H_0+a_A\cos t-b_A\sin t
 =\frac32+\frac12\cos t+\frac12\sin t=1+W(t).
\]
This proves (6), including its strict version when e is positive.

## 4. A complete E-zero exclusion with either or both negative outer errors

The local lemma joins the previously proved small-transverse
transport without any choice of a privileged side.
Retain the original normal H/A/B/D signs and all their actual
sorted circles at `q<=Q`, and let E have zero transverse
coordinate. Assume AB is aligned with
\[
                         b_A+b_B\ge1.
\tag{17}
\]
Let the nonnegative outer/hard angles be
\[
 t,u,e_H,e_D,\delta,\epsilon\ge0,
 \qquad t+u+e_H+e_D=\delta+\epsilon\le\frac7{10}.
\tag{18}
\]
The H-side path is either aligned (`e_H=0`) or retains the
negative noncanceling HG0/GA0 necessary composite (5), with
`e=e_H`. The D-side path has the reflected counterpart with
`A,H,t,e_H` replaced by `B,D,u,e_D`. Thus
\[
\begin{aligned}
 b_H&\ge\frac12+C_A\cos e_H+K\sin e_H,\\
 b_D&\ge\frac12+C_B\cos e_D+K\sin e_D,\\
 C_A&=1-(a_A-\tfrac12)\cos t+(b_A+\tfrac12)\sin t,\\
 C_B&=1-(a_B-\tfrac12)\cos u+(b_B+\tfrac12)\sin u.
\end{aligned}
\tag{19}
\]
The unchanged E-zero mixed contacts give
\[
                      b_H\le B(\epsilon),\qquad
                      b_D\le B(\delta).
\tag{20}
\]

On the H side there are two choices, determined by its actual
middle tangent.

* If `b_A<=1/2`, the small-transverse theorem in
  `HAND_G4_NEGATIVE_NONCANCELING_ZERO_CORE_TRANSPORT.md`
  absorbs `e_H` into the quarter tilt, giving the aligned
  comparison with `tau=t+e_H` and unchanged E angle epsilon.
  It retains the same H and A coordinates. At positive error
  its composite slack exceeds `e_H/150`.
* If `b_A>=1/2`, the local lemma instead deletes `e_H` from the
  E angle, giving the aligned cap comparison with `tau=t` and
  `epsilon'=epsilon-e_H>=0`. Again A's coordinates are unchanged.

At equality of the tangent threshold either valid choice may be
used. Apply the identical reflected alternatives on the D side,
absorbing its error into u when `b_B<=1/2`, or deleting it from
delta when `b_B>=1/2`.

Write `tau,upsilon` for the resulting two quarter tilts and
`epsilon',delta'` for the resulting E angles. In each choice,
the amount deleted from its E angle is exactly the amount not
absorbed into its quarter tilt. Consequently
\[
 \tau,\upsilon,\epsilon',\delta'\ge0,\qquad
 \tau+\upsilon=\epsilon'+\delta'\le\frac7{10}.
\tag{21}
\]
The same original A and B circles and coordinates satisfy
\[
\begin{aligned}
 B(\epsilon')+a_A\cos\tau-b_A\sin\tau&\ge1+W(\tau),\\
 a_B\cos\upsilon-b_B\sin\upsilon+B(\delta')&\ge1+W(\upsilon),\\
 b_A+b_B&\ge1.
\end{aligned}
\tag{22}
\]

These are exactly the necessary cap inequalities already
excluded by Sections 2--6 of
`HAND_G5_E_ZERO_HARD_QUARTER_SPLIT_EXCLUSION.md`. More explicitly,
put
\[
 \mathcal L(z,b)=\cos z\sqrt{Q-(3/2-b+\cos z)^2}
       -\sin z\,(3/2-b+\cos z).
\]
The same A and B circles in (22) give
\[
 2\le\mathcal L(\tau,B(\epsilon'))
            +\mathcal L(\upsilon,B(\delta'))
 <2-\frac{149}{625000},
\tag{23}
\]
the required contradiction. The quoted continuous cap theorem
allows all weak constraints, both zero-angle boundaries, and
arbitrary radial slack.

This closes the whole E-zero boundary (17)--(20), with either or
both negative noncanceling outer errors. Canceling negative owners
may first use their stronger same-anchor transport in
`HAND_G4_SIGNED_THREE_ZERO_REDUCTION_FOR_CANCELING_OUTER_OWNERS.md`
and then enter as aligned sides. The local proof and (23) also
retain any earlier strict A/B circle loss, because A and B were
never replaced in this argument.

Reflection presents no E-sign issue here: a zero transverse E
coordinate remains zero. The separate nonzero-E DE- and EH-aligned
boundaries, positive noncanceling outer errors opposite a remaining
negative error, AB alignment before (17), and global owner/frame
capture are not asserted by this theorem.
