# E's frame order follows by descent once the non-E chain is aligned and ordered

## 1. The five-anchor statement

Put `Q=9789/2500`. Let H, A, B, D and E have nonnegative
sorted own-frame magnitudes with
\[
 a_i\ge b_i\ge0,\qquad
 (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q.
\tag{1}
\]
The normal signed tangents are positive at H,A and negative at
B,D,E. Suppose the non-E chain is already aligned at its three
zero edges. Its remaining necessary inequalities are
\[
\begin{aligned}
 b_H+a_A\cos t-b_A\sin t&\ge1+W(t),\\
 b_A+b_B&\ge1,\\
 a_B\cos u-b_B\sin u+b_D&\ge1+W(u),
\end{aligned}
\tag{2}
\]
where
\[
 t,u\ge0,\qquad\alpha=t+u\le7/10,
 \qquad W(z)=\frac{1+\cos z+\sin z}{2}\quad(z\ge0).
\tag{3}
\]
Thus the common A/B frame lies between D and H. Set D's
frame to zero and H's to alpha. E's frame is an arbitrary real
number delta; put `epsilon=alpha-delta`. Assume only that the
whole real-frame spread is at most `7/10`, equivalently here
\[
                    \alpha-7/10\le\delta\le7/10.
\tag{4}
\]
The actual original DE3 and EH1 formulas are
\[
\begin{aligned}
 a_D+a_E\sin\delta+b_E\cos\delta&\ge\widehat W(\delta),\\
 a_H+a_E\sin\epsilon-b_E\cos\epsilon&\ge\widehat W(\epsilon),
 \qquad\widehat W(z)=\frac{1+\cos z+|\sin z|}{2}.
\end{aligned}
\tag{5}
\]
No E-frame order is an input.

**E-order reduction.** The case `delta>alpha` is impossible.
If `delta<0`, there is an E-only descendant with `delta'=0`
and a strictly smaller E corner value, keeping H,A,B,D and
their frames and actual corner values unchanged. Every such
five-anchor system has `q>=q_*`. At equality E was already
between D and H, and the original five anchors have the
canonical stationary values from
`HAND_G5_ALIGNED_HARD_CLASS_SHARP_REDUCTION.md`.

This removes E's order from the aligned and ordered non-E
class. It does not yet align three arbitrary original zero
edges or put an arbitrary A/B frame between D and H.

## 2. The shared non-E chain and the zero-span case

The bounds derived from (2) in Sections 2--3 of
`HAND_G4_E_INTERIOR_BOUNDARY_REDUCTION.md` do not use an E
sign or frame. They give
\[
 \alpha<11/50,\qquad
 a_H+a_D<1.9968-.718\sin\alpha<2,
 \qquad a_H,a_D>1/2,
\tag{6}
\]
as well as `b_i<9/10` from the sorted circles.

If alpha is zero, then epsilon is minus delta. Adding (5)
cancels both E coordinates and gives
\[
                    a_H+a_D\ge2\widehat W(\delta)\ge2,
\]
contradicting (6). Hence
\[
                            0<\alpha<11/50.
\tag{7}
\]

## 3. Every feasible E outside the frame interval has primary greater than one

Suppose delta is outside `[0,alpha]`, and put
\[
 \omega=\alpha/2,\qquad
 \zeta=|\delta-\epsilon|/2,\qquad
 c=\cos\omega,\quad s=\sin\omega,
 \quad m=\cos\zeta+\sin\zeta.
\tag{8}
\]
Equations (4), (7) give
`0<omega<.11`, `omega<zeta<.7<pi/4`, and therefore
`m>=c+s`. Adding the two actual mixed constraints (5),
\[
 \widehat W(\delta)+\widehat W(\epsilon)=1+cm,
 \qquad \sin\delta+\sin\epsilon=2s\cos\zeta.
\]
Also `|cos delta-cos epsilon|=2s sin zeta`.
Since `0<=b_E<=a_E`, (5)--(6) imply
\[
                         2s a_E m>cm-1+1.436sc.
\tag{9}
\]
The coefficient `1.436sc-1` is negative. Increasing m above
`c+s` therefore increases the lower bound obtained from (9):
\[
 a_E>
 \frac{c}{2s}+\frac{1.436sc-1}{2sm}
 \ge\frac{1.218c-.5s}{c+s}.
\tag{10}
\]
Using `c>.99`, `s<.11` and `c+s<1.11`,
\[
                  a_E>\frac{1.15082}{1.11}>1.
\tag{11}
\]
The final numerator reserve is `.04082>0`. The same estimate
holds at either angle endpoint by continuity, if it is feasible.

In particular every feasible outside E has `a_E>b_E`, since
`b_E<.9`. No diagonal, primary-zero or true-core boundary can
obstruct a sufficiently small local descent. We may omit the
core condition while minimizing E: (11) supplies it strictly
on every outside portion of the necessary relaxation.

## 4. Two exact derivative identities outside the interval

Fix H and D and write the E corner coordinates
\[
 X=a_E+\frac12,\qquad Y=b_E+\frac12,
 \qquad d_0=a_D-\frac12,\quad h_0=a_H-\frac12.
\tag{12}
\]
When both mixed contacts are equalities, they determine X,Y
smoothly as functions of delta on either outside sign branch.
Their coefficient determinant is `-sin(alpha)`, which is
nonzero by (7). Put
\[
 A=X\cos\epsilon+Y\sin\epsilon,
 \qquad B=X\cos\delta-Y\sin\delta.
\tag{13}
\]
Both A and B are positive: `X>Y>0`, and every relevant
angle has magnitude less than `pi/4`.

### E below D

For `delta<0<epsilon`, the equalities in corner coordinates are
\[
 X\sin\delta+Y\cos\delta=\cos\delta-d_0,
 \qquad X\sin\epsilon-Y\cos\epsilon=\sin\epsilon-h_0.
\tag{14}
\]
Differentiating with respect to delta, with `epsilon'= -1`,
gives
\[
 X'\sin\delta+Y'\cos\delta=-B-\sin\delta,
 \quad X'\sin\epsilon-Y'\cos\epsilon=A-\cos\epsilon.
\]
The vector `(X,Y)` is the positive linear combination of the
two coefficient rows with weights `A/sin(alpha)` and
`B/sin(alpha)`. Consequently, for `q_E=X^2+Y^2`,
\[
 \frac{q_E'}2
 =-\frac{A\sin\delta+B\cos\epsilon}{\sin\alpha}<0.
\tag{15}
\]
The numerator is positive because it equals
\[
 X\cos\epsilon(\cos\delta+\sin\delta)
       +Y\sin\delta(\sin\epsilon-\cos\epsilon)>0.
\]
Here `cos delta+sin delta>0`, while the two factors in the
last product are both negative. Thus increasing delta toward
D strictly decreases the corner value along this contact curve.

### E above H

For `delta>alpha>0>epsilon`, the exact contact equations are
\[
 X\sin\delta+Y\cos\delta
       =\sin\delta+\cos\delta-d_0,
 \qquad X\sin\epsilon-Y\cos\epsilon=-h_0.
\tag{16}
\]
Differentiation gives the right sides
`-B+cos(delta)-sin(delta)` and A. The same positive
combination therefore gives
\[
 \frac{q_E'}2
       =\frac{A(\cos\delta-\sin\delta)}{\sin\alpha}>0.
\tag{17}
\]
Solving those two differentiated equations also gives
\[
 Y'=-X+
       \frac{(\cos\delta-\sin\delta)\sin\epsilon}{\sin\alpha}
       <-X<0.
\tag{18}
\]
Hence decreasing delta toward H strictly decreases the corner
and strictly increases b_E. In particular this inward variation
is available even when `b_E=0` initially.

## 5. No feasible E lies above H

Suppose `delta_0>alpha` is feasible. Among all E states
satisfying (1), (5) with the unchanged non-E data and
\[
                        \alpha\le\delta\le\delta_0,
\tag{19}
\]
minimize q_E. This is a nonempty compact relaxation. Every
outside feasible state has the strict coordinate margins in
(11), and moving delta inward stays within the original
frame-spread interval.

A minimizer with `delta>alpha` must have both contacts active.
If only DE is active, the direction
`(da_E,db_E)=(-cos(delta),sin(delta))` preserves it and
strictly lowers the corner, because X>Y and cos(delta)>sin(delta).
It is allowed also at b_E zero. If only EH is active, decreasing
a_E improves EH since sin(epsilon)<0 and lowers the corner;
the slack DE constraint persists for a small step. If both
contacts have slack, decrease a_E. Thus each alternative to
two active contacts contradicts minimality.

For two active contacts, (17)--(18) give an inward decrease
of delta with smaller corner and nonnegative tangent, including
at b_E zero. Sorting and the primary condition remain strict.
This also contradicts minimality. Therefore every minimizer
in (19) has `delta=alpha`, or `epsilon=0`.

But `HAND_G5_ALIGNED_HARD_EPSILON_ZERO_EXCLUSION.md`
excludes exactly that endpoint when joined to the unchanged
ordered non-E chain (2), already at Q. This contradiction
proves that no E above H is feasible.

## 6. A transverse-zero E cannot lie below D

Suppose `b_E=0` and `delta<0`. Reflect the whole five-anchor
necessary system and relabel
\[
                  (H',A',B',D')=(D,B,A,H).
\tag{20}
\]
The hard tilts interchange, `t'=u,u'=t`, so (2)--(3) retain
their form. The E transverse sign changes under this reflection,
but is still zero. Its new angle split is
\[
                    \delta'=\epsilon>\alpha,
                    \epsilon'=\delta<0.
\]
Both original mixed equations, all circle values and the frame
spread retain exactly the form (1)--(5). The reflected E lies
above H', contrary to Section 5. Thus this boundary is excluded.

The use of reflection here is confined to `b_E=0`. No sign
claim about a nonzero reflected E tangent is required.

## 7. Every E below D descends strictly to D

Now let an arbitrary `delta_0<0` be feasible, and minimize q_E
over the necessary E relaxation with
\[
                         \delta_0\le\delta\le0,
\tag{21}
\]
keeping the four non-E anchors fixed. The minimum exists by
compactness and is at most the actual original E corner.

If a minimizer has delta negative, Section 6 gives `b_E>0`
and (11) gives all other coordinate margins. If only EH is
active, decrease b_E; EH improves and the slack DE contact
persists. If only DE is active, decrease a_E; sin(delta)<0,
so DE improves. If neither is active, decrease a_E. Thus both
contacts must be equalities.

At two active contacts, (15) gives a smaller corner by increasing
delta a little. The positive b_E and strict sorting margins
make this a valid local variation, even if the angle starts at
the lower endpoint delta_0. This contradiction proves that
every minimizer in (21) has `delta=0`.

The input delta_0 was negative and hence could not itself have
been a minimizer. Its corner decreases strictly. H,A,B,D,
their actual corner values and all three inequalities (2)
remain unchanged. This is the required E-only descent.

## 8. Sharpness and original equality

If E was inside `[D,H]`, apply
`HAND_G5_ALIGNED_HARD_CLASS_SHARP_REDUCTION.md` directly.
If E was below D, Section 7 produces exactly that theorem's
input at `delta=0`, at the same q and with a strict E-circle
loss. E above H has already been excluded. These alternatives
prove `q>=q_*` on the full class (1)--(5).

At `q=q_*`, the strict E loss from Section 7 is impossible:
the aligned sharp theorem keeps E fixed through its remaining
split comparison and has a positive mass on the actual E
circle in its final identity. Thus the original E was already
in `[D,H]`. Reapply the aligned theorem to the original five
anchors. It fixes the canonical hard and E splits and their
stationary corner vectors, including original `delta=0`.

All preceding reductions retain any separate strict loss in
an A/B circle. No omitted intermediate, nonneighbor constraint,
physical angular gap or mismatch bound is invoked. This is an
analytic removal of E's frame-order hypothesis within the
stated non-E class; the remaining global frame-order steps
remain distinct.
