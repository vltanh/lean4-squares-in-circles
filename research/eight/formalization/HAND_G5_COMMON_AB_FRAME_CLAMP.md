# A common A/B frame outside D--H moves to an endpoint with strict circle loss

## 1. The precise remaining order assumption

Put `Q=9789/2500` and `q_L=19577/5000`. Suppose all three
zero edges are aligned, and H,A,B,D have nonnegative sorted
own-frame magnitudes with corner ceilings at most q<=Q. Their
necessary hard-chain inequalities are
\[
\begin{aligned}
 b_H+a_A\cos t-b_A\sin t&\ge1+\widehat W(t),\\
 b_A+b_B&\ge1,\\
 a_B\cos u-b_B\sin u+b_D&\ge1+\widehat W(u),
 \qquad\widehat W(z)=\frac{1+\cos z+|\sin z|}{2}.
\end{aligned}
\tag{1}
\]
Here t=theta_H-rho and u=rho-theta_D, where rho is the
common A/B frame. Assume only
\[
                 \alpha=t+u=\theta_H-\theta_D>0
\tag{2}
\]
and a real-frame spread at most `7/10`. Neither t nor u is
assumed nonnegative.

**Common-frame clamp.** If rho is outside `[theta_D,theta_H]`,
the necessary chain has a descendant with common frame at
the nearer endpoint and both middle corner values strictly
less than q. It keeps H,D, every E coordinate and frame,
and all constraints not involving A/B unchanged. New middle
coordinates are nonnegative, sorted and satisfy the true core.
The new AB transverse sum is one.

For a sharp lower-bound argument a q below q_L may first be
enlarged to q_L without moving its input centers. The construction
below then uses this working q in `[q_L,Q]`; since q_L<q_*,
the resulting sharp conclusion also excludes the smaller
original ceiling. At q=q_* no enlargement occurs.

## 2. Positive and negative quarter caps

Write
\[
 D_H=\frac32-b_H,\qquad D_D=\frac32-b_D.
\tag{3}
\]
The sorted circles give b_H,b_D<.9, so both parameters exceed
`.6`. Feasibility also gives
\[
                            D_H,D_D<.915.
\tag{4}
\]
For a positive quarter angle z, its inequality gives
`D<=(a-1/2)cos z-(b+1/2)sin z<=a-1/2<.915`.
For a negative angle -z it gives
\[
                    D\le(a-\tfrac12)\cos z
                                   +(b-\tfrac12)\sin z.
\tag{5}
\]
If b<=1/2 the same upper bound .915 follows. If b>1/2, the
circle gives `a<1.20752`, while b<.9. Thus the right side of
(5) is at most the norm of `(a-1/2,b-1/2)`, less than
\[
                \sqrt{(.708)^2+(.4)^2}<.814<.915.
\]
These positive-square comparisons establish (4) without
assuming the quarter angle's sign.

At the actual working q define the positive-quarter cap
\[
 L(z,D)=\cos z\sqrt{q-(D+\cos z)^2}
                       -\sin z(D+\cos z).
\tag{6}
\]
The cap and derivative results in Section 4 of
`HAND_G4_SIGNED_THREE_ZERO_REDUCTION_FOR_CANCELING_OUTER_OWNERS.md`
apply on the wider interval `.434<D<.915`, hence here. Its
radicand is positive, L decreases on `[0,.7]`, and
\[
                        -L_z(z,D)>9/8\quad\text{if }L\ge1/2.
\tag{7}
\]

For a negative quarter angle -z put
\[
 C=D+\cos z+\sin z,\quad w=\sqrt{q-C^2},
 \quad M(z,D)=C\sin z+w\cos z.
\tag{8}
\]
Its corner inequality is `X cos z+Y sin z>=C`, with
`X=a+1/2`, `Y=b+1/2`. Rotating that same corner disk shows
that `Y<=M(z,D)` whenever the cap is feasible. In particular
its radicand is nonnegative. No extra circle at an unrelated
anchor has entered this comparison.

Indeed `C>1.6>sqrt(q) sin z`, since `sqrt(q)<2` and
`sin z<=.65`. Thus the unconstrained top point of the circle
is outside this cap; its maximum transverse coordinate is
the upper intersection in (8).

## 3. The negative cap grows slower than the positive cap decays

For a real negative cap with w>0 put
\[
 c=\cos z,\quad s=\sin z,\quad d=c-s,
 \quad X=Cc-ws.
\]
Direct differentiation of (8) gives
\[
                  M_z=X\left(1-\frac d w\right),
                  \qquad X^2+M^2=q.
\tag{9}
\]
On `0<=z<=.7`, one has c>=3/4, s<=13/20, and d>0.
Also C>8/5 and
\[
 w<\frac{233}{200}=1.165,\qquad 0<X<2.
\tag{10}
\]
The root bound follows from `Q-(8/5)^2<(233/200)^2`.
For positivity of X, use
`X>(8/5)(3/4)-(233/200)(13/20)>0`; its upper bound follows
from q<=Q<4.

If w<=d, (9) is nonpositive. Otherwise
\[
 0<w^2-d^2=q-D^2-2D(c+s)-2.
\]
Since D>3/5 and q<=Q,
\[
 c+s<\frac{Q-(3/5)^2-2}{2(3/5)}<\frac{13}{10}.
\]
Consequently
\[
 d^2=2-(c+s)^2>\frac{31}{100}
                            >\left(\frac{11}{20}\right)^2.
\]
Using (9)--(10) now gives the uniform derivative bound
\[
 M_z<2\left(1-\frac{11/20}{233/200}\right)
         =\frac{246}{233}<\frac98,
 \qquad \frac98-\frac{246}{233}=\frac{129}{1864}>0.
\tag{11}
\]
It also covers the preceding w<=d case. If a cap ends at w=0,
the integrated comparison extends to it by continuity.

## 4. Clamp a common frame above H

Suppose rho>theta_H and set `r=rho-theta_H>0`. Then
`t=-r`, `u=alpha+r`, and both angles have magnitude at most
`.7`. The original two corners and AB imply
\[
                  2\le M(r,D_H)+L(\alpha+r,D_D).
\tag{12}
\]
On the whole interval `0<=z<=r`, the negative cap is real:
its C increases with z, so its radicand is no smaller than
at the original feasible endpoint. The other cap is at least
its original value, hence at least 1/2, because L decreases.

Apply (7), (11) to
`S(z)=M(z,D_H)+L(alpha+z,D_D)`. Integration, including any
radicand-zero endpoint by continuity, gives
\[
\begin{aligned}
 L(0,D_H)+L(\alpha,D_D)
       &=S(0)\\
       &\ge S(r)+\frac{129}{1864}r
        \ge2+\frac{129}{1864}r>2.
\end{aligned}
\tag{13}
\]

Each endpoint cap is less than 1.165: the positive cap
decreases from `sqrt(q-(D+1)^2)<1.165`. Thus (13) puts
each cap strictly above .835. Choose two transverse corners
Y_A,Y_B strictly below their respective endpoint caps, with
\[
                             Y_A+Y_B=2.
\tag{14}
\]
They can be chosen in `(.835,1.165)`. Put the common A/B
frame at H. First choose their primary corners on the actual
q-circle. Their endpoint hard caps have strict slack because
the required transverse corners are strictly below the cap
frontiers. At a cap frontier, its identity
`(X-1)cos z-Y sin z=D` gives `X>=1+D>1.6`; lowering Y
on the same circle increases X. Hence both new points are
strictly sorted and have primary greater than 1.1.

Decrease each middle primary a sufficiently small positive
amount. The two strict hard-cap gaps absorb these decreases;
AB depends only on (14). Sorting, positivity and the true
core remain strict. Both middle corner values are now strictly
less than q, and `b_A+b_B=1`. All other anchors are unchanged.

For a common frame below D, apply the identical cap argument
with H,A and D,B interchanged and the frame direction reversed.
This argument changes only the middle data. E is neither
reflected nor re-signed by the resulting construction.

## 5. Consequence with arbitrary E order and original equality

Retain, in addition to (1)--(2), an E with the normal signed
tangent, sorted circle and the actual signed-width DE3/EH1
inequalities. Its frame may be anywhere in the original
span of length at most `.7`.

If the common A/B frame was already between D and H, leave
the middle anchors unchanged. Otherwise the clamp above
moves that frame to D or H and gives two strict middle-circle
losses. The new frame lies inside the old full frame span,
so the spread condition remains valid. H,D,E are unchanged.

Now `HAND_G5_E_ORDER_FROM_ALIGNED_NON_E_CHAIN.md` applies.
It removes E's order restriction, retaining all middle-circle
losses, and proves `q>=q_*`. At equality neither middle frame
clamp nor a below-D E descent is possible, because their
strict circle losses survive to five positive masses in the
aligned sharp identity. E above H is excluded outright.
Thus the original common A/B frame and E frame were already
ordered, and the original aligned sharp theorem fixes the
stationary five anchors.

This proves sharpness and original-anchor equality for the
entire aligned-three-zero class with `theta_H>theta_D`,
without any A/B or E placement assumption.
`HAND_G5_POSITIVE_HD_SPAN_WITH_ALIGNED_ZEROS.md` excludes the
reverse and zero H/D span directly from the same aligned
constraints, so the combined result needs no frame-order
hypothesis. Alignment of arbitrary original zero frames
remains a separate global-entry task.
