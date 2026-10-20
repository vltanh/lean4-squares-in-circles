# The intermediate frames can be ordered after exact AB alignment

## 1. Scope and conclusion

Put
\[
 q_L=\frac{19577}{5000},\qquad Q=\frac{9789}{2500},
 \qquad q_L\le q\le Q.
\tag{1}
\]
Retain the normal H,G,A,B,T,D signs, sorted nonnegative own-frame
coordinates, actual corner ceilings at most q, the true core,
and a real frame interval of length at most \(7/10\). The E tangent
may have either sign. Retain the hard GA0 and BT2 inequalities,
either original transverse owner on each of HG and TD, and the two
DE3/EH1 inequalities displayed in
HAND_G5_REVERSED_INTERMEDIATE_SPAN_WITH_NONNEGATIVE_OUTER_ERRORS.md.
No H/D/E frame ordering is assumed.

Assume that AB has already been aligned exactly:
\[
                 \theta_A=\theta_B=\rho,
                 \qquad b_A+b_B=1.
\tag{2}
\]

**Theorem.** This necessary system has a descendant at the same
working q with
\[
 \theta_G'\ge\theta_T',\qquad
 \theta_A'=\theta_B'=\rho'\in[\theta_T',\theta_G'],
 \qquad b_A'+b_B'=1.
\tag{3}
\]
H, D, E and all their coordinates and frames stay fixed. The actual
HG and TD owner inequalities remain available, with concrete sorted
core realizations of any replaced G or T. All constructed frames
remain in the original full frame interval. Separate strict losses
in the A and B circles are retained. If initially
\(\theta_G<\theta_T\), at least one final middle circle has a
strict loss.

This theorem starts from (2). It does not assert that arbitrary
original AB frames can already be aligned in the reversed
intermediate case. As elsewhere in the hand reduction, the
constructed neighboring system need not retain omitted
nonneighbor inequalities or the physical-gap hypotheses. A smaller
original radius may first be enlarged to q_L for a radius lower
bound; every construction below then uses the working q in (1).

## 2. Three elementary cap facts

The direct hard inequalities imply
\[
 0\le b_G,b_T<\frac{83}{200},\qquad
 D_G:=b_G+\frac12,\ D_T:=b_T+\frac12\in[\tfrac12,\tfrac{183}{200}).
\tag{4}
\]
Indeed each demand is at least one, and the actual nonnegative
middle center has norm less than \(283/200\).
Every feasible middle hard point also has
\[
                     a\ge\frac12+\frac1{2\sqrt2}>\frac7{12}.
\tag{5}
\]
This follows by bounding the hard projection by
\(a(\cos z+|\sin z|)\), using sorting. These are the direct
bounds in Section 2 of
HAND_G5_AB_ALIGNMENT_BETWEEN_ORDERED_INTERMEDIATE_FRAMES.md;
they do not use intermediate frame order.

For a nonnegative hard angle z and parameter D, the shifted
transverse cap is
\[
 L(z,D)=\cos z\sqrt{q-(D+\cos z)^2}
                         -\sin z(D+\cos z).
\tag{6}
\]
For \(1/2\le D<183/200\), the published positive-cap comparison
gives
\[
                   -L_z>\frac98\quad\text{whenever }L\ge\frac12.
\tag{7}
\]
Every transverse corner \(Y\in[1/2,L]\) is feasible on its
q-circle. The corresponding primary is strictly sorted: the
hard inequality forces \(X\ge1+D\ge3/2>\sqrt{Q/2}\).

For a negative hard angle \(-z\), \(z\ge0\), put
\[
\begin{gathered}
 C=D+\cos z+\sin z,\qquad w=\sqrt{q-C^2},\\
 M=C\sin z+w\cos z,\quad m=C\sin z-w\cos z,\qquad
 \overline M=\min(M,\sqrt{q/2}).
\end{gathered}
\tag{8}
\]
The feasible sorted q-circle tangents form exactly the interval
\[
                  \max(\tfrac12,m)\le Y\le\overline M.
\tag{9}
\]
Starting from any feasible angle \(z_0\), the radical in (8) is
real throughout \([0,z_0]\), because C increases with z.
The upper cap stays at least one half on that interval and obeys
the integrated upper-slope bound
\[
             \overline M(z_2,D)-\overline M(z_1,D)
                    <\frac{183}{200}(z_2-z_1)\quad(z_2>z_1).
\tag{10}
\]
These assertions are proved in Section 6 of the cited direct AB
note, using the exact identity
\[
 M_z=X\left(1-\frac{\cos z-\sin z}{w}\right)\le X-1<\frac{183}{200}
\]
on the non-diagonal portion, where \(X=C\cos z-w\sin z\).
The diagonal portion has derivative zero.

We will also need the lower endpoint in (9). Direct differentiation
gives
\[
 m_z=X_-\left(1+\frac{\cos z-\sin z}{w}\right)>0,
 \qquad X_-=C\cos z+w\sin z.
\tag{11}
\]
The comparison extends by continuity at a zero radical. Hence as
a negative hard angle decreases in magnitude, its lower feasible
transverse endpoint cannot increase. After any strict decrease
from an initially zero radical, the radical is positive. Equations
(9)--(11), including the lower endpoint, will ensure that a cap-sum
comparison actually supplies two feasible middle points.

## 3. A negative canceling outer error needs no H/A order

Suppose HG2 has \(\theta_G<\theta_H\). Normalize A's frame to
zero and write \(\Theta=\theta_H\), \(t=\theta_G<\Theta\),
\(e=\Theta-t\). The two original HG2/GA0 inequalities imply
\[
\begin{aligned}
 F(t):={}&(a_A-\tfrac12)\cos t-J(t)\sin t\\
        &+(b_H-\tfrac12)\cos(\Theta-t)
                         -(a_H+\tfrac12)\sin(\Theta-t)\ge1,
\end{aligned}
\tag{12}
\]
where \(J(t)=b_A-1/2\) for \(t<0\) and
\(J(t)=b_A+1/2\) for \(t\ge0\).

For \(\Theta\ge0\), Section 3 of
HAND_G4_SIGNED_THREE_ZERO_REDUCTION_FOR_CANCELING_OUTER_OWNERS.md
proves the forward-barrier derivative \(F'(t)>3/20\) wherever
\(F(t)\ge1\). Its proof allows either sign of t.
For \(\Theta<0\), every intervening t is negative. The same
exact differentiation used there gives
\[
\begin{aligned}
 F'(t)(\cos e-\sin e)
 \ge{}&1+\cos e+\sin e\\
      &-(a_A+b_A-1)\cos\Theta-(a_A-b_A)\sin\Theta.
\end{aligned}
\tag{13}
\]
Here \(a_A+b_A-1<4/5\), \(a_A-b_A\ge0\),
and \(\sin\Theta<0\). The right side exceeds \(6/5\).
Since \(0<\cos e-\sin e\le1\), this is stronger than the
same \(3/20\) derivative bound. Thus the original forward-barrier
argument applies for every H/A order and gives
\[
 F(\Theta)>1+\frac3{20}(\theta_H-\theta_G).
\tag{14}
\]

Set \(\theta_G'=\theta_H\),
\(a_G'=7/12\), \(b_G'=1-b_H\). The HG2 inequality is an
equality, and (14) is precisely the hard GA0 inequality with
strict slack. Feasibility of that hard inequality gives
\(1/10<b_G'<83/200\), so the replacement is sorted, on the
true core, and has circle strictly below q_L. The actual H and A
anchors have not moved. A sufficiently small decrease of \(a_A\)
converts the strict slack to a strict A-circle loss while retaining
(2). Sorting is strict: a diagonal middle point would make the
shifted hard value at most \((2/5)\sqrt2<3/5\), whereas here
its required parameter is \(3/2-b_H>3/5\). The primary core
is strict by (5).

The reflected argument aligns every negative TD0 error, retaining
a strict B loss. The E data need not be reflected; only the named
local formulas are exchanged.

## 4. A negative HG0 has a concrete decreasing core parameter

Suppose now that HG0 has \(G<H\), writing frame letters for
their real values. The true core at the original G gives
\(a_G\ge7/12\), because (4) gives \(b_G<1/2\).
Set
\[
 e=H-G>0,\qquad
 D(e)=1+(\tfrac12-b_H)\sec e+\frac{13}{12}\tan e.
\tag{15}
\]
The original HG0 inequality implies \(b_G+1/2\ge D(e)\).
The derivative satisfies
\[
\begin{aligned}
 D'(e)-1
 &=\frac{13/12+(1/2-b_H)\sin e-\cos^2e}{\cos^2e}\\
 &\ge\frac{(\sin e-1/5)^2+13/300}{\cos^2e}>0.
\end{aligned}
\tag{16}
\]
Consequently
\[
             \frac35<D(0)\le D(e)\le b_G+\frac12<\frac{183}{200}.
\tag{17}
\]
For every later value of e decreased from the original one, use
the exact realization
\[
                 a_G'=\frac7{12},\qquad b_G'=D(e)-\frac12.
\tag{18}
\]
HG0 is an equality, and the hard A inequality has parameter D(e).
This replacement is sorted and core-avoiding, with
\[
 (a_G'+\tfrac12)^2+(b_G'+\tfrac12)^2
 <\frac{169}{144}+\left(\frac{183}{200}\right)^2
 =\frac{723901}{360000}<q_L.
\tag{19}
\]
Replacing the original G by (18) initially only decreases the
hard GA demand. It changes no retained constraint outside HG/GA.

## 5. Consume a negative HG0 while \(G<T\)

Assume \(G<T\) and retain the common AB frame \(\rho\).
The following three elementary moves end either at \(G=T\)
or with \(G=H\), so the negative error has disappeared.

### 5.1 Raise a crossed G at the fixed common frame

If \(G\le\rho\), keep both actual middle coordinates and their
common frame fixed, and increase G until the first of H, T, or
\(\rho\) is reached. For \(t=G-\rho\le0\), the hard A
expression is
\[
 V_-(t)=(a_A-\tfrac12)\cos t-(b_A-\tfrac12)\sin t.
\]
Its slack over D satisfies, by (16),
\[
 \frac{d}{dG}\{V_-(G-\rho)-D(H-G)\}
 =-(a_A-\tfrac12)\sin t-(b_A-\tfrac12)\cos t+D'(e)
 >\frac35.
\tag{20}
\]
Thus the move is feasible throughout. Use (18) for G, and
convert any strict accumulated slack into strict A-circle loss
by a small decrease of its primary, as in Section 3. If H or T
is reached, this side is finished. Otherwise \(G=\rho<T,H\).

### 5.2 Bring a lower common frame up to G

If initially \(\rho<G<T\), keep G fixed and move the common
frame upward from \(\rho\) to G. The A hard angle is
nonnegative and decreases. Its cap \(L(G-\rho,D(e))\)
increases at rate greater than \(9/8\), by (7).
The B hard angle is negative, with magnitude \(z=T-\rho\).
Its upper cap can decrease at rate at most \(183/200\), by
(10), while its lower feasible endpoint decreases by (11).
Therefore after any positive common-frame displacement \(s\),
the sum of the two upper caps exceeds its original value by
more than
\[
                       \left(\frac98-\frac{183}{200}\right)s
                                      =\frac{21}{100}s.
\tag{21}
\]
It originally was at least two, by (2).

Here is the feasibility detail for this cap-sum construction.
At the new frame choose
\[
 \max\{\tfrac12,m(T-\rho,D_T),\,2-L(G-\rho,D(e))\}
                              <Y_B<\overline M(T-\rho,D_T),
 \qquad Y_A=2-Y_B.
\tag{22}
\]
Such a choice exists: the last term on the left is below the
upper cap by (21); the lower circle root is strictly below it
after any positive movement; and the upper cap is greater than
\(2-L>2-1.291>.7>1/2\). The root assertion also covers an
initially zero radical, which becomes positive immediately.
The two chosen tangents are inside their actual feasible circle
arcs. They are strictly sorted, are above the transverse floor,
and satisfy both hard constraints with strict slack on their
q-circles. Slightly decrease both primaries. This retains (2),
the true core by (5), and both hard inequalities, while creating
strict losses in both middle circles. The same construction can
be made at every intervening frame; for the conclusion only the
endpoint choice is needed. We have reached \(\rho=G\).

### 5.3 Move the common frame together with G

Now \(\rho=G<T,H\). Increase both \(\rho\) and G together
until the first of H or T is reached. The A hard angle stays zero,
and its cap is
\[
                  L(0,D(e))=\sqrt{q-(1+D(e))^2}.
\]
Its derivative with respect to the increasing common frame is
\[
 \frac{1+D(e)}{\sqrt{q-(1+D(e))^2}}D'(e)
                >\frac{320}{233}>\frac98.
\tag{23}
\]
Indeed \(1+D>8/5\), \(D'>1\), and
\(\sqrt{Q-(8/5)^2}<233/200\). The B negative hard angle
again decreases, so (10)--(11) apply unchanged. The cap sum
therefore grows strictly as before. Equation (22), now with
the zero-angle A cap, supplies a feasible exact AB sum and
strict losses in both middle circles at the endpoint. Use
(18) for the changing G throughout.

Every changing frame lies between original G, H, T, and the
original common frame. No frame leaves the original full span.
The process ends at \(G=T\), or at \(G=H<T\), as claimed.

## 6. Both sides and the remaining reverse case

Reflect the preceding local formulas by
\[
 (H,G,A,B,T,D;\theta)\longleftrightarrow
 (D,T,B,A,G,H;-\theta).
\tag{24}
\]
The condition \(G<T\) becomes the same condition in the new
names. This gives the identical consumption for a negative TD2
error. Only the changed local coordinates and frames are used;
H, D, E and the actual E inequalities remain fixed.

Start from any feasible system satisfying (2) with \(G<T\).
If HG is negative, process it by Section 3 or Sections 4--5,
according to its original owner. Either the intermediate order
has been reached, or HG is now aligned. If the order is still
reversed and TD is negative, process that side by its reflected
construction. The previously processed HG frame and owner are
unchanged, and its hard inequality is retained by the cap
construction. Thus no processed negative outer error is recreated.

If these at most two operations had still left \(G<T\), both
remaining outer errors would be nonnegative. The result would
satisfy
\(H\le G<T\le D\), together with the same exact common AB
sum and all the retained hypotheses of
HAND_G5_REVERSED_INTERMEDIATE_SPAN_WITH_NONNEGATIVE_OUTER_ERRORS.md.
That theorem excludes it. Hence some operation must reach
\(G\ge T\).

If the original intermediate order already held, no such processing
was necessary. In either case apply the common-frame clamp in
Section 6 of
HAND_G5_AB_ALIGNMENT_BETWEEN_ORDERED_INTERMEDIATE_FRAMES.md
to put the common frame in \([T,G]\), retaining sum one.
This changes only A/B, keeps all new G/T realizations fixed,
and proves (3).

## 7. Strict losses and the boundary of the conclusion

A fixed-anchor negative canceler creates strict hard slack and
then a strict loss in its adjacent middle circle. A crossed-core
move does the same by (20). Every positive common-frame movement
in Sections 5.2--5.3 creates strict slack at both middle points
and hence strict losses in both circles. These latter
reconstructions also recreate any earlier separate A/B strict
losses after a temporary use of the q-circle; an unchanged point
keeps its actual prior loss. The final ordered-intermediate clamp
has the same separate strictness property.

More explicitly, in (22) each chosen corner is strictly inside
its own hard feasible arc. If its q-circle coordinates are
\((X_i,Y_i)\), choose \(\varepsilon_i>0\) small enough to
retain that strict hard slack and sorting. Its new corner value is
\[
 (X_i-\varepsilon_i)^2+Y_i^2
       =q-\varepsilon_i(2X_i-\varepsilon_i)<q.
\tag{25}
\]
Choose the two positive \(\varepsilon_i\) separately. Thus every
step that uses a common q-circle finishes with strict deficits
at both anchors, including either anchor carrying a prior strict
deficit. Every other step either leaves the anchor unchanged or
decreases its actual primary. A zero-length cap step is the identity
and uses no temporary lift. This is an induction preserving, for
each anchor separately, the assertion that its actual corner is
strictly below q; it does not assert preservation of the numerical
size of that deficit.

If the original order was reversed, the all-nonnegative alternative
was impossible from the outset by the cited reverse-span theorem.
At least one negative error of positive magnitude was therefore
processed. Each such process has a positive movement and the
strict loss just described. This proves the strict assertion in
Section 1 without identifying a reconstructed G/T point with an
original center.

The remaining unrestricted alignment issue is now sharply located:
the input (2) must still be obtained from arbitrary original AB
frames when \(G<T\). No unproved intermediate order or E order
is used above. All comparisons are continuous whole-interval
cap inequalities or the exact analytic reverse-span exclusion;
no numerical acceptance premise, state or angle mesh, Lean
compilation, or CI is used.
