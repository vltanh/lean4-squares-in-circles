# AB alignment allows an intermediate sign error of one tenth

## 1. Scope and conclusion

Put
\[
 q_L=\frac{19577}{5000},\qquad Q=\frac{9789}{2500},
                         \qquad q_L\le q\le Q.
\tag{1}
\]
Retain positive A and negative B signed tangents, their actual
sorted corner circles at most q, and the true central exclusion.
The G and T signed tangents \(y_G,y_T\) need not have the normal
signs. Assume instead
\[
                           y_G\le\frac1{10},
                  \qquad y_T\ge-\frac1{10}.
\tag{2}
\]
The real frames lie in an interval of length at most \(7/10\),
and retain
\[
               \theta_G\ge\theta_T,
        \qquad GA0,\quad BT2,\quad AB0\text{ or }AB2.
\tag{3}
\]

**Alignment theorem.** At the same q there is a necessary
descendant with
\[
 \theta_A'=\theta_B'=\rho\in[\theta_T,\theta_G],
                          \qquad b_A'+b_B'=1.
\tag{4}
\]
It keeps the actual G,T coordinates and frames fixed. Every
unchanged H,D,E datum and every constraint not incident to A/B
therefore remains identical. The new middle points are sorted,
have positive tangents, and satisfy the true central exclusion.
Separate strict A/B circle losses are retained. Every original
nonzero AB difference gives a strict middle-circle loss, and
an original common frame outside the G/T interval gives strict
losses in both middle circles.

The bounds (2) are explicit inputs. This theorem does not yet
prove them globally or remove the G/T signs from the complete
arbitrary-frame sharp assembly.

The proof extends
[direct AB alignment between G and T](HAND_G5_AB_ALIGNMENT_BETWEEN_ORDERED_INTERMEDIATE_FRAMES.md).
All of its geometric constructions remain valid. The affected
cap, sorting, and core estimates are supplied below, so no
normal-sign condition is imported from its old cap range.

## 2. The signed parameters and automatic middle core bound

Set
\[
                         D_G=\frac12-y_G,
                  \qquad D_T=\frac12+y_T.
\tag{5}
\]
The actual hard inequalities are exactly
\[
 a\cos z-b\sin z\ge W(z)+D-\frac12,
       \qquad W(z)=\frac{1+\cos z+|\sin z|}{2},
\tag{6}
\]
with \((a,b,z,D)=(a_A,b_A,\theta_G-\theta_A,D_G)\) or
\((a_B,b_B,\theta_B-\theta_T,D_T)\).
The parameter range is
\[
                         \frac25\le D_G,D_T<\frac{183}{200}.
\tag{7}
\]
The lower bound is (2). For the upper bound, the actual center
norm is below \(283/200\) and \(W\ge1\); hence
\(D-1/2<83/200\).

Sorting in (6) gives, for either angle sign,
\[
 a(\cos z+|\sin z|)
    \ge D+\frac12(\cos z+|\sin z|).
\]
Consequently every feasible middle primary, including every
one constructed below, satisfies
\[
               a\ge\frac12+\frac{2}{5\sqrt2}>\frac7{12}.
\tag{8}
\]
Thus the central core constraint is strict on this entire
enlarged parameter range.

The circle argument in Section 2 of the direct-alignment note
also gives, without a sign assumption on G or T,
\[
                       D\le\sqrt{q-1/4}-1.
\tag{9}
\]
That calculation maximizes the signed hard expression (6)
on the actual sorted A or B circle. Its decreasing function
\(R_q(b)\) and its two branches depend only on the middle
coordinates; D is the resulting upper bound. It follows in
particular that the zero-angle transverse cap is at least 1/2.

## 3. Positive hard caps on the enlarged range

For \(0\le z\le7/10\), write
\[
 c=\cos z,\quad s=\sin z,\quad C=D+c,\quad
 w=\sqrt{q-C^2},\quad X=Cc+ws,\quad L=wc-Cs.
\tag{10}
\]
The same exact identities hold:
\[
 X^2+L^2=q,\qquad (X-1)c-Ls=D,
                         \qquad -L_z=X\frac{w-s}{w}.
\tag{11}
\]
The roots and \(w-s\) are positive because
\[
 w^2-s^2=q-D^2-1-2D\cos z
                    >q_L-(383/200)^2>0.
\tag{12}
\]

Whenever \(L\ge1/2\), the required derivative bound is
\[
                               -L_z>\frac{11}{10}.
\tag{13}
\]
Put \(P=7/5\). Equations (7),(11) imply
\[
 P\le X<383/200,\qquad \tan z\le(X-P)/L.
\]
The exact expression
\[
 -L_z=X\frac{L+(X-1)\tan z}{L+X\tan z}
\]
decreases with \(\tan z\). Thus
\[
 -L_z\ge\frac{X\{q+P-(P+1)X\}}{q-PX}.
\tag{14}
\]
The denominator is positive. Its cleared difference from
\(11/10\) is
\[
 \mathcal P(q,X)=-(P+1)X^2+
           (q+P+(11/10)P)X-(11/10)q.
\tag{15}
\]
It increases with q and is concave in X. At the two endpoints
of the larger X interval, the exact values at \(q=q_L\) are
\[
 \mathcal P(q_L,7/5)=\frac{29331}{50000}>0,
 \qquad \mathcal P(q_L,383/200)=\frac{19811}{10^6}>0.
\tag{16}
\]
This proves (13) on the whole domain.

The rotated-cap comparison also retains its strict rate. For
\[
                   g_z(C)=\cos z\sqrt{q-C^2}-\sin z\,C,
\]
one has
\[
                 C\ge D+\cos z\quad\Longrightarrow\quad
                               g_z'(C)<-1
\tag{17}
\]
where the circle expression is defined. All comparison factors
are positive, and its squared inequality follows from
\[
\begin{aligned}
 2(D+\cos z)^2-q(1-\sin z)
 &\ge2(D+1)^2-q+
                   \sin z\{q-(4D+2)\sin z\}\\
 &>\frac{11}{2500}+\frac{591}{2500}\sin z>0.
\end{aligned}
\tag{18}
\]
Here \(\cos z\ge1-\sin^2z\), \(\sin z<13/20\), and
the full parameter range (7) were used. The two rational
reserves are \(2(7/5)^2-Q=11/2500\) and
\(q_L-(4(183/200)+2)(13/20)=591/2500\).

## 4. All AB differences still align

For AB0 put \(d=\theta_B-\theta_A\). Its actual shifted
inequality is unchanged:
\[
 Y_A+X_B\sin d+Y_B\cos d\ge1+\cos d+(\sin d)_+.
\tag{19}
\]

For \(d>0\) and \(\theta_A\ge\theta_T\), use the exact
construction in Section 3 of the direct-alignment note:
\[
 Y_0=2-Y_A,\qquad
 X_0=1+D_T\sec\gamma+Y_0\tan\gamma,
                     \quad\gamma=\theta_A-\theta_T\ge0.
\tag{20}
\]
Its comparison coordinates and negative-coefficient expansion
do not depend on the old lower bound D>=1/2. They give
\(X_0^2+Y_0^2<X_B^2+Y_B^2\). Both comparison coordinates
are positive: \(Y_0>3/5\) and now \(X_0\ge7/5\).
Since \(Q<2(7/5)^2\), that strict norm comparison forces
\(Y_0<X_0\). Thus sorting still follows, and the new primary
is at least 9/10, so the true core is retained.

For \(d<0\) with B below T, apply the compact contact descent
in Section 4 of that note until B reaches the first of A,T.
Its exact negative norm derivative does not contain D.
The transverse floor remains excluded by (19), and the core
is now excluded by (8). At a diagonal double contact the
BT equality gives
\[
                  \ell=1+\frac{D_T}{\cos z+\sin z}>1,
\]
which is the only sign of D used in its sorting argument.
The remaining single-contact alternatives and their strict
norm decreases are unchanged. Finish by (17) if A is above T.
The same rotated comparison treats an original nonnegative
B hard angle. Thus every negative AB difference aligns with
a strict B-circle loss.

For the remaining positive AB differences, the cases in
Section 5 of the direct note are still exhaustive. A positive
GA cap grows at rate greater than 11/10 when its hard angle
decreases, by (13), while the original AB demand grows at
rate less than 21/20. Hence both the complete A-to-B move
and the partial A-to-G move have a strict cap reserve. For
the latter the reserve is greater than
\[
                 (11/10-21/20)|\theta_G-\theta_A|
                         =\frac1{20}|\theta_G-\theta_A|.
\tag{21}
\]
A small primary decrease gives strict A-circle loss. Positive
hard contacts have \(X\ge7/5>\sqrt{Q/2}\), so the new
middle point is sorted. In the remaining frame sector
\(\theta_A<\theta_T\le\theta_G<\theta_B\), the partial
move ends at G, and (20) then contracts B to G. No H,D,E
order has been used.

## 5. Clamp the common frame into the intermediate interval

For a negative hard angle \(-z\), use
\[
 C=D+\cos z+\sin z,\quad w=\sqrt{q-C^2},
 \quad X=C\cos z-w\sin z,\quad
 M=C\sin z+w\cos z.
\tag{22}
\]
The sorted cap is
\(\overline M=\min\{M,\sqrt{q/2}\}\). Its upper-intersection
description is valid on the enlarged parameter range, since
\[
                  C\ge7/5>\sqrt q\sin z
\]
by \(\sqrt q<99/50\) and \(\sin z<13/20\).
The radicand is real along every required feasible interval
because C increases with z. Its transverse floor is retained:
at zero it follows from (9), at the original endpoint from
feasibility, and between them M has at most one critical
point, a maximum. Indeed
\[
 M_z=X\left(1-\frac{\cos z-\sin z}{w}\right),\qquad
 w^2-(\cos z-\sin z)^2
                  =q-D^2-2D(\cos z+\sin z)-2
\]
has decreasing sign because D>0.

Where the sorted cap is not diagonal,
\(w=M\cos z-X\sin z\le X(\cos z-\sin z)\). Therefore
\[
                       \overline M_z\le X-1<183/200.
\tag{23}
\]
On a diagonal portion its derivative is zero. The same
integrated comparison holds across the transitions.

If a common frame is a distance r above G or below T,
the clamp argument in Section 6 of the direct note now
has the strict total-cap reserve
\[
                      (11/10-183/200)r=\frac{37}{200}r.
\tag{24}
\]
Each endpoint positive cap is at most
\(\sqrt{Q-(7/5)^2}<7/5\), so a cap sum greater than two
makes each cap greater than 3/5. Choose transverse corners
strictly below those caps whose sum is two. Their primary
corners exceed 7/5 and they are strictly sorted. Both hard
constraints have slack, so both primaries can be decreased
slightly to create strict losses in both circles.

If the common frame already lies between T and G, normalize
any sum above one by decreasing a middle tangent. Both hard
angles are nonnegative; this improves the corresponding
constraint, and sorting and the strict core bound persist.

## 6. The other owner and original strictness

For AB2, interchange A with B and G with T and reverse the
local frame direction. The signed tangents are negated under
this formal reflection, so (2) becomes the same pair of bounds
and the two D parameters are interchanged. Undoing the labels
does not move or re-sign the actual G,T,H,D,E points.

Every strict-loss argument from Section 7 of the direct note
is retained: the direct norm contraction and compact descent
decrease the actual circle; positive-cap reconstruction keeps
its strict cap gap; the partial move gives (21); and an exterior
common-frame clamp gives (24) and strict losses in both circles.
An unchanged middle point retains its original circle value.
Thus losses are preserved separately, even if a later step
temporarily uses the common q-circle.

This proves (4) under exactly (1)--(3). The new ingredients are
the enlarged signed parameter range, the whole-range cap
comparisons (13),(17), and the explicit sorting/core checks.
No state or angle mesh, numerical acceptance premise, Lean
compilation, or CI result is used.
