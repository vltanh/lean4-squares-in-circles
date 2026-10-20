# All mixed DE/EH owners reduce after the non-E chain is aligned and ordered

## 1. The five-anchor input and conclusion

Put
\[
q_L=\frac{19577}{5000},\qquad Q=\frac{9789}{2500},
\qquad q_L\le q\le Q.
\tag{1}
\]
Let H,A,B,D,E have sorted nonnegative own-frame magnitudes,
the normal signed tangents positive at H,A and negative at
B,D,E, and actual corner values at most q. Retain the true
central exclusion and a common real frame interval of length
at most \(7/10\). The E state is an actual radial boundary
representative: either an outer state
\[
(a_E+1/2)^2+(b_E+1/2)^2=q
\tag{2}
\]
or a true core state. Its radial kind is an explicit input.

Assume that the non-E chain has already been aligned and
ordered. Set D's frame to zero, H's to \(\alpha=t+u\),
and the common A/B frame to u, where \(t,u\ge0\). Retain
the three necessary inequalities
\[
\begin{aligned}
b_H+a_A\cos t-b_A\sin t&\ge1+W(t),\\
b_A+b_B&\ge1,\\
a_B\cos u-b_B\sin u+b_D&\ge1+W(u),
\end{aligned}
\qquad
W(x)=\frac{1+\cos x+|\sin x|}{2}.
\tag{3}
\]
The E frame \(\delta=\theta_E\) is arbitrary in the original
frame interval; put \(\epsilon=\alpha-\delta\).
Instead of fixing the mixed owners, retain either original
DE axis 2 or 3 and either original EH axis 0 or 1:
\[
\begin{array}{c|l}
DE2&a_D\cos\delta+b_D\sin\delta+b_E\ge W(\delta)\\
DE3&a_D+a_E\sin\delta+b_E\cos\delta\ge W(\delta)\\
EH0&a_H\cos\epsilon+b_H\sin\epsilon-b_E\ge W(\epsilon)\\
EH1&a_H+a_E\sin\epsilon-b_E\cos\epsilon\ge W(\epsilon).
\end{array}
\tag{4}
\]

**Theorem.** Every system (1)--(4) has \(q\ge q_*\).
At equality, E was already between D and H, and the five
original anchors have the stationary values in
[the aligned hard-class theorem](HAND_G5_ALIGNED_HARD_CLASS_SHARP_REDUCTION.md).
Every retained original mixed witness is included, including
ties. The equality conclusion concerns the original anchors;
it does not identify a reconstructed E or D with its predecessor.

This removes both mixed-owner choices from the aligned,
ordered non-E class. It does not supply that prior alignment,
the non-E order, the normal signs, or the radial-boundary
input (2) for an unrestricted candidate.

## 2. Uniform consequences of the non-E chain

Sections 2--3 of
[the E-interior reduction](HAND_G4_E_INTERIOR_BOUNDARY_REDUCTION.md)
use only (3) and the four non-E circles. They give
\[
\begin{gathered}
0\le\alpha<11/50,\qquad .335<b_A,b_B<.665,\qquad
a_A,a_B>11/10,\\
a_H+a_D<1.9968-.718\sin\alpha<2.
\end{gathered}
\tag{5}
\]
The bound on \(\alpha\) includes zero here; that endpoint
will be covered by the reductions below. Also
\[
a_i>\frac{447}{800}=:L,\qquad b_i<9/10,
\qquad a_i<283/200.
\tag{6}
\]
The strict tangent cut in (5) yields the useful stronger bounds
\[
b_H,b_D>\frac{353}{500}=.706,
\qquad a_H,a_D<\frac{11}{10}.
\tag{7}
\]
Indeed \(b_A>.335\) and its circle imply \(a_A<1.294\),
since
\[
(1.794)^2-\{Q-(.835)^2\}=\frac{61}{10^6}>0.
\]
The first line of (3) implies \(b_H+a_A\ge2\), giving
the H bound in (7); B gives the D bound. Since these
tangents exceed .7, a primary at least 1.1 would have
corner square greater than \(1.6^2+1.2^2=4>Q\).

We use throughout the elementary estimates
\[
\sqrt q<\frac{1979}{1000},\quad
a_0(q):=\sqrt{q-1/4}-\frac12<\frac{283}{200},\quad
\tan(x/2)<\frac38\quad(0\le x\le7/10).
\tag{8}
\]
The last follows from
\((3/8)(1-(7/20)^2/2)>7/20\).

## 3. A core E is impossible for every mixed-owner pair

Suppose E is core. Then
\[
a_E\le7/12,\qquad b_E\le a_E\le7/12,
\qquad a_E>L.
\]
Rearrange each inequality in (4) as a demand on its
unrotated endpoint primary plus or minus \(b_E\).
For a positive error x, the extra demand beyond one is
bounded below by \(-\tfrac12\sin x\); for a negative
error \(-x\), it is bounded below by \(+\tfrac12\sin x\).
Here are the complete coefficient bounds, after dividing
the extra demand by \(\sin x\) for \(x>0\):
\[
\begin{array}{c|c|c}
\text{owner}&x>0&-x<0\\ \hline
DE2, EH0&-2/5&1/2\\
DE3&-1/12-\tfrac12\tan(x/2)>-13/48
 &L+1/2-\tfrac12\tan(x/2)>697/800\\
EH1&-1/12-\tfrac{13}{12}\tan(x/2)>-47/96
 &L+1/2-\tfrac{13}{12}\tan(x/2)>261/400.
\end{array}
\tag{9}
\]
For DE2 and EH0 the discarded cosine term is
\((a_D-1/2)(1-\cos x)\) or
\((a_H-1/2)(1-\cos x)\), which is nonnegative.
For clarity, the exact DE3 extra demand is
\[
(b_E-1/2)(1-\cos x)+\tfrac12|\sin x|-a_E\sin x,
\]
while the EH1 extra demand is
\[
-(b_E+1/2)(1-\cos x)+\tfrac12|\sin x|-a_E\sin x.
\]
These identities and (8) give every entry of (9), including
the continuous zero-error endpoint.

All four owners therefore give, with the appropriate signs
of the actual errors,
\[
a_D+b_E\ge1-\tfrac12\sin\delta,
\qquad a_H-b_E\ge1-\tfrac12\sin\epsilon.
\]
Consequently
\[
\begin{aligned}
a_H+a_D
&\ge2-\tfrac12(\sin\delta+\sin\epsilon)\\
&=2-\sin(\alpha/2)\cos((\delta-\epsilon)/2)\\
&\ge2-\sin(\alpha/2).
\end{aligned}
\tag{10}
\]
This contradicts (5): since \(\cos(\alpha/2)>.99\),
\[
2-\sin(\alpha/2)
 -(1.9968-.718\sin\alpha)
=.0032+\{1.436\cos(\alpha/2)-1\}\sin(\alpha/2)>0.
\tag{11}
\]
The case \(\alpha=0\) is included. By the explicit radial
alternative in Section 1, E is therefore outer.

## 4. A nonnegative mixed error supplies the primary witness

Set \(c_q=\sqrt{q/2}-1/2\). Because E is outer and sorted,
\(a_E\ge c_q\), whereas every contained sorted endpoint
has \(b_H,b_D\le c_q\).
For \(\epsilon\ge0\), the exact difference of the two
EH projections is
\[
P_{EH1}-P_{EH0}
=(a_H+b_E)(1-\cos\epsilon)
                  +(a_E-b_H)\sin\epsilon\ge0.
\tag{12}
\]
For \(\delta\ge0\),
\[
P_{DE3}-P_{DE2}
=(a_D-b_E)(1-\cos\delta)
                  +(a_E-b_D)\sin\delta\ge0.
\tag{13}
\]
To check the latter sign when \(a_D-b_E<0\), sorting gives
\(a_E-b_D\ge b_E-a_D\), and
\(\sin\delta\ge1-\cos\delta\). If \(a_D-b_E\ge0\),
both terms are nonnegative directly.

Thus an E between D and H already has actual DE3 and EH1
witnesses. The aligned hard-class theorem applies with no
change to its five original anchors. It remains to handle
E above H and E below D.

## 5. E above H: the rotated EH0 branch reaches the excluded endpoint

Suppose \(\epsilon=-x<0\), \(\delta=\alpha+x>0\).
By (13), DE3 is feasible. If EH1 is feasible as well,
[the E-order theorem](HAND_G5_E_ORDER_FROM_ALIGNED_NON_E_CHAIN.md)
already excludes this whole above-H branch. Retain EH0
for the remaining case.

Write \(a=a_E\), \(b=b_E\),
\(A_H=a_H-1/2\), \(B_H=b_H+1/2\). The original EH0
inequality is equivalent to
\[
b' -b\ge A_H(1-\cos x)+B_H\sin x,
\qquad b':=a_H-1.
\tag{14}
\]
In particular \(a_H>1\). Equations (7), (14) give
\[
0\le b<b'<1/10,
\qquad A_H>1/2,
\qquad B_H>603/500.
\tag{15}
\]
On the actual q-circle put
\[
a_q(y)=\sqrt{q-(y+1/2)^2}-1/2,
\qquad M_\alpha(y)=(a_q(y)-1/2)\sin\alpha
                                      +(y-1/2)\cos\alpha.
\]
For \(b\le y\le b'\), the primary corner exceeds 9/5,
because \(q_L-(3/5)^2>(9/5)^2\). Thus
\[
M_\alpha'(y)
=\cos\alpha-\frac{y+1/2}{a_q(y)+1/2}\sin\alpha
>1-\frac{(11/50)^2}{2}-\frac13\frac{11}{50}
=\frac9{10}+\frac{37}{15000}.
\tag{16}
\]
It follows that
\(M_\alpha(b')-M_\alpha(b)>(9/10)(b'-b)\).

The loss from reducing the old E angle \(\alpha+x\) to
\(\alpha\) at fixed old coordinates is
\[
M_{\alpha+x}(b)-M_\alpha(b)
=\{(a-1/2)\cos\alpha-(b-1/2)\sin\alpha\}\sin x
                         -M_\alpha(b)(1-\cos x).
\]
Its sine coefficient is less than
\(183/200+(1/2)(11/50)=41/40\), and
\(M_\alpha(b)\ge-1/2\). Combining this with (14)--(16),
\[
\begin{aligned}
M_\alpha(b')-M_{\alpha+x}(b)
&>\left(\frac9{10}\frac{603}{500}-\frac{41}{40}\right)\sin x
                                    -\frac1{20}(1-\cos x)\\
&>\frac{833}{20000}\sin x>0.
\end{aligned}
\tag{17}
\]
The second step uses \(\tan(x/2)<3/8\).

Now place E at H's frame, with coordinates
\((a_q(b'),b')\). Its circle is still q, it is strictly
sorted and outside the core, and EH1 at zero error is an
equality: \(a_H-b'=1\). The DE3 margin strictly increases
by (17), so DE3 remains feasible. H,A,B,D and their frames
are unchanged. This is precisely the epsilon-zero necessary
system excluded at Q by
[the aligned epsilon-zero theorem](HAND_G5_ALIGNED_HARD_EPSILON_ZERO_EXCLUSION.md).
If \(\alpha=0\), its two endpoint inequalities already
give \(a_H+a_D\ge2\), contradicting (5).
Thus E above H is impossible for either original EH owner.

## 6. E below D: descend the rotated DE2 contact curve

Suppose \(\delta=-x<0\), \(\epsilon=\alpha+x>0\).
By (12), EH1 is feasible. If DE3 is feasible, the E-order
theorem already gives an E-only descendant with
\(\delta'=0\) and strict E-circle loss; H,A,B,D remain
unchanged. That descendant joins the aligned hard-class
theorem. We therefore treat a retained DE2 witness directly.

Put
\[
A_D=a_D-1/2,\quad B_D=b_D+1/2>603/500,
\qquad b(z)=\frac12-A_D\cos z+B_D\sin z.
\tag{18}
\]
The actual DE2 inequality is \(b_E\ge b(x)\).
At fixed z, EH1 improves if E's nonnegative tangent is
decreased along its q-circle. Thus at the original E frame
we may first replace its tangent by \(\max(0,b(x))\),
using its q-circle primary. This preserves DE2 and improves
or retains EH1. If the new tangent is zero, go to Section 7.

Otherwise let z decrease from x, with the contact tangent
\(b(z)>0\), until the first of \(z=0\) or \(b(z)=0\).
The derivative
\[
K(z):=b'(z)=A_D\sin z+B_D\cos z>0
\tag{19}
\]
shows that the tangent decreases throughout. Its q-circle
primary therefore increases and remains strictly sorted;
every intermediate state is outside the true core. All
changing frames lie between the original E and D frames.

Here is a uniform proof that EH1 strictly improves during
this entire descent. Put
\[
Y=b(z)+1/2=1-A_D\cos z+B_D\sin z,
\quad X=\sqrt{q-Y^2},\quad U=X-K(z).
\tag{20}
\]
On the traversed sorted arc \(0<Y\le X\). The EH1 margin is
\[
J(z)=a_H-1/2+(X-1)\sin(\alpha+z)-Y\cos(\alpha+z).
\]
Exact differentiation gives
\[
J'(z)=(U-1)\cos(\alpha+z)
              +\frac{YU}{X}\sin(\alpha+z).
\tag{21}
\]
Solving (20) for K and using one actual E circle gives
\[
\begin{aligned}
U&=\frac{X\cos z+Y\sin z-\sin z-B_D}{\cos z}\\
&\le\frac{\sqrt q-B_D-\sin z}{\cos z}
<g(z):=\frac{773/1000-\sin z}{\cos z}.
\end{aligned}
\tag{22}
\]
Write \(\kappa=773/1000\). The derivative of g satisfies
\[
g'(z)=\frac{\kappa\sin z-1}{\cos^2z}<-\frac45,
\tag{23}
\]
because the quadratic
\[
\frac45s^2-\kappa s+\frac15
\ge\frac15-\frac5{16}\kappa^2
=\frac{42471}{3200000}>0
\]
is positive for every real s. Hence
\[
U<\kappa-\frac45z,
\qquad \kappa-\frac45z>0\quad(0\le z\le7/10).
\tag{24}
\]
If \(U\le0\), (21) is already negative. If \(U>0\),
use \(Y/X\le1\), \(\cos(\alpha+z)>3/4\), and
\(\sin(\alpha+z)\le\alpha+z\). Equations (5), (24) give
\[
\begin{aligned}
\frac{J'(z)}{\cos(\alpha+z)}
&<\left(\kappa-\frac45z\right)
       \left(1+\frac43\left(\frac{11}{50}+z\right)\right)-1\\
&=-\frac{19}{75000}-\frac{z}{250}-\frac{16z^2}{15}<0.
\end{aligned}
\tag{25}
\]
This proves strict improvement as z decreases. It is one
whole-interval comparison, without subdivisions of the
contact curve.

If the descent reaches \(z=0\), its tangent is
\(b(0)=1-a_D\ge0\), and the aligned DE3 inequality is an
equality. EH1 has strict slack, since the original x was
positive. If \(\alpha=0\), adding the two endpoint
inequalities contradicts (5). Otherwise decrease E's primary
slightly, keeping its tangent and frame fixed. This preserves
DE3, the strict EH1 inequality, sorting and the true core,
and gives strict E-circle loss. The aligned hard-class theorem
now gives \(q\ge q_*\), with equality impossible because
its stationary E circle has value q. All four non-E anchors
were retained unchanged.

The only other endpoint is a zero E tangent at some
\(z>0\). We next exclude this endpoint, including the case
where the initial replacement already had zero tangent.

## 7. A zero tangent before D is excluded by a D/T move

At this endpoint E has tangent zero, primary \(a_0(q)\),
and frame \(-z\), with \(z>0\). EH1 is feasible. The
remaining original DE2 condition is
\[
(a_D-1/2)\cos z-(b_D+1/2)\sin z\ge\frac12.
\tag{26}
\]
In particular \(a_D>1\).

For the standard positive hard cap write
\[
\begin{gathered}
L_q(s,D)=\cos s\sqrt{q-(D+\cos s)^2}
                         -\sin s(D+\cos s),\\
Y_D=b_D+1/2,\qquad Y_0=L_q(0,1/2)=\sqrt{q-9/4}.
\end{gathered}
\tag{27}
\]
Equation (26) gives \(Y_D\le L_q(z,1/2)\).
The published positive-cap inequality \(-\partial_sL_q>9/8\)
holds throughout this feasible interval. Since
\(Y_D>603/500\) and \(Y_0<1291/1000\), it follows that
\[
\frac98z<Y_0-Y_D<\frac{85}{1000},\qquad z<\frac2{25}.
\tag{28}
\]
On \([0,z]\), put
\(w=\sqrt{q-(1/2+\cos s)^2}\), and let X be the positive
cap's primary corner. Then
\[
w>129/100,\qquad X\ge3/2,
\]
because \(q_L-9/4-(129/100)^2=13/10000\).
The exact cap derivative therefore sharpens to
\[
-\partial_sL_q=X\frac{w-\sin s}{w}
>\frac32\left(1-\frac{2/25}{129/100}\right)
=\frac{121}{86}>\frac75.
\tag{29}
\]
Consequently \(Y_0-Y_D>(7/5)z\).

Keep H,A,B,E and their frames fixed. Move D's frame down
to E's frame and set
\[
a_D'=1,\qquad b_D'=Y_0-1/2.
\tag{30}
\]
This is a strictly sorted D point on the same q-circle.
If an actual T representative is needed, set its frame to
D's new frame, \(a_T'=7/12\), \(b_T'=1-b_D'\).
Its tangent is positive and less than .211, so it is a
sorted true-core point with circle below \(q_L\).

The new B hard angle is \(u+z\). With B's actual unchanged
coordinates, put
\[
V_B(s)=(a_B-1/2)\cos s-(b_B+1/2)\sin s.
\]
By (5) and B's actual circle,
\[
|V_B'(s)|
\le\sqrt{(a_B-1/2)^2+(b_B+1/2)^2}
\le\sqrt{q-2a_B}
<\sqrt{Q-11/5}<\frac43.
\tag{31}
\]
The last squared reserve is \(1399/22500>0\).
The old third inequality in (3) is
\(V_B(u)\ge2-Y_D\). Thus (29)--(31) give
\[
V_B(u+z)>2-Y_0+\frac{z}{15}.
\tag{32}
\]
The new B/D composite is strictly feasible. A small decrease
of B's primary records strict B-circle loss while retaining
its tangent and AB inequality, sorting, and the true core.

Now the A/B frame still lies between the new D frame and H;
the total span is \(\alpha+z\), an original H/E frame
difference less than \(7/10\). The E frame agrees with D,
and DE3 at zero error is an equality, since \(a_D'=1\)
and \(b_E=0\). EH1 was unchanged. This is exactly the
aligned hard five-anchor system with zero E tangent, excluded
at Q by
[the E-zero split theorem](HAND_G5_E_ZERO_HARD_QUARTER_SPLIT_EXCLUSION.md).
Hence this endpoint is impossible.

## 8. Completion and equality bookkeeping

Every core E was excluded in Section 3. For outer E between
D and H, Sections 4 and the aligned hard-class theorem
give the sharp result on the original five anchors.
E above H is excluded by Section 5, for both original
EH owners. E below D either follows the existing primary
E-order descent or the contact-curve descent in Section 6;
both retain strict E-circle loss. Its possible zero-tangent
endpoint is excluded in Section 7.

Thus the only equality case lies in the unchanged, inside
E branch, where the original anchors are exactly the
stationary ones. A prior strict loss at A or B remains
untouched in Sections 3--6; Section 7 creates a strict B
loss itself and ends in an outright contradiction. The
actual circle of a reconstructed E was never attributed to
an original E. All new frame positions lie in the original
full real-frame interval.

The proof uses actual original projection comparisons,
one whole-interval contact-curve derivative, positive cap
rates, and the already proved sharp and endpoint theorems.
Every displayed numerical constant is an exact rational.
No state or angle mesh, numerical acceptance premise,
Lean compilation, or CI result enters the argument.
