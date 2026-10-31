# Two consecutive boundary contacts span less than three square-root-three halves

**Status: complete hand implication; full independent hand audit passed.** Suppose three consecutive members of a physical boundary-square cycle lie in the disk \(D_R\), where

\[
 \frac{\sqrt{17}}2\le R\le\frac{\sqrt{1105}}{16}.
\]

Their first and last centers have distance strictly less than \(3\sqrt3/2\). All orientations are independent, and no stress is required.

For the C7 covering-radius route, this excludes the acute supporting-triple gap partition \((1,2,4)\), in addition to the elementary exclusion of \((1,1,5)\). The two remaining partitions \((1,3,3)\) and \((2,2,3)\) are not resolved by this manuscript.

## 1. A uniform bound on each half-shadow

Use the radial frame of a circle-touching square, with center \((r,0)\), and put

\[
 h=\frac{\cos\psi+\sin\psi}{2},
 \qquad k=\frac{\cos\psi-\sin\psi}{2},
 \qquad 0\le\psi\le\frac\pi4.
\]

Then

\[
 h^2+k^2=\frac12,
 \qquad R^2=r^2+2rh+\frac12.
\]

The maximum absolute angular displacement of a square point from its center ray is

\[
 t_S=\arctan\frac{h}{r-k}.
\]

This formula, including both possible radial tilts, was proved from the four actual vertices in Section 3 of `BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md`.

We claim

\[
                t_S<t:=\arctan\frac35.
 \tag{1}
\]

At the comparison value \(r_*=k+5h/3\), the squared-circle expression is

\[
 r_*^2+2hr_*+\frac12
 =1+\frac{46}{9}h^2+\frac{16}{3}hk.
\]

Its difference below \(17/4\) is exactly

\[
\begin{aligned}
 \frac{17}{4}
 -\left(1+\frac{46}{9}h^2+\frac{16}{3}hk\right)
 &=\frac{13}{2}\left(k-\frac{16}{39}h\right)^2
   +\frac{23}{78}h^2\;>0.
\end{aligned}
 \tag{2}
\]

Since \(R^2\ge17/4\) and the expression \(r^2+2rh+1/2\) increases with positive r, we have \(r>r_*\). Thus \(h/(r-k)<3/5\), proving (1).

## 2. The two-contact endpoint distance

Let \(S_0,S_1,S_2\) be consecutive circle-touching squares, with lifted center angles \(\alpha_0<\alpha_1<\alpha_2\). The compatible contact-angle lifts are justified by the angular-order theorem, exactly as in Section 5 of `BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md`.

That manuscript proves that every full boundary-square shadow has width less than

\[
 w=\arctan\frac{23}{16},
\]

and every center radius is less than \(M=91/60\). Telescope the two contact angles through the middle square. Using (1) on the two endpoints and the full-shadow bound on the middle square gives

\[
            0<\gamma:=\alpha_2-\alpha_0<2t+w<\pi.
 \tag{3}
\]

The exact trigonometric value is

\[
 \cos(2t+w)
 =\frac{8\cdot16-15\cdot23}{17\sqrt{785}}
 =-\frac{217}{17\sqrt{785}}
 >-\frac{31}{68},
 \tag{4}
\]

where \(\sqrt{785}>28\) was used at the last step.

For the actual, possibly unequal, endpoint radii \(r_0,r_2<M\),

\[
\begin{aligned}
 |C_2-C_0|^2
 &=r_0^2+r_2^2-2r_0r_2\cos\gamma\\
 &<r_0^2+r_2^2+\frac{31}{34}r_0r_2\\
 &<2M^2\frac{99}{68}
 =\frac{91091}{13600}
 <\frac{27}{4}.
\end{aligned}
 \tag{5}
\]

The last positive margin is \(709/13600\). Hence

\[
                       \boxed{|C_2-C_0|<\frac{3\sqrt3}{2}.}
\]

## 3. Consequences for a minimum enclosing disk of C7 centers

The strict center-cover criterion in `CENTER_COVER_PIERCING.md` would close C7 completion if its seven centers could always be covered by a disk of radius less than \(3/2\).

For \(R<\sqrt{17}/2\), the origin itself supplies that cover, since every center satisfies \(r^2+r+1/2\le R^2<17/4\), hence \(r<3/2\). Consider only \(R\ge\sqrt{17}/2\).

The diameter theorem already excludes a minimum enclosing disk of radius at least \(3/2\) supported by two antipodal centers. Such a disk would therefore need an acute supporting triangle of centers. A right supporting triangle would also have an antipodal support pair and is excluded.

The three positive cyclic edge gaps between its vertices form, up to order, one of

\[
 (1,1,5),\quad(1,2,4),\quad(1,3,3),\quad(2,2,3).
 \tag{6}
\]

Let the supporting triangle have circumradius \(\rho\ge3/2\), and let its acute angles opposite side lengths a,b,c be A,B,C.

### 3.1. The partition (1,1,5)

Two sides are distances between touching unit-square centers, hence at most \(\sqrt2\). The sine rule and acuteness give, for each of their opposite angles,

\[
 \sin A\le\frac{\sqrt2}{3}<\frac12,
 \qquad A<\frac\pi6.
\]

The two such angles sum to less than \(\pi/3\), forcing the third angle to exceed \(2\pi/3\). This contradicts acuteness.

### 3.2. The partition (1,2,4)

The side corresponding to the one-edge gap again has opposite angle less than \(\pi/6\). The side corresponding to the two-edge gap satisfies (5), so its opposite acute angle B has

\[
 \sin B<\frac{3\sqrt3/2}{3}=\frac{\sqrt3}{2},
 \qquad B<\frac\pi3.
\]

These two angles sum to less than \(\pi/2\), forcing the third angle to exceed \(\pi/2\), again impossible.

Thus only

\[
                         \boxed{(1,3,3)\quad\text{or}\quad(2,2,3)}
\]

can support a remaining minimum-center-disk obstruction. Excluding both for the selected positive-stress C7, with all square orientations and all actual contacts retained, remains necessary for this covering-radius route. The stronger unstressed claim is false: C7_CENTER_COVER_GEOMETRIC_OBSTRUCTION.md supplies a physical (2,2,3) counterexample and proves separately that it has no positive C7 stress. No capacity conclusion for those two partitions is claimed here.
