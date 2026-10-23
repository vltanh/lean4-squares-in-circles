# AB aligns between ordered intermediate frames without H/D frame order

## 1. The direct four-anchor statement

Put \(q_L=19577/5000\), \(Q=9789/2500\), and work at
\(q_L\le q\le Q\). Retain the normal signed tangents at
G,A,B,T, their nonnegative sorted own-frame magnitudes, and
their actual corner ceilings at most q. The real frames have
spread at most \(7/10<\pi/4\). Assume only the intermediate
frame order
\[
                           \theta_G\ge\theta_T.
\tag{1}
\]
There is no order assumption involving H,D,E or the middle
frames. Retain original owners GA0, BT2 and either AB0 or AB2.
In particular the direct hard inequalities are
\[
\begin{aligned}
 a_A\cos(\theta_G-\theta_A)
       -b_A\sin(\theta_G-\theta_A)&\ge\widehat W(\theta_G-\theta_A)+b_G,\\
 a_B\cos(\theta_B-\theta_T)
       -b_B\sin(\theta_B-\theta_T)&\ge\widehat W(\theta_B-\theta_T)+b_T,
\end{aligned}
\quad
\widehat W(v)=\frac{1+\cos v+|\sin v|}{2}.
\tag{2}
\]

**Direct AB alignment.** These constraints have a descendant
at the same q with
\[
 \theta_A'=\theta_B'=\rho\in[\theta_T,\theta_G],
                    \qquad b_A'+b_B'=1.
\tag{3}
\]
It keeps the actual G and T coordinates and frames fixed.
Consequently all H,G,T,D,E data and every retained constraint
not incident to A/B remain fixed. New middle coordinates are
nonnegative, sorted and satisfy the true core. Separate strict
A/B corner losses are retained. A nonzero original AB frame
difference creates a strict loss in at least one middle circle;
an originally common frame outside the interval in (3) creates
strict losses in both.

The sole remaining frame hypothesis here is (1). This note
does not exclude or reduce the reverse intermediate order
\(\theta_G<\theta_T\), and does not align HG or TD.

For AB0 put \(d=\theta_B-\theta_A\), and write the middle
corner coordinates \(X_i=a_i+1/2,\ Y_i=b_i+1/2\). Its exact
inequality is
\[
 Y_A+X_B\sin d+Y_B\cos d
                      \ge1+\cos d+(\sin d)_+.
\tag{4}
\]
The proof first treats this owner.

## 2. The direct hard caps

Set
\[
                       D_G=b_G+\frac12,\qquad D_T=b_T+\frac12.
\tag{5}
\]
Both parameters lie in \([.5,.915)\). Indeed every nonnegative
center has norm less than \(283/200\), from its q-circle, while
\(\widehat W\ge1\); (2) therefore gives \(b_G,b_T<.415\).

For a nonnegative hard-quarter angle z the corner cap is
\[
 (X-1)\cos z-Y\sin z\ge D,
\]
and its transverse frontier is
\[
 L(z,D)=\cos z\sqrt{q-(D+\cos z)^2}
                              -\sin z(D+\cos z).
\tag{6}
\]
The positive-cap comparisons of
HAND_G4_SIGNED_THREE_ZERO_REDUCTION_FOR_CANCELING_OUTER_OWNERS.md
apply on this subinterval of its parameter range. In particular
\[
                    -L_z>9/8\quad\hbox{whenever }L\ge1/2.
\tag{7}
\]
Its rotated-cap comparison also applies whenever an old
nonnegative quarter angle increases to another nonnegative
one.

We will also use two elementary facts, including when a hard
quarter angle is negative. Every feasible middle primary obeys
\[
               a\ge\frac12+\frac1{2\sqrt2}>\frac7{12}.
\tag{8}
\]
To see this, sorting bounds its hard projection by
\(a(\cos z+|\sin z|)\), while its demand is at least
\((1+\cos z+|\sin z|)/2\).

Second, every feasible D obeys
\[
                    D\le\sqrt{q-\tfrac14}-1,
                    \qquad L(0,D)\ge\frac12.
\tag{9}
\]
For a negative angle \(-z\), the shifted hard expression is
\((a-1/2)\cos z+(b-1/2)\sin z\).
Its upper bound, after lifting a to its q-circle, is
\[
 R_q(b)=
 \begin{cases}
 \sqrt{q-(b+1/2)^2}-1,&b\le1/2,\\
 \sqrt{(\sqrt{q-(b+1/2)^2}-1)^2+(b-1/2)^2},&b\ge1/2.
 \end{cases}
\tag{10}
\]
This decreases in b on the sorted frontier: on the second
branch put \(X=\sqrt{q-(b+1/2)^2}\), \(Y=b+1/2\); then
\((R_q^2)'=-2(1-Y/X)\le0\). The first branch decreases
directly, and the branches agree. A positive quarter is
bounded by the same R_q. Thus \(D\le R_q(0)\), proving (9).

## 3. A positive AB difference contracts B directly when A is above T

Suppose \(d>0\) and \(\gamma=\theta_A-\theta_T\ge0\).
Then \(u=\gamma+d\le.7<\pi/4\). Keep A fixed and put
\[
                   Y_0=2-Y_A=\frac32-b_A> .6,\qquad
                   X_0=1+D_T\sec\gamma+Y_0\tan\gamma.
\tag{11}
\]
At A's frame this is the exact BT hard contact and gives
\(b_B'=1-b_A\), so AB is aligned and active. We prove that
its squared corner norm is strictly smaller than the original
B corner norm.

Abbreviate \(X=X_B,Y=Y_B,c=\cos d,s=\sin d,v=1-c\), and
\(a=1+\tan\gamma\). Equation (4) and the original BT contact
inequality give, respectively,
\[
\begin{aligned}
 Y_0&\le\widehat Y:=Xs+Yc+v-s,\\
 X_0&\le\widehat X:=Xc-Ys+av.
\end{aligned}
\tag{12}
\]
For the second comparison, substitute
\[
 D_T\le(X-1)\cos(\gamma+d)-Y\sin(\gamma+d)
\]
and the first comparison into (11). Both comparison coordinates
in (12) are positive, since \(X_0\ge1+D_T\ge3/2\) and
\(Y_0>.6\).

Direct expansion gives
\[
\begin{aligned}
 \frac{\widehat X^2+\widehat Y^2-X^2-Y^2}{2v}
   &=A_xX+A_yY+1-s+\frac{a^2v}{2},\\
 A_x&=\tan\gamma\,c+s-1
        =\frac{\sin(\gamma+d)}{\cos\gamma}-1<0,\\
 A_y&=-as+c-c\cot(d/2)<0.
\end{aligned}
\tag{13}
\]
Here \(\gamma+d<\pi/4\), \(\gamma\ge0\), and
\(\cot(d/2)>1\). Since \(X,Y\ge1/2\), the right side is
at most its value at the dummy corner \(X=Y=1/2\).

For that dummy corner the comparison coordinates are
\[
       \widehat X_{\rm d}=\tfrac12(c-s)+av,\qquad
       \widehat Y_{\rm d}=1-\tfrac12(c+s).
\tag{14}
\]
Both are strictly between zero and one half. The assertion
for \(\widehat Y_{\rm d}\) is immediate. For the other one,
\[
 a=1+\tan\gamma
   \le1+\tan(\pi/4-d)=\frac{2c}{c+s},
\]
and
\[
 (c+s)\left(1-c+s-\frac{4c(1-c)}{c+s}\right)
       =s-(1-c)(2c-1)>0.
\tag{15}
\]
The final inequality uses \(0<1-c<s\) and \(2c-1<1\).
Thus the dummy squared norm in (14) is less than \(1/2\).
Equations (12)--(15) prove
\[
                         X_0^2+Y_0^2<X_B^2+Y_B^2\le q.
\tag{16}
\]

The new point is sorted: \(X_0\ge3/2>\sqrt{Q/2}\), so (16)
forces \(Y_0<X_0\). It has primary at least one, hence the
true core. This is a strict contraction of the actual B
circle, with no primary lift. It therefore retains any
inherited strict B loss as well.

## 4. A negative AB difference moves B upward through negative hard quarters

Suppose \(d<0\) and \(\theta_B<\theta_T\). Keep A and T
fixed and increase the B frame up to
\[
                         \theta_{\rm end}=\min(\theta_A,\theta_T).
\tag{17}
\]
We show that a feasible descendant exists there with strict
B-circle loss. Throughout the open portion before (17), write
\[
 r=\theta_A-\theta_B>0,\quad
 z=\theta_T-\theta_B>0,\quad
 k=\frac12-b_A>-\frac25,\quad D=D_T.
\]
The two constraints are
\[
 -X\sin r+Y\cos r\ge k+\cos r,\qquad
 X\cos z+Y\sin z\ge D+\cos z+\sin z.
\tag{18}
\]
The first, in original coordinates, implies \(b_B>1-b_A>.1\).
Thus the transverse floor is strict everywhere in this
feasible region. The primary core is strict by (8).

Minimize \(X^2+Y^2\) over the compact feasible set consisting
of the frame interval from the original B frame to (17),
the sorted corner constraints, (18), and the original B
circle ceiling. We check that a minimizer cannot have a
frame strictly below (17).

If both contacts are active and \(X>Y\), differentiate them
with respect to the increasing B frame. Their determinant
is \(-\cos(r-z)\ne0\), and direct elimination gives
\[
 \frac12\frac{d}{d\theta_B}(X^2+Y^2)
 =-\frac{(X-Y)\sin z\sin r+
                   X\cos r(\cos z-\sin z)}{\cos(r-z)}<0.
\tag{19}
\]
All circle, floor and sorting constraints persist locally.
The same contact path is admissible at \(X=Y\). To see the
sorting direction there, first follow the AB contact along
the diagonal. Its common coordinate is
\[
                    \ell(r)=\frac{k+\cos r}{\cos r-\sin r},
 \qquad
 \ell'(r)=\frac{1+k(\cos r+\sin r)}
                         {(\cos r-\sin r)^2}>0.
\tag{20}
\]
As the frame increases, this diagonal coordinate decreases.
At a double contact \(\ell>1\), by the second inequality of
(18), so that diagonal move makes the BT constraint strictly
worse. Restoring BT while retaining AB adds a positive multiple
of \((\cos r,\sin r)\). Since \(\cos r>\sin r\), the double-contact
path therefore enters the strictly sorted side. Formula (19)
still makes its circle strictly decrease.

If only AB is active at a minimum for the fixed frame, its
least-norm sorted point is diagonal: lowering X toward Y
improves AB, after which both coordinates decrease to equality.
Equation (20) gives a feasible strict decrease as the frame
increases; the BT slack persists.

If only BT is active at a minimum, the least-norm point is
\[
 (X,Y)=(D+\cos z+\sin z)(\cos z,\sin z).
\tag{21}
\]
A diagonal point cannot be a minimum with AB slack, since
the direction \((\sin z,-\cos z)\) retains BT, enters the
sorted side and decreases the norm. The transverse floor
was already excluded by (18). The norm in (21) is
\((D+\cos z+\sin z)^2\), which strictly decreases as z
decreases. Finally, if both contacts have slack, the corner
can be decreased at the same frame.

These alternatives exclude every minimum before (17).
They also show that the minimum at (17) is strictly smaller
than the original B corner value: otherwise the original
feasible point would itself be a minimum at an earlier frame.
This proves the claimed strict descent.

If (17) is A's frame, AB is now aligned, with transverse
sum at least one. If (17) is T's frame strictly below A,
apply the ordinary rotated-cap comparison of Section 2:
the B hard angle increases from zero to
\(\theta_A-\theta_T\), while its negative AB difference
vanishes. It gives a B point at A's frame with AB sum one
and strict circle loss. Thus every \(d<0\) aligns AB at
A's frame, including the case where the original B frame
was below T. If the original B hard angle was already
nonnegative, only this ordinary rotated-cap comparison
is needed.

## 5. The remaining positive AB difference

Suppose \(d>0\). If \(\theta_A\ge\theta_T\), Section 3 applies.
If \(\theta_B\le\theta_G\), the ordinary increasing-cap
comparison (7) moves A to B's frame with a strict A loss.
This uses only nonnegative GA quarter angles; it requires
no H/D order.

Under (1), the only remaining case is
\[
                \theta_A<\theta_T\le\theta_G<\theta_B.
\tag{22}
\]
First move A upward to G, keeping B fixed. Put
\(r=\theta_G-\theta_A>0\). For a positive AB difference x,
its exact demand on b_A is
\[
 m(x)=\frac12+(\tfrac12-a_B)\sin x+(\tfrac12-b_B)\cos x.
\]
On the whole interval traversed,
\[
 -m'(x)=(a_B-\tfrac12)\cos x+(\tfrac12-b_B)\sin x
       <\sqrt{(.915)^2+(.5)^2}<\frac{21}{20}.
\tag{23}
\]
If \(b_B\ge1/2\), the bound follows already from
\(a_B-1/2<.915\); otherwise apply Cauchy's inequality.
The primary is positive by (8). Choose the new tangent
to be the larger of its old value and the final AB demand.
Its increase is at most \((21/20)r\).

Meanwhile its GA transverse cap increases by more than
\((9/8)r\), by (7). Hence the final required tangent is
strictly below that cap, with reserve greater than
\((3/40)r\). Choose its primary just below its q-circle.
This preserves GA and AB and gives strict A-circle loss.
The point is strictly sorted, because a positive hard cap
has primary corner at least \(1+D_G\ge3/2\).

Now A is at G, which is at or above T by (1), while B remains
above A. Section 3 moves B down to that frame with a strict
B-circle loss. Thus all positive AB differences are covered.
Every common frame constructed so far is one of the original
A,B,G,T frames or lies in their interval.

## 6. Clamp a common frame into the G/T interval

It remains possible that the common frame lies above G
or below T. The direct hard inequalities and AB now give
a transverse sum at least one.

For a negative hard quarter \(-z\), put
\[
 C=D+\cos z+\sin z,\quad w=\sqrt{q-C^2},
\quad X=C\cos z-w\sin z,\quad
 M=C\sin z+w\cos z.
\tag{24}
\]
The sorted transverse cap is
\[
                    \overline M(z,D)=\min\{M(z,D),\sqrt{q/2}\}.
\tag{25}
\]
Indeed \(C\ge3/2>\sqrt q\sin z\), so M is the upper
circle intersection. If that intersection is past the
diagonal, the diagonal itself is feasible and is the
largest sorted transverse coordinate.

On a feasible interval \(0\le z\le r\), the radical in (24)
is real because C increases. Also \(M\ge1/2\) throughout.
At zero this follows from (9), and at r from original
feasibility. Between them M has at most one critical point,
a maximum, since
\[
 M_z=X\left(1-\frac{\cos z-\sin z}{w}\right),\qquad
 w^2-(\cos z-\sin z)^2
             =q-D^2-2D(\cos z+\sin z)-2
\tag{26}
\]
has strictly decreasing sign.

Where the cap in (25) is not diagonal, \(X\ge M\), and
the exact identity \(w=M\cos z-X\sin z\) gives
\[
                    M_z\le X-1<\frac{183}{200}=.915.
\tag{27}
\]
The upper bound uses \(M\ge1/2\) and \(X^2+M^2=q\).
On a diagonal portion \(\overline M_z=0\), so the same
upper bound holds. Integrated comparisons extend over
transitions and any radical-zero endpoint by continuity.

Suppose the common frame is \(r>0\) above G, and put
\(\eta=\theta_G-\theta_T\ge0\). The original two transverse
corners give
\[
                 \overline M(r,D_G)+L(\eta+r,D_T)\ge2.
\tag{28}
\]
The positive cap stays at least one half while the common
frame moves down. From (7),(27),
\[
             L(0,D_G)+L(\eta,D_T)
                    >2+\left(\frac98-\frac{183}{200}\right)r
                     =2+\frac{21}{100}r.
\tag{29}
\]
Each endpoint cap is less than
\(\sqrt{Q-9/4}<1.291\), so each is greater than .709.
Choose transverse corners strictly below these two caps
whose sum is two. Their q-circle primaries are strictly
sorted and exceed one, since their positive hard caps have
primary corners at least \(1+D\ge3/2\).

At the endpoint frame G both hard inequalities have strict
slack. Decrease both primaries slightly. This leaves AB
active and gives strict losses in both circles. The same
argument, with the two sides reversed, moves a common
frame below T up to T. All constructed frames remain in
the original full span.

If a common frame was already between T and G, both hard
quarters are nonnegative. Any transverse sum greater than
one can then be normalized by lowering one middle tangent;
this improves its hard cap and circle and retains sorting
and its strict primary core.

## 7. Other AB owner and inherited strictness

For AB2 interchange A with B and G with T and reverse
the frame direction in this local four-anchor argument.
Condition (1) becomes the same ordered intermediate
condition. Undoing that formal relabeling changes only
the original A/B data; H,D,E and the actual G/T data are
never reflected or re-signed by the construction.

The norm contraction in Section 3 and the compact descent
in Section 4 strictly decrease the actual changed circle.
An ordinary positive-cap reconstruction retains strict
loss through its strict cap gap. The partial move in
Section 5 recreates a strict loss at its changed middle
point, and the final common-frame clamp recreates strict
losses at both. Unchanged middle points retain their
actual circles. Thus earlier A and B losses survive
separately, as claimed in Section 1.

This gives (3) under exactly the stated direct-quarter
owners, normal intermediate signs and ordered intermediate
frames. No H/D/E ordering, angular mesh, state enumeration,
numerical acceptance result, Lean compilation or CI is used.
