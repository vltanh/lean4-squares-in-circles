# The complete actual-four-chain domain: a coupled endpoint budget

This note specifies the first whole domain requested by
[the roadmap](PROOF_PLAN.md), and proves two necessary inequalities on
that unchanged domain. It does **not** prove its impossibility. In
particular, the all-nine implication at the end remains open and G3 is
not passed by this note. No Lean build, numerical search or certificate
replay is used.

## 1. Fixed domain and intended conclusion

Let

\[
 Q=\frac{1105}{256},\qquad r=\frac{\sqrt{1105}}{16}.
\]

There are nine original unit squares

\[
 S_i=c_i+[-1/2,1/2]u_i+[-1/2,1/2]v_i,
 \qquad i=0,\ldots,8,
\]

with independent orthonormal frames. Every one of their 36 corners has
norm at most \(R<r\). Every one of the 36 unordered pairs has disjoint
open interiors. Choose an orthonormal coordinate frame in which
\(S_0,S_1,S_2,S_3\) form an actual horizontal projection chain. Thus,
writing \(c_i=(x_i,y_i)\) and

\[
 h_i=\frac{|e_x\cdot u_i|+|e_x\cdot v_i|}{2},
\]

its three gaps are

\[
 \delta_i=x_{i+1}-x_i-h_i-h_{i+1}\ge0,
 \qquad i=0,1,2.
 \tag{1}
\]

The five outsiders are exactly \(S_4,\ldots,S_8\); none is discarded.
The intended theorem is that this full domain is empty. It would suffice
to prove that some four originals in some direction meet the weighted
endpoint criterion in [the proof draft](PROOF.md), or that three whole
originals lie beyond a line at distance \(7/16\) from the disk center.
Both alternatives allow different labels and a different direction from
those in (1).

All statements below also apply to \(R\le r\), unless a strict inequality
is explicitly attributed to \(R<r\).

**Two-endpoint version.** The budget in Section 3 and the band in
Section 4 in fact require only two of the original squares, labelled
0 and 3, such that

\[
 L=x_3-x_0-h_0-h_3\ge2.
\]

For that version put \(E=L-2\) and \(U=h_0+h_3-1\), without assuming
that either inner main exists. Then \(x_3-x_0=3+U+E\), so the center
bound gives the same endpoint localization, \(U+E<1/30\), and
\(h_0,h_3<8/15\). These are all the hypotheses used in Section 3.
In Section 4 the estimates \(a,d<61/60\), together with
\(a+d=L\ge2\), give \(a,d>59/60\); all pair-cap applications remain
unchanged. Thus both conclusions hold for the same seven other
originals in this broader setting. For example, the outer-actual,
cone-middle configuration of [the foundation, C.2](FOUNDATION.md)
supplies \(L\ge2+\eta_B+\eta_C\), so it also inherits these two
conclusions. This extension does not assert a closure of that domain.
The fixed nine-square research domain of this note remains the one
specified in (1).

## 2. Keep the entire actual-chain surplus

Put

\[
 e_i=h_i-\frac12,\qquad
 U=e_0+e_3,\qquad
 E=2e_1+2e_2+\delta_0+\delta_1+\delta_2,
 \qquad S=|y_0|+|y_3|.
 \tag{2}
\]

These quantities are nonnegative. Telescoping gives the exact identities

\[
 x_3-x_0=3+U+E,
 \qquad
 L:=x_3-x_0-h_0-h_3=2+E.
 \tag{3}
\]

The universal center estimate is

\[
 |c_i|\le\sqrt{R^2-\frac14}-\frac12<\frac{91}{60}=:\rho.
 \tag{4}
\]

Indeed the greatest squared corner norm equals
\(|c_i|^2+1/2+|c_i\cdot u_i|+|c_i\cdot v_i|\), which is at least
\(|c_i|^2+|c_i|+1/2\). The strict rational comparison in (4) follows
from \((121/60)^2-(Q-1/4)=31/57600>0\).
Consequently

\[
 U+E<\frac1{30},\qquad
 -\rho<x_0<-\frac{89}{60},\qquad
 \frac{89}{60}<x_3<\rho,
 \tag{5}
\]

and

\[
 \frac12\le h_0,h_3<\frac8{15},\qquad
 \frac12\le h_1,h_2<\frac{31}{60}.
 \tag{6}
\]

The quantity \(E\) includes every actual projection gap. Replacing it
by a smaller inset-width reserve loses information needed by the
endpoint criterion.

## 3. A transverse budget for the same endpoints

The following strengthens the budget that keeps only inner inset excesses:

\[
 \boxed{\quad
 S+\frac{37}{50}U+\frac{32}{9}E\le\frac18.
 \quad}
 \tag{7}
\]

It is strict when \(R<r\). At \(R\le r\), equality in (7) forces
\(U=E=0\), hence all four main halfwidths equal \(1/2\) and all three
actual gaps vanish.

Here is a full scalar proof. Put
\(X_i=|x_i|\), \(Y_i=|y_i|\), and
\(k_i=\sqrt{1/2-h_i^2}\) for \(i=0,3\).
Equation (5) and the center bound give
\(Y_i^2<\rho^2-(89/60)^2=1/10\), so \(X_i>Y_i\).
An outward-quadrant corner of a square has unsigned offsets either
\((h_i,k_i)\) or \((k_i,h_i)\). The latter order has the smaller
norm when \(X_i>Y_i\), and therefore

\[
 (X_i+k_i)^2+(Y_i+h_i)^2\le R^2.
 \tag{8}
\]

The triangle inequality applied to these two nonnegative corner vectors,
together with (3), yields

\[
 4R^2\ge
 (2+E+h_0+k_0+h_3+k_3)^2+(S+h_0+h_3)^2.
 \tag{9}
\]

On \(1/2\le h\le8/15\), concavity gives

\[
 h+\sqrt{1/2-h^2}
 \ge1-\frac{73}{1000}\left(h-\frac12\right).
 \tag{10}
\]

The two sides agree at \(h=1/2\). At \(h=8/15\) the comparison is
\(\sqrt{97/450}\ge13927/30000\), whose squared difference is
\(38671/900000000>0\). This proves (10) on the entire interval.
Hence

\[
 4R^2\ge(4+E-73U/1000)^2+(S+1+U)^2.
 \tag{11}
\]

Suppose the left side of (7) is at least \(1/8\). Then

\[
 S+1+U\ge\frac98+\frac{13}{50}U-\frac{32}{9}E>0.
\]

Positivity follows from \(E<1/30\); its right side exceeds
\(9/8-16/135=1087/1080\). Squaring is therefore legitimate, and
(11) gives

\[
\begin{aligned}
4R^2
&\ge(4+E-73U/1000)^2+
 (9/8+13U/50-32E/9)^2\\
&=4Q+\frac{U}{1000}
 +(E-73U/1000)^2+(13U/50-32E/9)^2.
\end{aligned}
 \tag{12}
\]

The added terms are nonnegative. For \(R<r\), (12) is already a
contradiction. For \(R\le r\), it forces \(U=0\) and then \(E=0\).
Equation (11) now gives \(S\le1/8\). This proves (7) and its equality
assertion, with all endpoint-tilt and actual-gap contributions retained.

## 4. An exact central band forced by the pair caps

Define the endpoint inward distances

\[
 a=-x_0-h_0,\qquad d=x_3-h_3.
\]

By (3), \(a+d=2+E\). The actual chain and (4) also give

\[
 \frac{59}{60}<a,d<\frac{61}{60}.
 \tag{13}
\]

For example,
\(a=h_3+2h_1+2h_2+\sum\delta_i-x_3>5/2-\rho=59/60\);
the other lower bound is reflected, and the upper bounds use
\(h_0,h_3\ge1/2\).

Set

\[
 p=\frac{46a-211/4}{27/2},\qquad
 q=\frac{211/4-46d}{27/2},\qquad
 \tau=q-p=1-\frac{92}{27}E.
 \tag{14}
\]

Apply the physical weighted two-square cap to \((S_0,S_j)\) in
horizontal direction and to \((S_3,S_j)\) in the opposite direction.
For every \(j=1,2,4,5,6,7,8\) it gives

\[
 x_j+h_j\ge p,\qquad x_j-h_j\le q.
 \tag{15}
\]

Both inequalities are strict for \(R<r\). Thus every one of the seven
remaining originals has its horizontal projection intersecting the
**same** interval \([p,q]\), whose width obeys

\[
 \frac{359}{405}<\tau\le1,
 \qquad
 -\frac{451}{810}<p<-\frac{359}{810},\qquad
 \frac{359}{810}<q<\frac{451}{810}.
 \tag{16}
\]

This statement retains the original physical squares; it does not
replace them by their projections. Since each projection has length at
least one, (15)--(16) also imply that each intersects at least one of the
two vertical lines \(x=p\) and \(x=q\). The sections on those lines need
not have length one, and their vertical projections need not separate.
Consequently this line-incidence fact alone supplies no packing count.

For any two distinct labels \(j,k\) among these seven, adding the
corresponding inequalities in (15) gives

\[
 x_k-x_j-h_j-h_k\le\tau.
 \tag{17}
\]

Equivalently, a strict counterexample must satisfy

\[
 x_k-x_j-h_j-h_k
 <1-\frac{92}{27}E
 \quad\text{for every such ordered pair }(j,k).
 \tag{18}
\]

Finding even one ordered pair that reverses (18) closes the domain:
with the main endpoints it gives

\[
 46(2+E)+\frac{27}{2}
       (x_k-x_j-h_j-h_k)\ge\frac{211}{2}.
\]

An actual three-chain among the outsiders is a sufficient special case.
The required pair span may be smaller than one; all positive main-chain
gaps in (2) decrease its threshold by exactly \(92E/27\).

### 4.1. Seven physical squares can satisfy the band and strip bounds

The central band and outsider strip alone cannot give a capacity of six.
Here is an exact obstruction to that relaxation; no outer endpoint
squares are supplied by this construction.

Start with seven aligned unit squares at

\[
 (0,-1),\ (0,0),\ (0,1),\qquad (\pm1,\pm\tfrac12).
\]

They have disjoint open interiors: centers in the same vertical column
have height gaps at least one, and distinct columns have horizontal
gaps at least one. Rotate all centers and frames by the orthonormal
frame

\[
 u=(99,20)/101,\qquad v=(-20,99)/101,
\]

and then multiply every center by \(t=1001/1000\), leaving the frames
fixed. Every original center displacement in a separating direction is
multiplied by \(t>1\), while both support halfwidths stay fixed. Thus
the resulting seven closed squares are pairwise disjoint. Rotation
does not change corner norms. In the common physical frame, their
greatest squared corner radius is

\[
 (t+\tfrac12)^2+(\tfrac t2+\tfrac12)^2
 =\frac54t^2+\frac32t+\frac12
 =\frac{13016005}{4000000}<4<Q.
 \tag{19}
\]

The central-column squares have the smaller bound
\(t^2+t+1/2\). All seven have horizontal halfwidth
\(h=119/202\), and their largest horizontal center magnitude is

\[
 X=\frac{109}{101}t=\frac{109109}{101000}<\frac{13}{12}.
\]

By central symmetry, their greatest left projection endpoint and least
right projection endpoint are respectively \(X-h\) and \(-X+h\).
Since

\[
 X-h=\frac{49609}{101000}<\frac{99}{200},
 \tag{20}
\]

every square satisfies, strictly,

\[
 |x|<\frac{13}{12},\qquad
 x-h<\frac{99}{200},\qquad x+h>-\frac{99}{200}.
\]

Thus seven closed-disjoint original squares can fit below the target
radius while their projections all meet the same band of width
\(99/100<1\), with all centers in the established outsider strip.
The example does not satisfy or refute the full domain of Section 1:
it supplies no two outer endpoints and no endpoint-to-original
nonoverlap conditions. A valid capacity argument must retain those
physical conditions, beyond their band and strip consequences. This
obstruction to the relaxation does not close G3.

## 5. The precise surviving problem

No argument above proves that a pair violating (18) exists. The
unchanged surviving domain has all nine independent frames, all 36
corner bounds at one radius \(R<r\), all 36 physical nonoverlap
conditions, the three actual-chain inequalities (1), and the strict
endpoint-span restrictions (18). It also necessarily obeys (7),
(13)--(16), and the retained outsider-strip, side-capacity and inner
clearance theorems.

To close the planned route, one must prove that this full predicate
forces either an endpoint criterion after another label/direction
choice, or three whole originals beyond a \(7/16\) cap line. In
particular, a proof may not turn a short section on \(x=p\) or \(x=q\)
into full projection separation, drop either extra original, or discard
the complement of a main-height or orientation guard. The coupled
budget and band above are consequences available to that proof; they
are not the missing all-nine implication.
