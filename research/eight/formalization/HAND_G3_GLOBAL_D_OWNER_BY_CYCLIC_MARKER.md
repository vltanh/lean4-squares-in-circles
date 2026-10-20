# The D sign and every original DE owner are forced globally

## 1. Result and dependency order

Assume the actual G0--G2 seven-cycle geometry, its common real frame
spread less than \(7/10\), the containing squared radius
\(q\le Q=9789/2500\), and the reflection normalization \(u_E\le0\).
Then
\[
\boxed{\text{every feasible original DE axis belongs to }\{2,3\}.}
\tag{1}
\]
Moreover, the same argument proves the strict sign \(u_D<0\).
Original axes are numbered from zero. The conclusion excludes an
original axis 0 or 1 even when it is tied with another feasible axis.

There is no hypothesis on the mismatch sum S, no tangent cut, no
prescribed sign on D or on any other zero-edge role, no quarter or
mixed owner input, and no choice of a preferred tied witness. In fact
the local estimate below needs only that the edge is a quarter edge
whose target has nonpositive signed transverse coordinate.

The proof uses the unchanged common G1 marker and a closed real frame
return path. Its local quantitative conclusion is
\[
\boxed{\phi_{DE}+\ell_D-\ell_E+
       \frac9{50}h(|d_{DE}|)>1}
\tag{2}
\]
for every putative forbidden DE witness on the boundary cycle at Q,
where \(h(x)=(\sin x+\cos x-1)/2\).
Every other edge has the actual G1 lower bound with the opposite
charge sign. These seven estimates contradict the full angular budget.

This closes the D-sign subgate and the DE part of G6 globally. It does not prove the BT owner
restriction, a bound on S, the remaining global tangent cuts, or the
unrestricted sharp radius theorem.

## 2. The common boundary marker and elementary bounds

First work on the G0 boundary neighbor cycle at Q. An unsigned
canonical center is \((a,b)\), with \(0\le b\le a\), and its signed
own-frame center is \((a,-\sigma b)\).
Each center is on the outer curve
\[
(a+1/2)^2+(b+1/2)^2=Q
\tag{3}
\]
or on the actual core side/corner curve. Set
\[
L=\frac{447}{800},\qquad U=\frac{283}{200},\qquad
a_0=\sqrt{Q-\frac14}-\frac12,\qquad
c_0=\sqrt{Q/2}-\frac12.
\]
The geometric bounds are
\[
a>L,\qquad a<U,\qquad |(a,b)|<U,\qquad 0\le b<\frac9{10}.
\tag{4}
\]
The center-norm bound is proved directly from corner containment in
[the center-norm note](HAND_G3_CENTER_NORM_AND_HIGH_TAIL_DIRECTIONS.md),
Section 1. A core boundary center has \(a\le7/12\), and if
\(b\le1/2\) then \(a=7/12\). Both statements include the side/corner
junction.

Use precisely the unsigned G1 marker from
[the exterior frame proof](../HAND_EXTERIOR_FRAME_CONCENTRATION.md):
\[
\begin{aligned}
F_C(a,b)&=7.506931(7/12-a)+1.077372b,\\
F_L(a,b)&=.403875(a-a_0)+1.089065b,
 &&0\le b/a\le1/4,\\
F_M(a,b)&=-2.143075+1.489593a+1.580219b,
 &&1/4\le b/a\le3/7,\\
F_H(a,b)&=\pi/4-.569472(a-c_0)+.390886(b-c_0),
 &&3/7\le b/a\le1.
\end{aligned}
\tag{5}
\]
Every terminating decimal is an exact rational. The signed marker is
\(\ell=\sigma F\). At an outer-chart junction choose a containing
marker once for that vertex and use the same value on both incident
edges. All bounds used here hold for either choice.

The whole-chart proof in
[the zero-primary exclusion](HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md),
Section 3, supplies
\[
F_O\ge\frac45b,\qquad
F_O\le\frac25(a-a_0)+\frac{111}{100}b
      \le\frac{111}{100}b,
\tag{6}
\]
for each outer marker. The core formula immediately gives
\(F_C\ge(4/5)b\), and, when \(b\le1/2\),
\(F_C=1.077372b\le(111/100)b\). Hence, on all radial kinds,
\[
\boxed{F\ge\frac45b\ge0,\qquad
 b\le\frac12\ \Longrightarrow\ F\le\frac{111}{100}b.}
\tag{7}
\]
The upper bound in (6) remains available on every outer state even
when \(b>1/2\).

We also need the uniform bound
\[
\boxed{F<\frac45.}
\tag{8}
\]
For core states, \(b\le a\) and \(a>L\) give
\[
F_C<
7.506931(7/12-L)+1.077372L
=\frac{1887664781}{2400000000}<\frac45,
\tag{9}
\]
whose last reserve is \(32335219/2400000000\).
For L, \(a-a_0\le0\) and \(b\le a/4<U/4\), so
\[
F_L<1.089065\,U/4=\frac{61641079}{160000000}<\frac45.
\]
For M, set \(v_1=1.489593\), \(v_2=1.580219\). Circle support and
\(\sqrt{v_1^2+v_2^2}<109/50\), \(R=\sqrt Q<2\), give
\[
F_M\le-2.143075+R\sqrt{v_1^2+v_2^2}
                  -\frac{v_1+v_2}{2}
<\frac{682019}{1000000}<\frac45.
\]
The asserted norm-square reserve is
\[
(109/50)^2-v_1^2-v_2^2
=\frac{3642060639}{100000000000}>0.
\]
Finally (3) and \(a\ge b\) imply \(a\ge c_0\), \(b\le c_0\).
Thus \(F_H\le\pi/4<11/14<4/5\). This proves (8) on all charts
without subdividing any chart.

For \(x\in[0,7/10]\), write \(c=\cos x\), \(r=\sin x\). We use
\[
c\ge\frac34,\qquad 0\le r\le\frac{13}{20},\qquad
c^2+r^2=1,\qquad h(x)\ge0,\qquad \frac\pi2>\frac{157}{100}.
\tag{10}
\]
The sine upper bound follows from its alternating Taylor estimate at
\(7/10\); all other trigonometric comparisons below use the same
elementary Taylor inequalities or \(1-c=r^2/(1+c)\).

## 3. The two original forbidden DE projections

Write D as \((a,-\sigma b)\), where \(\sigma\in\{-1,1\}\), and
write E as \((A,B)\), where \(B\ge0\), using \(u_E\le0\).
Set
\[
d=d_{DE},\quad |d|<7/10,\quad
\phi=\pi/2+d,\quad c=\cos d,\quad s=\sin d,
\quad W=\frac{1+c+|s|}{2},\quad\beta=\frac9{50}.
\tag{11}
\]
The original axes 0 and 1 have projections
\[
P_0=\sigma b+A c-Bs,\qquad
P_1=A+a s+\sigma b c.
\tag{12}
\]
Thus a retained forbidden witness satisfies \(P_0\ge W\) or
\(P_1\ge W\), with its original weak inequality. These formulas
can also be read directly by rotating E into the D frame through
\(\pi/2+d\), or D into the E frame through its negative.

Because \(\ell_E=-F_E\), the expression to bound is
\[
C=\frac\pi2+d+\sigma F_D+F_E+\beta h(|d|).
\tag{13}
\]
We prove \(C>1\) for the four combinations of the original axis
and D sign. If \(b=0\), either sign representation is covered.

## 4. Original axis 0, negative D sign

Suppose \(\sigma=-1\) and \(P_0\ge W\). By (4) and \(W\ge1\),
\[
b\le A c-Bs-W\le |(A,B)|-1<U-1<\frac12.
\]
Thus (7) gives \(F_D\le\lambda b\), where
\(\lambda=111/100\). Combining (7), (12), and (13),
\[
\begin{aligned}
C
&\ge\frac\pi2+d+\beta h+\lambda W-\lambda cA
                      +\left(\frac45+\lambda s\right)B\\
&>\frac\pi2+d+\beta h+\lambda W-\lambda Uc.
\end{aligned}
\tag{14}
\]
The discarded B coefficient is positive: by (10) it is at least
\(4/5-(111/100)(13/20)=157/2000\).

The last expression in (14) equals
\[
f_-(d)=\frac\pi2+d+\frac{93}{200}
                   -\frac{18513}{20000}\cos d
                   +\frac{129}{200}|\sin d|.
\tag{15}
\]
For \(d\ge0\), this is at least
\(\pi/2-9213/20000>22187/20000>1\).

For \(d=-x\), \(0\le x\le7/10\), use
\(\cos x\le1-x^2/2+x^4/24\) and
\(\sin x\ge x-x^3/6\). Equations (10) and (15) give
\[
\begin{aligned}
f_-(-x)
&>\frac{22187}{20000}-\frac{71}{200}x
 +\frac{18513}{40000}x^2
 -\frac{43}{400}x^3-\frac{6171}{160000}x^4\\
&\ge\frac{22187}{20000}-\frac{71}{200}x+\frac9{25}x^2.
\end{aligned}
\tag{16}
\]
Indeed, after using \(x\le7/10\), the exact available quadratic
coefficient is \(5898821/16000000\), exceeding \(9/25\) by
\(138821/16000000\). Completing this one square gives
\[
f_-(-x)>
\frac{22187}{20000}-\frac{5041}{57600}
=1+\frac{31439}{1440000}>1.
\tag{17}
\]
This proves (2) for original axis 0 with negative D sign.

## 5. Original axis 0, positive D sign

Now suppose \(\sigma=1\) and \(P_0\ge W\). Both markers in
(13) are bounded below using (7). Also
\[
b+B\ge W-Ac+(1+s)B>W-Uc,
\]
since \(c>0\) and \(1+s>0\). Therefore
\[
C>\frac\pi2+d+\beta h+\frac45(W-Uc)
 =f_+(d),
\tag{18}
\]
where
\[
f_+(d)=\frac\pi2+d+\frac{31}{100}
                   -\frac{321}{500}\cos d
                   +\frac{49}{100}|\sin d|.
\tag{19}
\]
For \(d\ge0\), \(f_+(d)\ge\pi/2-83/250>619/500>1\).

For \(d=-x\), the function
\[
\frac\pi2-x+\frac{31}{100}
                    -\frac{321}{500}\cos x+\frac{49}{100}\sin x
\]
is strictly decreasing on \([0,7/10]\), because its derivative is
\[
-1+\frac{321}{500}\sin x+\frac{49}{100}\cos x<0.
\]
The unit-circle support establishing this sign has squared reserve
\[
1-(321/500)^2-(49/100)^2=\frac{43467}{125000}>0.
\]
Its value at \(7/10\), bounded with the fourth-degree cosine upper
bound, cubic sine lower bound, and \(\pi/2>157/100\), is greater than
\[
\begin{aligned}
&\frac{157}{100}-\frac7{10}+\frac{31}{100}
-\frac{321}{500}
 \left(1-\frac12(\frac7{10})^2+\frac1{24}(\frac7{10})^4\right)
+\frac{49}{100}
 \left(\frac7{10}-\frac16(\frac7{10})^3\right)\\
&\hspace{20mm}=\frac{120462679}{120000000}
=1+\frac{462679}{120000000}>1.
\end{aligned}
\tag{20}
\]
This proves (2) for original axis 0 with positive D sign.

## 6. Original axis 1, negative D sign

Suppose \(\sigma=-1\) and \(P_1\ge W\), so
\[
A+a\sin d-b\cos d\ge W.
\tag{21}
\]

### 6.1. Nonpositive frame increment

Put \(d=-x\), \(r=\sin x\), \(c=\cos x\). By (4),
\[
bc<U-W-Lr\le U-1-Lr<\frac12c.
\tag{22}
\]
For the last inequality, use \(c\ge1-r^2\):
\[
U-1-Lr-\frac12c
\le-\frac{17}{200}-r\left(L-\frac r2\right)<0,
\]
because \(r\le13/20\). Thus \(b<1/2\), and (7) gives
\(F_D\le\lambda b\), \(\lambda=111/100\).

Feasibility in (21) also forces \(x<1/2\). Indeed \(A\ge W+Lr\),
and the function \(W+L\sin x=1/2+(1/2)\cos x+(1/2+L)\sin x\)
is increasing on \([0,7/10]\). Its derivative is positive by (10).
At \(x=1/2\), the bounds \(\cos x\ge7/8\),
\(\sin x\ge23/48\) give
\[
\frac12+\frac12\frac78+
       \left(\frac12+L\right)\frac{23}{48}-U
=\frac{229}{7680}>0.
\tag{23}
\]
This would contradict \(A<U\).

Set \(v=U-1/2=183/200\), \(w=L+1/2=847/800\).
Equations (13), (21), \(F_E\ge0\), and \(h\ge0\) imply
\[
C>\frac\pi2-x+\frac{\lambda}{c}(W-U+Lr)
 =\frac\pi2-x+\frac\lambda2-\frac{\lambda v}{c}
                                  +\frac{\lambda w r}{c}.
\tag{24}
\]
Since \(x\le1/2\), \(c\ge7/8\), and hence
\[
\frac1c-1=\frac{r^2}{c(1+c)}\le\frac{64}{105}r^2.
\]
Use this bound on the negative term in (24), use \(r/c\ge r\)
on the positive term, and use \(r^2\le x^2\),
\(r\ge x-x^3/6\). It follows that
\[
\begin{aligned}
C
&>\frac{22187}{20000}
 +\frac{14017}{80000}x-\frac{13542}{21875}x^2
                                      -\frac{31339}{160000}x^3\\
&\ge \frac{22187}{20000}+\frac7{40}x-\frac{31}{50}x^2
                                                    -\frac15x^3.
\end{aligned}
\tag{25}
\]
The last cubic is concave on \([0,1/2]\), so its minimum is an
endpoint value. The two endpoint values are \(22187/20000\)
and \(20337/20000\), both strictly greater than one.

### 6.2. Nonnegative frame increment

If \(d\ge1/4\), (8), (13), \(F_E\ge0\), and \(h\ge0\) give
\[
C>\frac{157}{100}+\frac14-\frac45=\frac{51}{50}>1.
\tag{26}
\]
It remains to take \(0\le d\le1/4\). A core state with \(b>1/2\)
cannot satisfy (21): because \(a\le7/12\),
\[
P_1-W<U-\frac12+\frac1{12}\sin d-\cos d
\le\frac{183}{200}+\frac1{48}-\frac{31}{32}
=-\frac{79}{2400}<0.
\tag{27}
\]
Thus D is either outer or core with \(b\le1/2\). In both cases
(6)--(7) give \(F_D\le\lambda b\), \(\lambda=111/100\).
Using \(a,A<U\) in (21), (13) therefore yields
\[
C>\frac\pi2+d+\frac\lambda2
                    -\lambda v\frac{1+\sin d}{\cos d}.
\tag{28}
\]
Here \(c\ge31/32\), so
\[
\frac1c-1\le\frac{1024}{1953}\sin^2d,\qquad
\frac{1+\sin d}{c}
\le(1+d)\left(1+\frac{1024}{1953}d^2\right)
\le1+d+\frac{1280}{1953}d^2.
\]
Consequently
\[
C>\frac{22187}{20000}-\frac{313}{20000}d
                              -\frac{18056}{27125}d^2
\ge\frac{22187}{20000}-\frac1{50}d-\frac23d^2.
\tag{29}
\]
The last expression decreases on \([0,1/4]\); its value at \(1/4\)
is \(63761/60000>1\). This finishes all original axis 1 cases
with negative D sign.

## 7. Original axis 1, positive D sign

If \(\sigma=1\) and \(d\ge0\), (7), (10), and (13) give
\(C\ge\pi/2>1\). Suppose henceforth that \(d=-x\),
\(0\le x\le7/10\), with \(r=\sin x\), \(c=\cos x\).
The original projection \(A-ar+bc\ge W\) and (4) give
\[
bc>W-U+Lr.
\]
Use \(F_D\ge(4/5)b\), \(F_E\ge0\). With
\(\lambda=4/5\), \(v=183/200\), \(w=847/800\), we obtain
\[
C>\frac\pi2-x+\frac\lambda2
                +\lambda\frac{-v+wr}{c}+\beta h(x).
\tag{30}
\]
On the entire interval, the numerator is negative:
\[
-v+wr\le-\frac{183}{200}+\frac{847}{800}\frac{13}{20}
=-\frac{3629}{16000}<0.
\tag{31}
\]
Also \(c\ge3/4\), so
\[
\frac1c\le1+\frac{16}{21}r^2.
\]
Applying this upper bound to the negative numerator in (30) gives
\[
C>\frac\pi2-\lambda(U-1)-x
   +\lambda wr-\lambda v\frac{16}{21}r^2
   +\lambda w\frac{16}{21}r^3+\beta h(x).
\tag{32}
\]
For \(0\le x\le7/10\), use
\[
r\ge x-\frac{x^3}{6}\ge\frac{551}{600}x,\qquad r^2\le x^2,
\]
and
\[
\beta h(x)\ge\frac9{100}
                     \left(x-\frac{x^2}{2}-\frac{x^3}{6}\right).
\]
The positive \(r^3\) term can therefore be bounded by
\((551/600)^3x^3\); the negative quadratic term uses \(r^2\le x^2\).
Equation (32) becomes
\[
C>\frac{619}{500}-\frac{63}{1000}x
       -\frac{4219}{7000}x^2
       +\frac{13916632271}{40500000000}x^3
\ge p(x),
\tag{33}
\]
where
\[
p(x)=\frac{619}{500}-\frac{63}{1000}x-\frac{61}{100}x^2
                                                    +\frac13x^3.
\]
The coefficient reserves in the last comparison are
\[
\frac{61}{100}-\frac{4219}{7000}=\frac{51}{7000}>0,\qquad
\frac{13916632271}{40500000000}-\frac13
=\frac{416632271}{40500000000}>0.
\]
The derivative
\[
p'(x)=-\frac{63}{1000}-\frac{61}{50}x+x^2
\]
is a convex quadratic. Its endpoint values on \([0,7/10]\)
are \(-63/1000\) and \(-427/1000\), so it is negative throughout.
Hence
\[
C>p(7/10)=\frac{757}{750}>1.
\tag{34}
\]
This proves (2) for the final sign/axis combination.

## 8. The same estimates force the D sign

Suppose D has nonnegative signed transverse coordinate; if that
coordinate is zero, choose its positive sign representation. Then
\(\sigma=1\) in (13), so all markers in that expression are
nonnegative. The original forbidden axes 0 and 1 already have
\(C>1\) by Sections 5 and 7.

The two original intended projections are
\[
P_2=a\cos d-b\sin d+B,\qquad
P_3=a+A\sin d+B\cos d.
\tag{35}
\]
If \(d\ge0\), \(C\ge\pi/2>1\) independently of which projection
is feasible. It remains to set \(d=-x\), \(r=\sin x\), \(c=\cos x\).

If \(P_2\ge W\), its inequality \(ac+br+B\ge W\) gives
\[
b+B\ge W-ac+(1-r)b>W-Uc.
\]
Using \(F_D+F_E\ge(4/5)(b+B)\) in (13) gives exactly
\[
C>\frac\pi2-x+\beta h(x)+\frac45(W-Uc)=f_+(-x)>1,
\]
where the last inequality was proved on the full interval in Section 5.

If \(P_3\ge W\), its inequality \(a-Ar+Bc\ge W\) gives
\[
Bc>W-U+Lr.
\]
Now \(F_D+F_E\ge(4/5)B\), so (13) gives exactly the lower
bound (30). All numerator signs, denominator bounds, and the final
cubic comparison in Section 7 apply unchanged. Thus \(C>1\)
also for original axis 3.

Consequently every feasible original witness would have the boosted
bound (2) if \(u_D\ge0\). The next cyclic contradiction excludes
this possibility. No intended owner was assumed before proving this
sign: all four original witnesses were explicitly included.

## 9. Close the cyclic contradiction

Retain any putative forbidden original DE witness. Choose the common
G1 marker once per vertex as in Section 2. The other six original edges
obey the actual G1 pair inequality
\[
\phi_j+\ell_j-\ell_{j+1}-\beta h(|d_j|)
>\frac{8833}{10000}.
\tag{36}
\]
This is the unchanged complete four-type result in
[the exterior frame proof](../HAND_EXTERIOR_FRAME_CONCENTRATION.md);
its least pair constant is the displayed value.

The seven real frame lifts lie in a common interval of length less
than \(7/10\). On that interval, \(h\) of distance is a metric:
h is increasing and concave with \(h(0)=0\). If a middle point lies
between two others, the triangle inequality follows from concavity
and subadditivity; if it lies outside, monotonicity applies to the
longer incident distance. Apply this triangle inequality along the
six-edge return path joining the endpoints of DE. It gives
\[
\sum_{j\ne DE}h(|d_j|)\ge h(|d_{DE}|).
\tag{37}
\]
This is the same closed-tour argument as
[the zero-primary exclusion](HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md),
Section 6.

Summing (2) with (36), the vertex markers cancel exactly, and (37)
implies
\[
1+6\frac{8833}{10000}
<\sum_j\phi_j+\beta h(|d_{DE}|)
                -\beta\sum_{j\ne DE}h(|d_j|)
\le2\pi.
\tag{38}
\]
But
\[
1+6\frac{8833}{10000}-\frac{710}{113}
=\frac{9387}{565000}>0,\qquad 2\pi<\frac{710}{113}.
\tag{39}
\]
This contradiction excludes every forbidden original DE witness.
By Section 8 it also excludes \(u_D\ge0\), proving \(u_D<0\).

## 10. Original centers, ties, and verification boundary

To apply the theorem to the original G0--G2 candidate at \(q\le Q\),
retain the putative forbidden DE witness first, and retain any feasible
original witness on each other edge. The G0 fixed-witness boundary
reduction and radius expansion to Q preserve these chosen weak SAT
inequalities, each square's real frame, and the quarter increments.
Radial changes preserve the signed center ray, so they also preserve
the weak normalization \(u_E\le0\). This is precisely the application
boundary documented for the earlier global zero-primary exclusion in
[its Section 7](HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md).

For the sign conclusion, the same reduction also preserves the
putative weak sign \(u_D\ge0\); retain any original DE witness.
Choose the common G1 marker on that Q-boundary cycle only after the
radial reduction. Sections 2--9 then give a contradiction. No marker
is transferred to another ceiling, and no actual contained center is
silently replaced inside a proof that assumes the original center.

Because the original forbidden witness was retained throughout, a tie
with any other axis does not escape the argument. If a transverse
coordinate is zero, both sign encodings have already been covered.
The core side/corner endpoint and every outer-chart junction satisfy
all bounds used here.

The proof consists of whole-chart marker bounds, the two original
projection identities, four continuous one-variable estimates, and
one complete-cycle return inequality. Exact rational arithmetic checks
verify the displayed endpoint reserves and polynomial coefficients;
no state table, angle mesh, numerical decision certificate, Lean
compilation, or CI is part of this proof.
