# An outside inner unit has a unique signed outward ray witness

**Status: complete hand implication; root and independent full hand audits passed.**
Keep the hypotheses and notation of
`C7_SHARP_BALANCED_RADIAL_TAIL.md`, with the stronger first-coordinate
assumption

\[
1/2\le a\le k=3721/7200,\qquad 2a/3\le b\le a.
\tag{1}
\]

All actual boundary centers have norm less than \(M=91/60\), and
distinct unit-square centers have distance at least one. We prove that
the unit meeting the outgoing center ray of this inner square is the
same unit supplied by the outward middle-face-zone extraction. In the
reflected negative-secondary case this gives a signed tangential bound
which is incompatible with the right-hand excess budget of an enclosed
pair. The asymmetric case in which only the left inner unit is outside
the origin is not discarded.

## 1. All upper and middle ray cases exceed the radius bound

Use the full owner and sign cover of the sharp radial-tail manuscript.
The upward rectangle-owned, upper positive-normal, and leftward
mixed-normal cases all have squared center norm at least

\[
F_U(a,b)=\left(a(1+1/(2b))-1/2\right)^2+(b+1)^2
\ge \frac1{16b^2}+(b+1)^2.
\tag{2}
\]

The last inequality uses \(a\ge1/2\). Put
\(f(b)=1/(16b^2)+(b+1)^2\). For \(0<b\le k<11/20\),

\[
f''(b)=\frac3{8b^4}+2>6.
\]

At \(b_0=3/8\),

\[
f(b_0)=1345/576>7/3,
\qquad f'(b_0)=41/108<2/5.
\]

The quadratic Taylor lower bound and completion of the square give

\[
f(b)>\frac73-\frac1{75}=\frac{58}{25}>M^2.
\tag{3}
\]

These entire upper cases are therefore impossible.

For a positive-quadrant square-owned normal, the middle regime
\(|g|\le1/2\) is also impossible. Indeed
\(\lambda\ge1+1/(2a)\), so

\[
|z_m|\le\frac{a}{2a+1}<\frac{21}{82},
\qquad |z|^2=a^2+b^2\ge\frac{13}{36}.
\]

Consequently

\[
z_n^2>\frac{13}{36}-\left(\frac{21}{82}\right)^2
>\left(\frac{31}{60}\right)^2=(M-1)^2.
\]

Since \(H_T(n)\ge1/2\), the lower normal coordinate of the outer
center is \(H+1/2\ge z_n+1>M\), a contradiction.

## 2. Every surviving ray center lies in the same narrow outward cap

There remain three cases from the sharp-tail cover. Write

\[
B=b(1+1/(2a)),\qquad B_0=B-1/2>0.
\]

### 2.1. A rightward rectangle-owned separator

Here

\[
C_x\ge a+1/2+h\ge a+1,\qquad C_y\ge B-h,
\qquad h\in[1/2,1/\sqrt2].
\tag{4}
\]

The radius bound gives \(h<M-a-1/2\).

### 2.2. A positive-quadrant square-owned normal with \(g>1/2\)

Let \(n=(u,v)\), \(m=(-v,u)\). First,

\[
v<1/40.
\tag{5}
\]

To prove this, \(g>1/2\) implies \(v/u<b/a\le1\), hence
\(0\le v<1/\sqrt2\). Also

\[
M-1/2>H=(a+1/2)u+(b+1/2)v
\ge1-v^2+5v/6.
\]

If \(1/40\le v\le1/\sqrt2\), concavity shows that
\(5v/6-v^2\) is at least the minimum of its two endpoint values.
Both exceed \(1/60\): they are \(97/4800\) and
\(5/(6\sqrt2)-1/2\), respectively. This contradicts
\(M-1/2=61/60\), proving (5).

The lower normal coordinate \(N=H+1/2\) is at least \(a+1\).
For example, \(1-u\le v^2\), \(a+1/2<2\),
\(b+1/2\ge1/2\), and \(v<1/40\) give \(H\ge a+1/2\).
The own tangential coordinate is nonnegative. Since \(n\cdot C\ge
3/2\) and \(|C|<M\), it is less than

\[
\sqrt{M^2-9/4}=\frac{\sqrt{181}}{60}<\frac14.
\]

Therefore the actual center, not just the norm-minimizing candidate,
satisfies

\[
C_x>\frac32(1-1/1600)-\frac1{160}>rac{149}{100}.
\tag{6}
\]

Both own-coordinate increments from the candidate have nonnegative
vertical projection. The coordinate monotonicity in the sharp-tail proof
therefore also gives

\[
C_y\ge B_0.
\tag{7}
\]

### 2.3. A downward mixed-sign square-owned normal

Let \(n=(u,-v)\), \(m=(v,u)\). The positive candidate in the
sharp-tail proof satisfies \((C_*)_x\ge a+1\) and
\((C_*)_y\ge B_0\). Both actual own-coordinate increments
\(\Delta_n,\Delta_m\) are nonnegative. Their horizontal projections
are nonnegative too, so

\[
C_x\ge a+1\ge3/2,
\qquad u\Delta_n+v\Delta_m<1/60.
\]

Here \(v/u<a/b\le3/2\). Thus

\[
C_y=(C_*)_y-v\Delta_n+u\Delta_m
\ge B_0-\frac{v/u}{60}>B_0-\frac1{40}.
\tag{8}
\]

The estimates (4), (6), and (8) prove that every possible ray witness
has \(C_x>149/100\).

## 3. Uniqueness and the signed offset

The far-face extraction supplies a boundary center

\[
C_F=(a+1+\delta,b+t),\qquad \delta\ge0,\quad |t|\le1/2.
\]

It also lies in the cap \(x>149/100\). At most one physical boundary
center lies in that cap. Indeed every point of
\(D_{M^2}\cap\{x\ge149/100\}\) lies in the disk centered at
\((149/100,0)\) of radius

\[
\sqrt{M^2-(149/100)^2}<1/2.
\]

The displayed containment follows by subtracting
\(2(149/100)x-(149/100)^2\) from \(x^2+y^2\).
The cap's diameter is therefore less than one, contradicting the center
separation of two interior-disjoint units if two centers lay there.

Thus the ray witness and the far-face unit are the same actual unit.
Reflect now in the horizontal axis, so the inner center is \((a,-b)\),
and write its extracted far center as

\[
C_F=(a+1+\delta,-b+r).
\]

The reflected versions of (4), (7), and (8) imply, respectively,

\[
\begin{aligned}
r&\le h-b/(2a)<M-a-1/2-1/3\le11/60,\
r&\le1/2-b/(2a)\le1/6,\
r&<1/2-b/(2a)+1/40\le23/120.
\end{aligned}
\]

Hence all cases give the uniform signed bound

\[
\boxed{r<23/120.}
\tag{9}
\]

## 4. Consequence for the right member of an enclosed pair

Use the exact pair notation from
`C7_INNER_PAIR_FAR_FACE_CENTERS.md`:

\[
C_T=(-\alpha,\beta),\qquad C_U=\xi u+\eta v,
\qquad C_R=(\xi+1+\varepsilon)u+(\eta+r)v.
\]

Suppose the right member has \(\xi\ge1/2\). The established
nonparallel angle bound and strict center-diameter bound give

\[
r>\frac12-\frac32\tan(\theta/2)
>\frac12-\frac6{29}=\frac{17}{58}>\frac{23}{120},
\tag{10}
\]

because \(\sin\theta<4/15\) and \(\cos\theta>14/15\).
If \(\eta\ge0\), then the tangential own coordinate of \(C_R\)
is at least \(r>17/58\), whereas its normal coordinate is at least
\(3/2\). This contradicts
\(\sqrt{M^2-9/4}<1/4<17/58\).

The outside-face exclusion in
`C7_INNER_OUTSIDE_FACE_CORNER_EXCLUSION.md` also gives
\(|\eta|<3/8<\xi\), so the ordering of the two own coordinates in
(1) is available. Thus \(\eta<0\). If also
\(-\eta\ge2\xi/3\), Sections 1--3
apply to this actual right inner unit, and (9) contradicts (10).
Consequently the entire right-outside case satisfies

\[
\boxed{-2\xi/3<\eta<0.}
\tag{11}
\]

For completeness, these are exhaustive outside-coordinate alternatives.
The far-face extraction gives \(\alpha,\xi>9/20>3/8\). The
outside-face exclusion therefore forces \(|\beta|,|\eta|<1/2\):
otherwise that secondary coordinate together with the corresponding main
coordinate would violate its conclusion. If both \(\alpha\le1/2\)
and \(\xi\le1/2\), then \(\eta>-1/2\) and \(s>0\) give

\[
\alpha+\xi c-\eta s<\frac{1+c+s}{2},
\]

contradicting the actual pair SAT inequality. Thus at least one main
coordinate is strictly greater than \(1/2\), and the residual cover is
exactly

\[
\begin{cases}
\xi\ge1/2,&-2\xi/3<\eta<0,\\
\xi<1/2,&\alpha>1/2.
\end{cases}
\tag{12}
\]

This is an additional necessary condition, not a completed C7 capacity
theorem. In particular the original inner SAT axis is owned by the left
unit, so one may not interchange the two units and assume that the new
right-hand separator is valid. Both sectors in (12) still require the
whole four-square or ring argument.
