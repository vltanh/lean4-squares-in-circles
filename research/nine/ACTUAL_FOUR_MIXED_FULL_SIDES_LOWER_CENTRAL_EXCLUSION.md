# A lower central outsider cannot occur in the mixed full-side pattern

November 2, 2026. Complete hand proof with an exact rational arithmetic
replay. Numerical direction checks suggested the intermediate one-third
bound; no numerical optimizer result is a proof premise. No Lean or CI.

Put

\[
 Q=1105/256,\quad r=\sqrt Q,\quad \rho=91/60,
 \quad l=29/60,\quad u=13/12.
\]

Retain four physical unit squares forming an actual horizontal chain
\(M_0<_xM_1<_xM_2<_xM_3\), in the closed Q-disk. All other squares
below are original physical units, with arbitrary independent orientations
and pairwise disjoint open interiors. We use the established actual-four
bounds

\[
 -31/60<x_1<-29/60,\qquad 29/60<x_2<31/60,
 \qquad 1/2\le h_i<31/60,\quad g_i=1/(4h_i)>15/31,
 \tag{1}
\]

\[
 x_1>h_1-61/60,\qquad |c_S|<\rho,\qquad |x_S|<u
 \quad\text{for outsiders }S.
 \tag{2}
\]

The right endpoint contains the fixed rectangle

\[
 [A,B]\times[-c,c],\qquad
 A=503/480,\quad B=937/480,\quad c=221/600.
 \tag{3}
\]

These are consequences of
`UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md`.
The same-half-plane inner-clearance theorem gives vertical center gap
strictly greater than \(97/100\) from the corresponding inner main.

## 1. The statement

Suppose

\[
 y_1<-3/5,\qquad y_2<7/20,
 \tag{4}
\]

and suppose there is a right-side outsider \(T\) satisfying

\[
 l\le x_T<u,\qquad y_T<y_2.
 \tag{5}
\]

Then there is **no** central outsider \(F\) with

\[
 |x_F|\le l,\qquad y_F<y_1.
 \tag{6}
\]

In particular, in the normalized strict-counterexample occupancy
\((L,C,R)=(2,1,2)\), if the left inner main is the bottom unit of its
full side and the right inner main is the middle unit of its full side,
the central outsider is above both inner main centers. The full-side
height theorems supply (4), and the right lower outsider supplies (5).
The retained main cone comparison supplies the already proved fact that
a central outsider is above both or below both; the latter alternative
is excluded here.

The reflected versions exchange left and right, or top and bottom.
This closes the stated complete occupancy alternative, not the whole
actual-four family or the entire `000/11` mask.

## 2. A lower central outsider must lie beyond one third

We first prove the following stronger local implication:

\[
 y_1<-3/5,\quad |x_F|\le l,\quad y_F<y_1
       \quad\Longrightarrow\quad x_F>1/3.
 \tag{7}
\]

Reflect the vertical coordinate. Write \((X,Y)\) for the reflected
center of F, and \((x_1,Z)\) for the reflected center of M1. Thus
\(Y>Z>3/5\). Let \(g=g_1>15/31\). The aligned square of halfwidth
g centered at \((x_1,Z)\) is contained in M1.

Suppose \(X\le1/3\). Because \(X\ge-l>x_1\), its horizontal center
gap \(D=X-x_1\) satisfies

\[
 D<17/20,\qquad D-g<227/620<11/30.
 \tag{8}
\]

Write the absolute side-axis components of F as

\[
 a\ge b\ge0,\quad a^2+b^2=1,\quad h=(a+b)/2.
\]

Its top projection lies in the disk, so \(Y+h\le r<133/64\).
Consequently its positive vertical center gap \(V=Y-Z\) obeys

\[
 V-g<133/64-3/5-15/31-h<1-h.
 \tag{9}
\]

The positive margins in (8)--(9) are respectively \(1/1860\) and
\(57/9920\). The radius comparison has squared reserve \(9/4096\).

The coordinate axes cannot separate F from the aligned inset: (8)
gives \(D<g+h\), while (9) gives
\(V-g<1-h\le h\). A side-axis separator of F would require one of

\[
 a(D-g)+b(V-g)\ge1/2,
 \qquad b(D-g)+a(V-g)\ge1/2.
 \tag{10}
\]

Taking absolute components makes (10) necessary for every sign choice
of a physical side normal. We now exclude both alternatives on the full
orientation interval.

### 2.1. The first side-axis alternative

For \(0\le b\le1/\sqrt2\),

\[
 a\le1-b^2/2,\qquad h\ge1/2+(2/7)b.
 \tag{11}
\]

The first follows by squaring positive sides. For the second,
\(a\ge1-3b/7\) follows from

\[
 a^2-(1-3b/7)^2=b(42-58b)/49\ge0,
\]

because \(b\le1/\sqrt2<5/7<21/29\). Thus (8)--(9) give

\[
\begin{aligned}
 a(D-g)+b(V-g)
 &< (11/30)a+b(1-h)\\
 &\le11/30+b/2-(197/420)b^2\\
 &\le11/30+105/788
   =1/2-1/11820<1/2.
\end{aligned}
 \tag{12}
\]

The last inequality is the maximum of one concave quadratic, obtained
by completing its square. It excludes the first alternative of (10).

### 2.2. The other side-axis alternative

If \(a\ge3/4\), use \(a+b^2/2\le1\) and
\(11/30-a/2\le-1/120\) to obtain

\[
\begin{aligned}
 (11/30)b+a(1-h)
 &=a-1/2+b^2/2+b(11/30-a/2)\\
 &\le1/2.
\end{aligned}
 \tag{13}
\]

If \(a\le3/4\), then
\(a+b\ge(3+\sqrt7)/4>7/5\), so \(h>7/10\).
The displayed minimum follows from the monotonicity of
\(a+\sqrt{1-a^2}\) on \([1/\sqrt2,3/4]\); the final comparison
uses \(\sqrt7>13/5\). Since \(b<5/7\),

\[
 (11/30)b+a(1-h)
 <11/42+9/40=409/840<1/2.
 \tag{14}
\]

In either case (8)--(9) make the second expression of (10) strictly
less than one half. All four separating-axis possibilities have failed.
This contradicts physical interior-disjointness and proves (7).

We will also need the elementary height consequence

\[
                         Y>3/5+15/31.
 \tag{15}
\]

Indeed (2) and \(h_1+g_1\ge1\) give
\(D-g_1<X+1/60\le1/2\). The radius-one-half disk inside F avoids
the aligned inset. If \(V\le g_1\), its distance to that inset would
be less than one half. Thus \(V>g_1>15/31\), proving (15).

## 3. The right lower outsider has a circular lower profile

Continue in the vertically reflected frame. Write \((s,t)\) for T.
The same-half-plane clearance, (4), and (5) imply

\[
 l\le s<u,\qquad t>97/100-7/20=31/50.
 \tag{16}
\]

The reflected rectangle (3) is unchanged. The radius-one-half disk of T
is disjoint in interior from it, so

\[
 \max(A-s,0)^2+(t-c)^2\ge1/4.
 \tag{17}
\]

Here \(s<u<B\) and \(t>31/50>c\), so these are exactly its
distance coordinates from the rectangle.

Put

\[
 s_0=A-\sqrt{1/4-(31/50-c)^2}.
\]

Then \(l<s_0<A<u\) and \(s_0<37/60\). For the latter comparison,
both sides of the required positive-root comparison are positive and

\[
 1/4-(31/50-c)^2-(A-37/60)^2
                         =3959/5760000>0.
 \tag{18}
\]

Equations (16)--(17) imply \(t\ge L(s)\), where

\[
 L(s)=
 \begin{cases}
 31/50,&l\le s\le s_0,\\
 c+\sqrt{1/4-(A-s)^2},&s_0\le s\le A,\\
 c+1/2,&A\le s\le u.
 \end{cases}
 \tag{19}
\]

## 4. The two original unit disks would overlap

By (7), (15), and the universal center bound, F satisfies

\[
 1/3<X\le l,\qquad 3/5+15/31<Y<\rho.
 \tag{20}
\]

First suppose \(t\ge Y\). Since \(s\ge l\ge X\),

\[
 (s-X)^2+(t-Y)^2
 <(3/4)^2+(\rho-3/5-15/31)^2
 =1-17311/69192<1.
 \tag{21}
\]

Suppose instead \(t\le Y\). Replacing t by its lower bound (19)
can only increase its squared vertical distance from Y. Put

\[
 f(s)=(s-X)^2+(Y-L(s))^2.
\]

On the first and last intervals of (19), this function increases with s,
because \(s\ge X\). On the middle interval, expansion gives

\[
\begin{aligned}
 f(s)={}&2(A-X)s+X^2-A^2+(Y-c)^2+1/4\\
       &-2(Y-c)\sqrt{1/4-(A-s)^2}.
\end{aligned}
\]

It is convex there: the square root is concave and \(Y-c>0\).
Its maximum over the whole interval \([l,u]\) is therefore attained
at \(s_0\) or u. These two values satisfy, by (18) and (20),

\[
\begin{aligned}
 f(s_0)&<(17/60)^2+(269/300)^2
        =1-5207/45000<1,\\
 f(u)&<(3/4)^2+(389/600)^2
        =1-6179/360000<1.
\end{aligned}
 \tag{22}
\]

Together (21)--(22) give \(|c_F-c_T|<1\) in every case. The open
radius-one-half disks contained in F and T would overlap. This is
incompatible with physical interior-disjointness and proves the theorem.

## 5. Coverage and replay

The argument includes all orientations of F and T, both chiralities, every
physical separator owner, all equalities in their strip coordinates, and
all possible vertical orders of F and T. Its only assumptions beyond the
actual-four bounds are the original predicates (4)--(6). No selected
short-chain edge is used.

`verify_mixed_full_side_lower_central.py` replays the rational coefficient
identities and every positive rational comparison above. The full physical
coverage is the separating-axis and convexity argument in Sections 2--4.
The verifier is a small arithmetic audit, not a sampled pose search and
not a substitute for the quantified hand proof.

## 6. Stronger cone-chain version: no upper bound on the opposite main

If the actual main four-chain is also a center-cone chain, the hypothesis
\(y_2<7/20\) in Section 1 can be dropped. More precisely,

\[
 y_1<-3/5,\qquad l\le x_T<u,\qquad y_T<y_2
\]

still excludes every central F below M1. Thus the opposite side need
not be full or have a middle-marker main.

Indeed the main cone gives
\(y_2<y_1+31/30<13/30\). Its same-half-plane clearance from T gives
\(y_T<13/30-97/100=-161/300\). In the reflected notation of the
preceding proof we may therefore replace (16) by

\[
                      t>f_0:=161/300.
 \tag{23}
\]

Sections 2 and 4's case \(t\ge Y\) remain unchanged. The other order
requires one additional coupled center estimate.

### 6.1. A lower central unit with reflected height at least three halves

In addition to (20), suppose \(Y\ge3/2\). Then

\[
                              X>2/5.
 \tag{24}
\]

To prove this, suppose instead \(X\le2/5\). With the reflected left
main center height \(Z>3/5\) and inset halfwidth \(g>15/31\), put

\[
 C=3/5+15/31=168/155,\qquad
 d=11/12-15/31=161/372,\qquad v=Y-C.
\]

The actual center gaps satisfy \(D<11/12\), \(V<Y-3/5\). Thus
\(D-g<d\) and \(V-g<v\), with
\(0<v\le d\) and \(d-v=\rho-Y\). Coordinate separation is
impossible, since both gaps are below \(11/12<g+h\).

For the two possible component orders of an F-owned side axis, the
larger adjusted center projection is strictly below \(ad+bv\).
Because \(a\le1\) and \(a+b=2h\),

\[
 ad+bv\le2hv+d-v
       <2(133/64-Y)(Y-C)+\rho-Y=:W(Y).
\]

Here top containment gave \(h<133/64-Y\). The function W decreases
on \([3/2,\rho]\): its derivative at the left endpoint is
\(-3353/4960<0\), and its derivative then decreases. Its maximum is

\[
 W(3/2)=2963/5952=1/2-13/5952<1/2.
\]

Both physical side-axis alternatives fail as well. This proves (24),
with no independent maximization of Y and h.

### 6.2. The broadened circular profile

Define the profile (19) with \(f_0\) in place of \(31/50\), and let

\[
 s'_0=A-\sqrt{1/4-(f_0-c)^2}.
\]

The same monotonicity and convexity proof reduces the squared center
distance in the case \(t\le Y\) to the two vertices \(s'_0\) and u.
The latter vertex has exactly the previous bound
\(1-6179/360000\). Also

\[
 s'_0<7/12,
 \qquad 1/4-(f_0-c)^2-(A-7/12)^2=33559/5760000>0.
\]

If \(Y\le3/2\), use \(X>1/3\) from Section 2. At the first vertex,

\[
 (s'_0-X)^2+(Y-f_0)^2
  <(1/4)^2+(289/300)^2=1-427/45000<1.
\]

If \(Y>3/2\), use (24). The same squared distance is less than

\[
 (11/60)^2+(49/50)^2=1-539/90000<1.
\]

Thus every vertical order again forces the original unit disks of F
and T to overlap. This proves the strengthened cone-chain statement,
including all boundary heights and physical orientations.
