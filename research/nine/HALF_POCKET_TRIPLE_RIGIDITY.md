# Every upper terminal-pocket triple is the canonical aligned triple

Put

\[
D=\{(x,y):x^2+y^2\le17/4\},\qquad
E=[1,2]\times[-1/2,1/2],\quad W=-E,
\]

and write

\[
N=[-1/2,1/2]\times[1,2],\qquad
\sigma=1/\sqrt2,\qquad
K=\{p:|p-(0,3/2)|<1/2\}.
\]

**Theorem (`HALF.3`).** If three physical unit squares lie wholly in
\(D\cap\{y\ge0\}\), avoid the open interiors of \(E,W\), and
have pairwise disjoint open interiors, then they are exactly

\[
[-1,0]\times[0,1],\qquad [0,1]\times[0,1],\qquad N.
\tag{1}
\]

This proof retains all square orientations and all boundary contacts.
It uses the proved analytic cap and open-disk intersection inputs below.
It does not need the quantitative \(19/120\) section bound used in
the independent path-completion proof.

## 1. Local inputs and the remaining center order

We use the following established results.

- Every unit-square center in \(D\) has radius at most \(3/2\), and
  its support halfwidth \(H_T(n)\) in a unit direction is at least
  \(1/2\). Distinct physical square centers have distance at least one.
- `DIAGONAL_CENTER_EXCLUSION.md` gives \(-1<c_x<1\) for every
  upper square avoiding \(E,W\).
- `HALF_DISK_CLOSE_CENTER_RIGIDITY.md`, Corollary 3, proves (1) whenever
  any two of the three horizontal center coordinates differ by at most
  \(1/2\).
- `LOW_OUTER_SQUARE_MEETS_N_DISK.md` and
  `HIGH_OUTER_SQUARE_MEETS_N_DISK.md` prove that every upper square
  avoiding \(E,W\) with \(1/2<c_x<1\) meets the open disk \(K\).
  The latter theorem also proves this for every such square with
  \(c_x\ge0,c_y\ge1\), by placing \((3/7,5/4)\) strictly inside.
- `ANNULAR_SAME_SIDE_PAIR_EXCLUSION.md` proves that an upper pair with
  \(0\le x_A<x_B<1\) and \(x_B-x_A>1/2\) cannot have both center
  radii at least \(\sigma\).
- The positive-cap consequence in `WEDGE_135_CAPACITY_ONE.md`, Section 4,
  says that for any upper square \(T\) avoiding \(E\) with
  \(1/2<c_x<1\), and any unit \(n=(b,a)\) with \(0\le a\le b\),
  \[
  \min_T n\cdot p<1/2+\sigma a.                     \tag{2}
  \]
  This is a single-terminal result; it assumes no 135-degree wedge.

For later use, (2) extends to every \(0\le c_x<1\). Indeed if
\(c_x\le1/2\), the elementary center and support bounds give

\[
\min_T n\cdot p\le b/2+3a/2-1/2<1/2+\sigma a,
\tag{3}
\]

because

\[
b/2+(3/2-\sigma)a
\le\sqrt{1/4+(3/2-\sigma)^2}
=\sqrt{3-3\sigma}<1.
\]

The last strict inequality is \(\sigma>2/3\), or \(9>8\).
Reflection gives the corresponding bound for left-center squares in
left-up directions.

Suppose, for contradiction, that a triple is not (1). Sort its squares
as \(C,A,B\) by horizontal center coordinate. The close-center theorem
gives both adjacent gaps strictly greater than \(1/2\). Reflect the
whole picture horizontally, if necessary, so that the middle square
has nonnegative center coordinate. Write its center as \((x,y)\).
Then

\[
0\le x<1/2,\quad x_B>x+1/2>1/2,\quad
x_C<x-1/2<0.                                       \tag{4}
\]

The annular same-side pair theorem applied to \(A,B\) forces

\[
x^2+y^2<1/2,\qquad 1/2\le y<\sigma.                \tag{5}
\]

## 2. The right neighbor forces a precise tilt and center inequality

The proof of the annular pair theorem supplies a useful fact independent
of annularity: every separator from \(A\) toward \(B\) in (4) must
point shallowly up-right. For completeness, its reductions are these.

Any down-right unit normal \((b,-a)\), \(a,b\ge0\), obeys

\[
\max_A(b,-a)\cdot p
\ge1/2-3a/2=\sup_K(b,-a)\cdot p.
\]

Since \(B\) meets \(K\), it cannot be separated on that positive side.
For a steep up-right normal \((b,a)\), \(0<b<a\), whole upper
containment gives the two-direction support estimate

\[
\begin{aligned}
\max_A(b,a)\cdot p
&\ge aH_A(e_y)+H_A((b,a))\\
&\ge\min\{a+b/2,\ [1+a(a+b)]/2\}>1,
\end{aligned}
\]

whereas \(\min_B(b,a)\cdot p\le1\). Finally, leftward or vertical
normals have center projection gap below one: \(x_B>x\) and the
center height gap has absolute value below one. Thus every possible
separator is \((b,a)\) with \(0<a\le b\). By (2), at least one such
direction must satisfy

\[
\max_A(b,a)\cdot p<1/2+\sigma a.                   \tag{6}
\]

Represent the actual frame of \(A\), up to its square symmetries, by
coordinate magnitudes

\[
p=\cos\phi,\quad q=\sin\phi,\quad
0\le\phi\le\pi/4,\quad
h=(p+q)/2,\quad k=(p-q)/2,
\quad d=\sigma-y.
\]

Whole upper containment and (5) give

\[
y\ge h,\quad d>0,\quad d\le\sigma-h,
\quad h^2+k^2=1/2.                                 \tag{7}
\]

The following two factorizations will control every orientation:

\[
\begin{aligned}
p(h-1/2)-q(\sigma-h)
  &=(1-p)/2+q(p-\sigma)\ge0,\\
p(p-\sigma)-(p+q)(\sigma-h)
  &=(p-\sigma)(p+q-\sigma)\ge0.
\end{aligned}                                      \tag{8}
\]

Consequently

\[
h-1/2\ge(q/p)d,
\qquad p-\sigma\ge(1+q/p)d.                         \tag{9}
\]

Let a shallow up-right unit normal have angle
\(\theta\in[0,\pi/4]\), so \((b,a)=(\cos\theta,\sin\theta)\).
Subtract \(1/2+\sigma a\) from \(A\)'s support in this direction.

For the negative-tilt frame \((p,-q),(q,p)\), the difference is

\[
b(x+h)+a(k-d)-1/2.
\]

Both coefficients of \(b,a\) are nonnegative, since
\(k-d\ge p-\sigma\ge0\). The expression is concave in \(\theta\),
and its endpoint values are

\[
x+h-1/2\ge0,
\qquad (x+p-d-\sigma)/\sqrt2\ge0
\]

by (9). This tilt cannot satisfy (6).

For the positive-tilt frame \((p,q),(-q,p)\), the difference is

\[
\begin{cases}
b(x+h)-a(k+d)-1/2,&0\le\theta\le\phi,\\
b(x+k)+a(h-d)-1/2,&\phi\le\theta\le\pi/4.
\end{cases}                                       \tag{10}
\]

The first branch is decreasing. The second is concave, because both
coefficients before the constant are nonnegative. Their common value
at \(\theta=\phi\) is \(px-qd\), while the value at \(\pi/4\)
is nonnegative by (9). Therefore (6) is possible only when

\[
\boxed{\quad A\text{ has the positive-tilt frame},\qquad
        0<q<p,\qquad 0\le x<(q/p)d.\quad}           \tag{11}
\]

Here \(q=0\) would make the strict inequality impossible, while
\(p=q\) would force \(y\ge h=\sigma\), contrary to (5).
Useful consequences of (7), (9), and (11) are

\[
\begin{gathered}
x<d\le\sigma-1/2<1/4,\qquad x<k,\\
h-x>1/2,\qquad p-x-d>\sigma.                       \tag{12}
\end{gathered}
\]

For \(x<k\), use
\(\sigma-h=k^2/(\sigma+h)\le k\), together with \(x<d\).

## 3. The left neighbor meets the same open north disk

Reflect \(C\) across the vertical axis. Its horizontal center coordinate
is positive by (4). If \(-x_C>1/2\), the open-disk intersection theorem
immediately gives \(C\cap K\ne\varnothing\), since \(K\) is invariant
under this reflection.

If \(-x_C\le1/2\) and \(y_C<1\), equations (5), (12) give

\[
|x-x_C|<3/4,\qquad |y-y_C|<1/2.
\]

Their squared center distance is then less than
\(9/16+1/4=13/16<1\), contradicting physical disjointness. Thus in
this second case \(y_C\ge1\), and the high-center common-point theorem
again gives \(C\cap K\ne\varnothing\). We have proved in all cases

\[
                         C\cap K\ne\varnothing.     \tag{13}
\]

## 4. The forced inner tilt blocks every direction toward the left neighbor

We now exclude every possible separator from \(A\) toward \(C\).
Normals with nonnegative horizontal coordinate are already impossible:
their horizontal center projection is nonpositive, and their vertical
center projection has magnitude below one. It remains to treat the
left-up and left-down directions.

### 4.1. Shallow left-up directions

For a unit normal \((-b,a)\), \(0\le a\le b\), the positive frame
in (11) gives exactly

\[
\max_A(-b,a)\cdot p-(1/2+\sigma a)
 =b(h-x)+a(k-d)-1/2.                               \tag{14}
\]

This is concave as the normal angle above the negative horizontal axis
runs from zero to \(\pi/4\). Both endpoint values are strictly positive
by (12): they are

\[
h-x-1/2,\qquad (p-x-d-\sigma)/\sqrt2.
\]

Thus \(\max_A(-b,a)\cdot p>1/2+\sigma a\). The reflected form of
the general positive-cap bound (2)--(3) gives
\(\min_C(-b,a)\cdot p<1/2+\sigma a\), excluding separation.

### 4.2. Steep left-up directions

For \((-b,a)\), \(a\ge b\ge0\), parameterize the angle as
\(\theta\in[\pi/4,\pi/2]\). The actual support of \(A\) has just
one frame breakpoint at

\[
\theta_v=\pi/2-\phi,\qquad (-b,a)=(-q,p).
\]

The support is positive and concave on each of the two resulting
intervals. Positivity follows already from
\(-bx+ay\ge a(y-x)>0\). Hence its minimum occurs at one of
\(\pi/4,\theta_v,\pi/2\).

At \(\pi/4\) the support is strictly greater than one by (14). At
\(\pi/2\) it equals \(y+h\ge2h>1\), since \(q>0\). At the
owned-axis breakpoint it is

\[
-qx+py+1/2>1.
\]

Indeed (11), (7), and \(p^2+q^2=1\) give

\[
\begin{aligned}
py-qx
&>py-(q^2/p)d
 =\frac{y-q^2\sigma}{p}\\
&\ge\frac{h-q^2\sigma}{p}
 =\frac12+\frac{q(1/2-\sigma q)}p
 >\frac12,
\end{aligned}
\]

because \(0<q<\sigma\). Thus all steep left-up supports exceed one,
while \(\min_C n\cdot p\le1\) for every unit \(n\). These directions
cannot separate either.

### 4.3. Every left-down direction

Write \(n=(-b,-a)\), with \((b,a)=(\cos\theta,\sin\theta)\) and
\(0\le\theta\le\pi/2\). Compare the support of \(A\) to that of
the open disk \(K\):

\[
G(\theta):=\max_A n\cdot p-(1/2-3a/2)
=H_A((b,a))-1/2-bx+a(3/2-y).
\]

Using the positive-tilt frame, this is exactly

\[
G(\theta)=
\begin{cases}
b(h-x)+a(3/2-y-k)-1/2,&0\le\theta\le\phi,\\
b(k-x)+a(3/2-y+h)-1/2,&\phi\le\theta\le\pi/2.
\end{cases}                                       \tag{15}
\]

All the coefficients before the constant are nonnegative. In particular
\(k-x>0\), and
\(3/2-y-k>3/2-\sigma-1/2=1-\sigma>0\).
Each branch is therefore concave. Its possible minima occur at the
three endpoints, where

\[
\begin{aligned}
G(0)&=h-x-1/2>0,\\
G(\phi)&=-px+q(3/2-y)
          >q(3/2-\sigma)>0,\\
G(\pi/2)&=1-y+h>0.
\end{aligned}
\]

Consequently \(\max_A n\cdot p\ge\sup_K n\cdot p\) for every
left-down unit normal. By (13),
\(\min_C n\cdot p<\sup_K n\cdot p\). These directions also cannot
separate \(A,C\).

All unit normals have been excluded, in particular every possible
separating axis of the two actual squares. This contradicts their
physical disjointness. Hence the noncanonical triple does not exist,
and the only triple is (1). Conversely the three squares in (1) plainly
satisfy every hypothesis, completing the classification. \(\square\)

## 5. Capacity consequences

There are at most three squares in an upper terminal half-pocket. If
four existed, any chosen three would be the canonical triple, and
applying the same classification to a triple containing the fourth
would force it to coincide with one of the first three, contrary to
interior-disjointness.

More sharply, a screened terminal pocket of aperture strictly less than
\(\pi\) has capacity at most two. Widen both rays to an antipodal pair,
keeping their bisector and the squares fixed. The outer-face screen
proves terminal avoidance is preserved exactly as in
`WEDGE_135_CAPACITY_ONE.md`, Section 1.1. Three squares would therefore
be the canonical triple in that half-plane frame. The two aligned inner
squares have bottom edges whose union contains nonzero points on both
opposite boundary rays. An origin wedge of aperture less than \(\pi\)
cannot contain both rays. Thus that triple cannot have lain in the
original strict wedge.
