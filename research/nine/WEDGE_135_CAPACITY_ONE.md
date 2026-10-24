# A screened pocket of aperture at most 135 degrees holds at most one square

**Status:** complete hand proof, using the two analytic cap inequalities
and the right-owned downward-separator lemma identified below. The
squares have independent orientations throughout. This closes the
uniform `WEDGE.2` statement. The complementary strict-half-pocket bound
is now proved in HALF_POCKET_TRIPLE_RIGIDITY.md; together the two bounds
close Y.ALL in Y_ALL_COMPLETION.md.

Put

\[
D=\{(x,y):x^2+y^2\le17/4\},\qquad R=\sqrt{17}/2,
\]

and, for a unit direction \(e\), put

\[
S(e)=\{te+sJe:1\le t\le2,\ -1/2\le s\le1/2\}.
\]

**Theorem.** Let \(W\) be a closed origin wedge of aperture at most
\(3\pi/4\), whose two boundary directions are \(e_1,e_2\). At most one
unit square can lie wholly in \(D\cap W\), with its open interior
disjoint from both \(S(e_1),S(e_2)\), when all the additional squares
are also required to have pairwise disjoint open interiors.

The proof uses these established local results:

1. The center-radius bound, outer-face screen, and radial-terminal
   separation lemma in `RADIAL_SECTOR_POCKET_CAPACITY.md`.
2. `DIAGONAL_CENTER_EXCLUSION.md` and
   `HALF_DISK_CLOSE_CENTER_RIGIDITY.md`.
3. `POSITIVE_NORMAL_CAP_FLOOR_EXCLUSION.md` and
   `OWNED_AXIS_TERMINAL_CAP_EXCLUSION.md`.
4. `RIGHT_OWNED_DOWNWARD_SEPARATOR.md`.

For a square \(T\), write \(c_T\) for its center and \(H_T(v)\) for
its centered support halfwidth. For a unit vector \(v\),

\[
H_T(v)\ge1/2,\qquad |c_T|\le3/2.                 \tag{1}
\]

Physical disjointness of squares \(A,B\) supplies a unit separating
axis \(n\) owned by one of them, oriented so that

\[
n\cdot(c_B-c_A)\ge H_A(n)+H_B(n)\ge1.            \tag{2}
\]

This is the ordinary separating-axis theorem for their actual squares;
no common orientation is imposed.

## 1. Widening and the admissible center sector

### 1.1. Widening preserves terminal avoidance

It suffices to prove the theorem at aperture \(3\pi/4\). Indeed, widen
both boundary rays outward to this aperture, keeping the bisector fixed
and the additional squares fixed. Every additional square remains in
the wider wedge and still avoids the moved terminals.

To verify the latter assertion, suppose an interior point \(p\) of an
additional square newly belonged to the interior of an upper moved
terminal. Its angular distance \(\delta'\) below the new upper ray
satisfies \(0\le\delta'<\arctan(1/2)<\pi/2\). Since the point was
inside the old wedge, its distance \(\delta\) below the old ray obeys
\(0\le\delta\le\delta'\). Its old radial projection is therefore
at least its new radial projection, which exceeds one. Its old absolute
tangential projection is at most its new one, which is below \(1/2\).
The outer-face screen for the old terminal gives old radial projection
strictly below two. Thus \(p\) was in the old terminal interior, a
contradiction. The lower terminal is identical. The argument concerns
open interiors and therefore retains all boundary-contact cases.

Rotate the widened wedge so its rays have angles \(0\) and
\(3\pi/4\). Write

\[
E=S((1,0))=[1,2]\times[-1/2,1/2],\qquad
F=S((-1,1)/\sqrt2).
\]

### 1.2. Every center is in the annulus

Every unit square wholly in a wedge of aperture at most \(3\pi/4\)
has center radius at least \(1/\sqrt2\). Here is the exact elementary
argument. If \(|c|^2<1/2\), express its center in its own square axes
as \((p,q)\), with \(p\ge|q|\) and \(p\ge0\). The origin cannot
be in the square interior. Nor can it lie in the relative interior of
a side, since that gives angular spread \(\pi\). Thus \(p>1/2\)
and \(|q|<1/2\). The two endpoints of the near side are

\[
u=(p-1/2,q-1/2),\qquad v=(p-1/2,q+1/2).
\]

They have positive determinant \(p-1/2\), whereas

\[
u\cdot v=|c|^2-p<1/2-p=-\det(u,v).
\]

Their angle therefore exceeds \(3\pi/4\), a contradiction.

### 1.3. Each terminal excludes center angles below 45 degrees

Suppose a square in \(D\), avoiding \(E\), has center \((x,y)\)
with \(x\ge y\ge0\) and \(x^2+y^2\ge1/2\). Its open inscribed
radius-\(1/2\) disk avoids \(E\), so its center has distance at
least \(1/2\) from \(E\). Elementary rectangle-distance cases give:

- If \(y\le1/2\), then \(x\le1/2\), forcing
  \(x=y=1/2\) by the annulus condition.
- If \(1/2<y\le x<1\), the squared distance is at most
  \((1-x)^2+(x-1/2)^2<1/4\), since the difference from \(1/4\)
  is \((2x-1)(x-1)<0\).
- If \(x\ge1\), then \(x\le3/2<2\) and the distance condition
  forces \(y\ge1\). The diagonal-center exclusion puts the terminal
  corner \((1,1/2)\) in the square interior, a contradiction.

In the first case the point \((1,1/2)\) is an inscribed-disk tangent
point. Unless the square is axis aligned, this point lies in its open
interior, again giving terminal overlap. Thus the only equality case
is \([0,1]^2\), with center angle exactly \(\pi/4\).

Apply this observation to both terminals. Every additional center has
angle in \([\pi/4,\pi/2]\). In particular

\[
0\le x\le y,\quad x<1,\quad 1/2\le y\le3/2.     \tag{3}
\]

The strict bound \(x<1\) follows once more from diagonal-center
exclusion. Introduce the reflection exchanging the two terminals,

\[
M(x,y)=((y-x)/\sqrt2,(x+y)/\sqrt2).               \tag{4}
\]

The same inequalities (3) hold in the reflected coordinates.

## 2. Two putative squares have opposite horizontal orders in the two frames

The north radial square \(N=S((0,1))\) cannot be an additional square:
its angle from \(F\) is \(\pi/4\), whereas two disjoint radial
terminals require angular separation at least
\(2\arctan(1/2)>\pi/4\). The analogous north square in the reflected
frame is also forbidden. In particular equality \(y=3/2\) in (3) is
impossible: (1) would force center \((0,3/2)\), and equality in the
farthest-corner bound would force the radial square \(N\).

Now suppose two additional squares \(A,B\) exist. The close-horizontal-
center theorem says that an upper-half-disk pair with horizontal center
gap at most \(1/2\) must include \(N\). Therefore the horizontal gap
is strictly greater than \(1/2\), in both terminal frames. Name the
squares so that \(x_A<x_B\), and put

\[
d_x=x_B-x_A,\qquad d_y=y_B-y_A.
\]

Then

\[
1/2<d_x<1,\qquad -1<d_y<1.                      \tag{5}
\]

The reflected horizontal gap is
\((d_y-d_x)/\sqrt2\), whose absolute value exceeds \(1/2\). It
cannot be positive: that would give
\(d_y>d_x+1/\sqrt2>1\). Consequently

\[
\frac{d_y-d_x}{\sqrt2}<-1/2.                    \tag{6}
\]

Thus \(MB\) is the square on the left and \(MA\) the square on the
right in the reflected frame. Both frames have all the hypotheses
needed below, including right-center coordinate strictly between
\(1/2\) and one.

## 3. A support lower bound for every annular upper square

**Lemma.** Let \(T\subset\{y\ge0\}\) be a unit square whose center
has \(c_x\ge0\) and \(|c|\ge1/\sqrt2\). For a unit up-right
direction \(n=(b,a)\), the following hold:

\[
\begin{array}{ll}
0\le a\le b:&\displaystyle\max_{p\in T}n\cdot p
                 \ge\frac12+\frac a{\sqrt2},\\[4pt]
0<b<a:&\displaystyle\max_{p\in T}n\cdot p>1.
\end{array}                                                   \tag{7}
\]

To prove it, write the magnitudes of the square-axis coordinates as
\(p=\cos\phi,q=\sin\phi\), where \(0\le\phi\le\pi/4\).
Its vertical halfwidth is \(h=(p+q)/2\); put \(k=(p-q)/2\), so
\(h^2+k^2=1/2\). For the fixed orientation, the minimum of
\(bc_x+ac_y\), subject to

\[
c_x\ge0,\quad c_y\ge h,\quad c_x^2+c_y^2\ge1/2,
\]

occurs at one of \((0,1/\sqrt2)\), \((k,h)\). Indeed, below height
\(1/\sqrt2\) the least admissible horizontal coordinate is
\(\sqrt{1/2-c_y^2}\), and the resulting function
\(b\sqrt{1/2-c_y^2}+ac_y\) is concave on \([h,1/\sqrt2]\).
At greater heights the first endpoint is no worse.

The first endpoint gives support at least
\(a/\sqrt2+1/2\). At the second endpoint, add
\(bk+ah\) to the actual orientation-dependent support halfwidth.
There are only two tilt signs, dealt with exactly as follows.

If \(a\le b\), put \(a=\sin\theta,b=\cos\theta\), with
\(0\le\theta\le\pi/4\).

- For the frame \((p,-q),(q,p)\), the sum is \((a+b)p\), hence
  at least \((a+b)/\sqrt2\).
- For the frame \((p,q),(-q,p)\), when \(\phi\le\theta\) the
  sum is \((a+b)p+(a-b)q\). It is positive and concave in
  \(\phi\), and its endpoint values are \(a+b\ge1\) and one.
  When \(\phi\ge\theta\), the sum is
  \(bp+aq=\cos(\phi-\theta)\ge(a+b)/\sqrt2\).

Now \((a+b)/\sqrt2\ge1/2+a/\sqrt2\), since
\(b\ge1/\sqrt2\), and \(1\ge1/2+a/\sqrt2\). This proves the
first assertion of (7).

For \(0<b<a\), the first center endpoint already gives a value
strictly greater than one. For the positive-tilt frame, the second
endpoint gives \((a+b)p+(a-b)q\), whose minimum on
\([0,\pi/4]\) is at least
\(\min\{a+b,\sqrt2a\}>1\). For the negative-tilt frame split at
\(\psi=\arctan(b/a)\). When \(\phi\le\psi\), the sum is
\((a+b)p\ge a(a+b)\); when \(\phi\ge\psi\), it is
\(a(p+q)\ge a(a+b)\). Finally
\(a(a+b)=1+b(a-b)>1\). This proves (7) for every orientation.

## 4. No shallow up-right cap can avoid the east terminal

We use this direct consequence of the two analytic cap theorems:

**Cap consequence.** Suppose a unit square \(T\subset D\cap\{y\ge0\}\)
avoids \(E\) and has center \(1/2<c_x<1\). For
\(n=(b,a)\), \(0\le a\le b\), \(a^2+b^2=1\),

\[
\min_{p\in T}n\cdot p<\frac12+\frac a{\sqrt2}.        \tag{8}
\]

Here is the complete separator routing needed to apply those results.
Assume the reverse weak inequality. A terminal-owned separator cannot
put \(T\) to the left of \(E\), since its horizontal halfwidth is
at least \(1/2\) and \(c_x>1/2\). Right and below are also
impossible. An above separator gives \(T\subset\{y\ge1/2\}\),
contradicting `POSITIVE_NORMAL_CAP_FLOOR_EXCLUSION.md`.

For an axis owned by \(T\), direct its normal from \(E\) toward
\(T\), and write its nonnegative coordinate magnitudes as \(A,B\).

- A down-right normal is impossible because \(c_x<1<3/2\) and
  \(c_y\ge1/2\).
- An up-left normal \(m=(-B,A)\) gives exactly
  \(\min_Tm\cdot p\ge A/2-B\). Since
  \(1/\sqrt2>7/10\), the contradiction is
  `OWNED_AXIS_TERMINAL_CAP_EXCLUSION.md`.
- An up-right normal \(m=(A,B)\) gives
  \(Ac_x+Bc_y\ge2A+B/2+1/2\). If \(B=0\) it is
  impossible. Otherwise \(c_x<1\) yields
  \[
  Bc_y\ge A+B/2+1/2\ge B(1+A+B)/2,
  \]
  because \(2A+1-AB-B^2=A(2-B)+A^2\ge0\).
  The owned frame has vertical halfwidth \((A+B)/2\), so
  \(T\subset\{y\ge1/2\}\), the first cap contradiction again.
- A down-left normal \(m=(-A,-B)\) gives
  \(Ac_x+Bc_y\le A-B/2-1/2\). Since
  \(c_y\ge(A+B)/2\),
  \[
  Ac_x\le A-1/2-B/2-B(A+B)/2
          \le A-A(A+B)/2.
  \]
  The last inequality is \(1+B+B^2\ge A^2\). If \(A=0\)
  separation was already impossible; otherwise \(\max_Tx\le1\),
  again contradicting \(c_x>1/2\).

This exhausts every actual terminal separator, including zero-coordinate
boundaries, and proves (8).

## 5. Exhaust all pair separators in the two terminal frames

Take a separating axis (2) for the putative pair, with \(B\) on its
positive side. We use angles modulo \(2\pi\) in the first terminal
frame.

### 5.1. Up-right directions cannot separate

For \(n=(b,a)\) with \(0\le a\le b\), the annular support bound
(7) for \(A\) and the cap consequence (8) for \(B\) give

\[
\max_A n\cdot p\ge1/2+a/\sqrt2
                  >\min_B n\cdot p,
\]

contradicting separation. For \(0<b<a\), (7) gives
\(\max_A n\cdot p>1\), whereas every square in \(D\) satisfies

\[
\min_B n\cdot p=n\cdot c_B-H_B(n)\le3/2-1/2=1.
\]

The vertical direction cannot separate either, since \(d_y<1\).
Thus every normal angle in \([0,\pi/2]\) is excluded, regardless
of which square owns it. The identical conclusion holds in the
reflected frame.

### 5.2. Up-left and shallow down-left directions are too short

If \(n_x\le0,n_y\ge0\), then (5) gives
\(n\cdot(c_B-c_A)<1\), contradicting (2). For a shallow down-left
normal \(n=(-b,-a)\), \(0\le a\le b\), (5) gives

\[
n\cdot(c_B-c_A)
 =-bd_x-ad_y\le a(-d_x-d_y)<a(1-d_x)<1.
\]

Thus all normal angles in \([\pi/2,5\pi/4]\) are excluded.

### 5.3. The remaining steep downward directions reflect to up-right

For a normal angle \(\phi\in[-3\pi/4,-\pi/4]\), reflect the
pair and reverse its labels, as required by (6). The directed normal
is then \(-Mn\), whose angle is \(-\pi/4-\phi\in[0,\pi/2]\).
Section 5.1 in that frame excludes it.

### 5.4. Shallow downward directions use ownership and reflection

It remains only

\[
n=(b,-a),\qquad 0\le a\le b,\qquad a^2+b^2=1.
\]

If \(B\), the square on the right, owns this separator, all the
hypotheses of `RIGHT_OWNED_DOWNWARD_SEPARATOR.md` hold by (3) and
(5). That theorem excludes it.

If \(A\) owns it, reflect and reverse the labels. The right square
is now \(MA\), which owns the transformed directed normal

\[
-Mn=\left(\frac{a+b}{\sqrt2},-
                 \frac{b-a}{\sqrt2}\right).
\]

This is again a shallow downward normal of the required form, now
owned by the square on the right. Equations (3) and (6) verify the
same hypotheses in the reflected frame, so the same theorem excludes
this case too.

All separator directions and both possible owners have been exhausted.
The required separator (2) therefore cannot exist. This contradicts
physical disjointness of the two squares and proves the theorem.
\(\square\)

## 6. Precise use for the Y family

In the Y family the screened rays route all extra squares into two
closed pockets of apertures \(\pi/2+\theta\) and \(\pi-\theta\),
where \(0<\theta<\pi/2\). Their sum is \(3\pi/2\), so one has
aperture at most \(3\pi/4\); the theorem above gives capacity one
for that entire pocket, uniformly in the parameters. The other pocket
has aperture strictly below \(\pi\). A capacity-two theorem for every
such strict pocket would give at most three extras and close `Y.ALL`.
That latter theorem is a separate remaining input; it has not been
assumed or proved in this file.

This proof also does **not** establish that an arbitrary pair of upper
E/W-pocket squares with positive annular centers is impossible. The
left-owned shallow downward case above uses the second, 135-degree
terminal and the reversal of horizontal order. An antipodal terminal
does not supply that same reflected frame.
