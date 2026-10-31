# A central channel cannot return through a circle-touching neighbor

**Status: complete exact hand argument; root and separate independent hand audits passed.**
This manuscript excludes the entire adjacent-loaded-pair pattern of
the C4-with-leaf branch of C1.4.b1. Both radial leaf types, every
articulation orientation, both transmitter widths, all contact types,
and all circle-weight masks are included. The proof excludes the core
itself and retains all four completion squares.

The main geometric theorem is stronger than that load pattern: a
one-square normal channel leaving the articulation of a radial leaf
cannot return to that articulation through a circle-touching unit
neighbor. The far endpoint of the channel need not itself touch the
circle. No new generic normal selection or owner-axis classification
is used.

Throughout, put

\[
 Q=\frac{1105}{256},\qquad
 \frac{79}{40}\le R\le\sqrt Q,\qquad
 T=\sqrt{R^2-\frac14},\qquad
 d=T-1,\qquad \delta=d-1=T-2.
 \tag{1}
\]

We will use the exact bounds

\[
 T<\frac{121}{60},\qquad
 \delta<\frac1{60},\qquad
 \sqrt Q<\frac{25}{12}.
 \tag{2}
\]

They follow by squaring positive quantities. For the first comparison,
\((121/60)^2-(Q-1/4)=31/57600>0\).

## 1. A narrow angular cap for an arbitrary unit square

**Lemma 1.1.** Let a unit square S lie in the disk of squared radius
at most Q, and suppose every point of S has first coordinate at least
59/60. Then every point (X,Y) of S satisfies

\[
                    |Y|<\frac{13}{20}X.
 \tag{3}
\]

Equivalently, its entire angular shadow lies strictly within angle
\(\beta=\arctan(13/20)\) of the positive horizontal axis.

*Proof.* Put \(k=13/20\), and let r be the minimum first
coordinate of S. Choose a corner p on its left support face. Its two
inward unit side vectors, labeled by their first coordinates, have one
of the forms

\[
\begin{array}{ll}
 \text{I:}&u=(a,b),\quad v=(b,-a),\\
 \text{II:}&u=(a,-b),\quad v=(b,a),
\end{array}
 \qquad
 a\ge b\ge0,\quad a^2+b^2=1.
 \tag{4}
\]

Thus S is \(p+[0,1]u+[0,1]v\). The aligned case b=0
is included by choosing the appropriate endpoint of the left side.
Its horizontal width is a+b, and containment gives

\[
 a+b\le\sqrt Q-r
       <\frac{25}{12}-\frac{59}{60}=\frac{11}{10}.
 \tag{5}
\]

Consequently b/a<13/20. Indeed, on 0\le b/a\le1 the
width \((1+t)/\sqrt{1+t^2}\) increases with t, whereas

\[
 \frac{33}{\sqrt{569}}>\frac43>\frac{11}{10}.
\]

We will also use

\[
                         a\ge1-\frac b2.
 \tag{6}
\]

Both sides are nonnegative, and their squared difference is
\(b(1-5b/4)\ge0\), since \(b\le1/\sqrt2<4/5\).

It suffices to exclude a nonnegative maximum of the linear function
Y-kX. In case I, both side increments of this function are negative,
because b-ka<0 and -a-kb<0. Its maximum is at p=(r,y).
If y\ge kr, the corner p+u has squared norm at least

\[
\begin{aligned}
 (r+a)^2+(kr+b)^2
  &=(1+k^2)r^2+1+2r(a+kb)\\
  &\ge(r+1)^2+k^2r^2.
\end{aligned}
 \tag{7}
\]

The last step follows from (6) and k>1/2.

In case II, the maximum is at the corner q=p+v. If
\(q_y\ge k(r+b)\), the further corner q+u has first
coordinate r+a+b and second coordinate at least
\(kr-(1-k)b>0\). Positivity follows already from
\(r\ge59/60\), b\le1, and k=13/20. Using (6), its
squared norm is at least

\[
\begin{aligned}
 (r+1+b/2)^2+(kr-(1-k)b)^2
  &=(r+1)^2+k^2r^2\\
  &\quad+b\bigl[1+(1-2k(1-k))r\bigr]
        +b^2\bigl[1/4+(1-k)^2\bigr]\\
  &\ge(r+1)^2+k^2r^2.
\end{aligned}
 \tag{8}
\]

Here \(2k(1-k)=91/200<1\). The common lower bound in
(7)--(8) increases for r>0, and at r=59/60 it exceeds Q by
the exact positive margin

\[
 \left(\frac{119}{60}\right)^2
  +\left(\frac{13}{20}\frac{59}{60}\right)^2-Q
                   =\frac{4633}{180000}>0.
 \tag{9}
\]

This contradicts disk containment in both cases. Reflection across the
horizontal axis excludes a nonnegative maximum of -Y-kX. Thus (3)
holds at every vertex and hence throughout S. \(\square\)

The lemma is invariant under rotations: if \(n\cdot x\ge59/60\)
throughout a contained unit square, every direction of its points is
within angle beta of n.

## 2. A radial leaf puts its articulation near the origin

**Lemma 2.1.** Let L be a positive radial S or D leaf and A its
neighbor in the selected certificate. Then

\[
                    \operatorname{dist}(0,A)
                    \le\max(\delta,0).
 \tag{10}
\]

*Proof.* In the D case, the selected nonradial point-normal convention
gives the full aligned articulation domain

\[
 A=[R-\sqrt2-1,R-\sqrt2]
       \times[t-1/2,t+1/2],\qquad |t|<1/2.
 \tag{11}
\]

Since 0<R-sqrt(2)<1 in (1), the origin belongs to A, and (10)
follows. This is the D leaf/articulation statement in
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md and
TRIANGLE_LEAF_CORE_REDUCTION.md; it uses only the leaf edge, not the
other edges at A.

In the S case the leaf's inner application point is p=(d,0), a
rightmost support point of A. If A is aligned, its full domain is

\[
 A=[d-1,d]\times[t-1/2,t+1/2],\qquad |t|\le1/2.
 \tag{12}
\]

Its distance from the origin is exactly max(d-1,0), as its vertical
interval contains0.

If A is tilted, its two inward side vectors at p can be written

\[
                 u=(-a,-b),\qquad v=(-b,a),
                 \qquad a,b>0,\quad a^2+b^2=1,
 \tag{13}
\]

after a possible reflection; no ordering of a and b is imposed.
In these orthonormal coordinates the origin has coordinates (da,db)
relative to p. Thus its squared distance from A is

\[
       \max(da-1,0)^2+\max(db-1,0)^2.
 \tag{14}
\]

At most one of these two terms is positive, because
\(d<61/60<\sqrt2\) and
\((da)^2+(db)^2=d^2<2\). Each possible positive coordinate
excess is at most d-1. This proves (10), including d\le1 and
both reflected tilted families. \(\square\)

## 3. A unit-square center and a physical normal channel

Every contained unit square with center c and orthonormal side axes
u,v satisfies the farthest-corner inequality

\[
 R^2\ge |c|^2+\frac12+|c\cdot u|+|c\cdot v|
       \ge |c|^2+|c|+\frac12.
\]

Consequently

\[
                              |c|\le T-\frac12=d+\frac12.
 \tag{15}
\]

Suppose a positive path A--U--C has a zero-circle-weight,
degree-two internal body U. Its physical force and torque balance
give a unit normal n, an actual application p_A in A, and an actual
application p_C in C, with

\[
 p_C-p_A=w n,\quad w\in\{1,\sqrt2\},\qquad
 n\cdot x\le\alpha:=n\cdot p_A\quad(x\in A),\qquad
 n\cdot x\ge\alpha+w\quad(x\in C).
 \tag{16}
\]

These are the normal-channel conclusions of
PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md. Shared-side applications may
be their actual weighted means; (16) retains them exactly. The proof
below only needs w\ge1, so it also covers any longer positive
normal channel if such a channel is otherwise feasible.

The projection halfwidth of C is at least1/2. Combining its minimum
projection in (16) with (15) gives

\[
                  \alpha+w+\frac12
                  \le n\cdot c_C\le |c_C|\le d+\frac12,
                  \qquad \alpha\le d-w\le\delta.
 \tag{17}
\]

## 4. The complete boundary-detour exclusion

**Theorem 4.1.** Let a unit square A satisfy (10), and suppose it is
one endpoint of a physical normal channel (16) with w\ge1. No
circle-touching unit square D in the same packing can physically
touch both A and C.

*Proof.* By (10), a point of A at minimum distance from0 gives

\[
                    \alpha\ge-\max(\delta,0).
 \tag{18}
\]

If delta<0, (18) and (17) would give 0\le alpha\le delta<0.
Therefore

\[
                    \delta\ge0,\qquad
                    -\delta\le\alpha\le\delta,
                    \qquad R\ge R_0:=\frac{\sqrt{17}}2.
 \tag{19}
\]

Every point of C now has n-projection at least

\[
                     \alpha+w\ge1-\delta>\frac{59}{60}.
 \tag{20}
\]

Choose genuine contacts p in C intersect D and q in A intersect D.
Lemma 1.1, applied in the n frame, shows that

\[
                         \angle(n,p)<\beta,
                         \qquad \beta=\arctan\frac{13}{20}.
 \tag{21}
\]

The notation angle denotes the smaller angle in [0,pi] between
nonzero vectors. The point p is nonzero by (20).

Because D contains a circle corner z, the unit-square diameter gives

\[
                         |q|\ge |z|-|z-q|
                              \ge R-\sqrt2>\frac35.
 \tag{22}
\]

For the final strict inequality, (19) gives
\(R\ge\sqrt{17}/2>41/20\), while \(\sqrt2<29/20\).
Also q lies in A, so (17) and (2) imply

\[
                  \frac{n\cdot q}{|q|}
                     \le\frac{\delta}{|q|}<\frac1{36}.
 \tag{23}
\]

In particular q is nonzero and

\[
                            \angle(n,q)>\arccos\frac1{36}.
 \tag{24}
\]

For R\ge R_0, Section2 of
BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md proves that **every**
circle-touching unit square has angular shadow shorter than

\[
                             \omega=\arctan\frac{23}{16}.
 \tag{25}
\]

That local shadow theorem has no seven-cycle hypothesis; the seven-cycle
assumption is used only later in its source manuscript. Since p,q
belong to the same circle-touching D, it gives
\(\angle(p,q)<\omega\). The angular metric triangle inequality
and (21) therefore give

\[
                            \angle(n,q)<\beta+\omega.
 \tag{26}
\]

Finally \(\tan\beta\tan\omega=299/320<1\), so
\(\beta+\omega<\pi/2\), and

\[
 \cos(\beta+\omega)=\frac{21}{\sqrt{446665}}>
                       \frac1{36}.
 \tag{27}
\]

The last comparison is exact: \(756^2=571536>446665\).
Thus \(\beta+\omega<\arccos(1/36)\), contradicting
(24)--(26). \(\square\)

No force or torque condition at D was used. It may be a boundary body
whose circle weight is zero. Likewise C was not required to touch the
circle. All orientations and shared-contact degeneracies are retained.

## 5. Whole-family consequence for C1.4.b1

Let the positive component be the four-cycle

\[
                             A-U-C-D-A
\]

with a pendant leaf L attached to A. Suppose U has zero circle weight
and D physically touches the circle. The radial leaf theorem gives
one of the full D/S articulation families of Lemma 2.1. The clear
degree-two body U gives (16). The positive edges CD and DA are actual
physical contacts. Theorem 4.1 supplies a contradiction.

**Corollary 5.1.** In the C4-with-leaf branch of C1.4.b1, the
pattern with exactly two adjacent loaded block vertices is entirely
excluded. This includes both radial leaf types, all articulation poses,
all circle-corner masks, all zero-weight physical contacts, and every
completion by the other four squares.

More generally, whenever a zero-load cycle vertex is adjacent to the
leaf articulation, the articulation's other cycle neighbor cannot
physically touch the circle, even with zero multiplier.

The C4 branch still retains its opposite-loaded-pair and
three-loaded-block patterns, as well as the already separately
excluded two-load completion class. The two diamond attachment branches
are not closed by this theorem. The entire C1.4.b1 cell and the
unrestricted nine-square theorem therefore remain open.

No Lean compilation, CI, numerical pose search, or unproved owner-axis
assumption is a premise of this argument.
