# Two radial S leaves cannot share a triangle articulation

**Status: complete hand proof; root and separate independent hand audits passed.** Let the
positive component consist of a triangle A,B,C and two pendant bodies
L1,L2, both attached to A. If both leaves have radial S type, the core
is impossible throughout

\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
 \tag{1}
\]

The theorem includes all articulation orientations, side applications
and their variable means, all circle-corner masks of B,C, and arbitrary
positive weights. It does not require a bound on the other four squares.
The D/D and D/S leaf-type branches of this layout, and the layout with
two different articulations, remain separate.

## 1. Exact common inputs

Put

\[
 d=\sqrt{R^2-\tfrac14}-1,
 \qquad r=R-\sqrt2,
 \qquad \sigma=1/\sqrt2.
\]

The uniform bounds used below are

\[
 d>\frac{91}{100},\qquad d<\frac{61}{60},\qquad
 r>\frac{67}{120}>\frac59,
 \qquad \sigma<\frac{71}{100}.
 \tag{2}
\]

The first is the lower-endpoint calculation in
S_LEAF_TRIANGLE_EXCLUSION.md; the second follows from
\(\sqrt{R^2-1/4}<121/60\). For the third use
\(R\ge79/40\), \(\sqrt2<17/12\).

Each S leaf has its inward application point \(p_i=d n_i\),
where \(n_i\) is its unit outward radial direction. That point
belongs to A's supporting face with normal \(n_i\). Its circle
resultant is a positive multiple of \(n_i\). Two leaves with the
same direction would be the same physical square, and are excluded.

A is physically circle-clear by the radial-bridge endpoint theorem.
B and C are loaded: each is a degree-two triangle vertex and cannot
be a clear transmitter with touching neighbors. Their positive circle
corners are pairwise acute, including corners on the same body.
Global force balance gives

\[
                   m_B+m_C=-\alpha n_1-\beta n_2,
                   \qquad\alpha,\beta>0.
 \tag{3}
\]

We use two elementary consequences repeatedly. First, any point of
a circle-touching unit square has norm at least r, by its diameter
\(\sqrt2\). Second, if a circle point z is farther than
\(\sqrt2\) from A, it cannot be a circle corner of a square
touching A.

**Acute-arc observation.** Suppose a closed circle arc of angular
length at least \(\pi/2\) and less than \(\pi\) is inaccessible
to every circle corner of a neighbor of A. The direction of the
positive sum of the B,C circle corners cannot lie in the interior of
that arc. Indeed a finite pairwise acute collection of nonzero planar
vectors lies in one open angular interval of length less than
\(\pi/2\). Its positive sum is in the same interval. Such an
interval, with its endpoints outside the inaccessible arc, cannot
cross that arc. The same conclusion holds for an inaccessible arc
of exactly \(\pi/2\).

The two support faces of A containing \(p_1,p_2\) are either sides
or unique vertices. These cases are treated exhaustively below.

## 2. If one S application is on a side support face

Rotate that leaf east. Its application is \((d,0)\), and A has
the full aligned form

\[
                   A=[d-1,d]\times[t-1/2,t+1/2],
                   \qquad |t|\le1/2.
 \tag{4}
\]

The second leaf cannot use the same direction. The opposite side
normal would require \(2d=1\), which contradicts (2). If it
uses an adjacent side normal, reflect vertically so it points north.
Then \(t=d-1/2\), \(d\le1\), and

\[
                         A=[d-1,d]^2.
 \tag{5}
\]

Otherwise the second application is a unique vertex. A right vertex
has first coordinate d, so norm d forces its height to be zero; this
would repeat the first leaf. At a left vertex, radial support requires
\(d-1\le0\). Reflect vertically so its height is positive.
The vertex and articulation are

\[
 p_2=(d-1,Y),\qquad Y=\sqrt{2d-1},
 \qquad A=[d-1,d]\times[Y-1,Y].
 \tag{6}
\]

Here \(d\le1\) and \(Y>9/10\). The second leaf direction
has angle \(\eta\in[\pi/2,2\pi/3)\): its negative horizontal
component has absolute value less than \(1/10\), while its
vertical component before normalization exceeds \(9/10\).
The adjacent-side case has \(\eta=\pi/2\).

In both (5) and (6),

\[
                          A\subset[-1/10,\infty)^2.
 \tag{7}
\]

Every circle point with angle between \(5\pi/6\) and
\(5\pi/3\), i.e. 150 to 300 degrees, is more than
\(\sqrt2\) from A. On the first 30 degrees of this arc its
first coordinate is at most \(-R\sqrt3/2\), giving distance
at least

\[
 R\sqrt3/2-1/10
   >\frac{79}{40}\frac56-\frac1{10}
   =\frac{371}{240}>\frac32>\sqrt2.
\]

The last 30 degrees give the same bound in the second coordinate.
On the intervening southwest quadrant, the distance to the shifted
northeast quadrant in (7) is at least
\(R-\sqrt2/10>\sqrt2\). This last bound follows also by
clipping the two coordinates at \(-1/10\): the clipped point
has norm at most \(\sqrt2/10\).

This is an inaccessible 150-degree arc. The direction of
\(-\alpha n_1-\beta n_2\) is strictly between \(\pi\) and
\(\pi+\eta<5\pi/3\), inside that arc. Equations (3) and the
acute-arc observation contradict each other. Thus every case with
at least one side support face is excluded, including support-face
endpoint means.

## 3. Two adjacent vertex applications

Suppose now that both applications are unique vertices and they are
adjacent vertices of A. They have the same norm d. Rotate their
common side vertically. The equal norms make the two endpoints
symmetric about the horizontal axis. Their radial normals must point
outward from their common side, so after reflection

\[
 A=[a-1,a]\times[-1/2,1/2],
 \qquad p_1=(a,1/2),\quad p_2=(a,-1/2),
 \qquad a=\sqrt{d^2-1/4}>0.
 \tag{8}
\]

Both leaf directions have positive first coordinate. From (2),

\[
                   \frac{19}{25}<a<1,
                   \qquad 0<1-a<\frac6{25}.
\]

Every point of A's left face consequently has norm strictly less than

\[
 \sqrt{(6/25)^2+1/4}<\frac59<r.
 \tag{9}
\]

The squared comparison in (9) is
\(769/2500<25/81\). Therefore no circle-touching square can
contact A on that face.

But the sum of the two positive leaf forces has positive first
coordinate. Force balance at the unloaded A requires at least one
of its two triangle normals to have negative first coordinate.
Such a normal supports A at its left face or one of that face's
endpoints, both excluded by (9). This is a contradiction.

## 4. Two opposite vertex applications

The remaining possibility is a pair of opposite vertices. Their equal
norms make A's center perpendicular to their diagonal. In a suitable
orthonormal frame, after reflection,

\[
 A=\{(X,Y):|X|+|Y-h|\le\sigma\},
 \qquad p_1=(\sigma,h),\quad p_2=(-\sigma,h),
 \qquad h=\sqrt{d^2-1/2}>0.
 \tag{10}
\]

Radial support at both vertices requires \(h\le\sigma\):
the outward normal cones there are the two 90-degree cones about
their horizontal diagonal directions. Thus \(d\le1\). The
bounds (2) give

\[
 h>\frac{57}{100},\qquad
 0\le k:=\sigma-h<\frac7{50}.
 \tag{11}
\]

In particular A satisfies all three half-plane bounds

\[
                      Y\ge-k,\qquad Y+X\ge-k,
                      \qquad Y-X\ge-k.
 \tag{12}
\]

The whole lower circle arc from \(7\pi/6\) to \(11\pi/6\),
i.e. 210 to 330 degrees, is inaccessible to neighbors of A.
Write its points as
\(z=(\pm R\sin\phi,-R\cos\phi)\),
\(0\le\phi\le\pi/3\). If \(\phi\le\pi/6\),
the first bound in (12) gives distance at least

\[
 R\sqrt3/2-k
   >\frac{79}{40}\frac56-\frac7{50}
   =\frac{1807}{1200}>\frac32>\sqrt2.
\]

If \(\pi/6\le\phi\le\pi/3\), use the appropriate
diagonal half-plane in (12). The perpendicular distance is at least

\[
 \frac{R(\sin\phi+\cos\phi)-k}{\sqrt2}
 >\frac{(79/40)(4/3)-7/50}{\sqrt2}
 =\frac{187}{75\sqrt2}>\sqrt2.
\]

The bound \(\sin\phi+\cos\phi\ge(1+\sqrt3)/2>4/3\)
holds on this interval. Thus the entire stated 120-degree arc is
inaccessible.

The two positive leaf directions have angles \(\eta\) and
\(\pi-\eta\), where
\(\eta=\arctan(h/\sigma)\in(\pi/6,\pi/4]\).
For the lower bound, (11) and \(\sigma<71/100\) give
\(h/\sigma>57/71>1/\sqrt3\). Consequently every positive
combination of these two leaf vectors has its negative direction
strictly inside the inaccessible lower arc. This again contradicts
(3) and pairwise acuteness of the B,C circle corners.

## 5. Complete S/S conclusion and exact remaining scope

Two distinct support faces of a square are covered by the side case,
or are two adjacent or two opposite vertices. Repeating a direction
would repeat the same S leaf. These are all possibilities, including
the limiting cases whose support face is a side rather than a unique
vertex. Sections 2--4 therefore prove:

**Theorem 5.1.** A positive triangle with two pendant radial S
leaves attached to the same articulation cannot occur anywhere in (1).
No choice of circle-corner weights, application means, or independent
B/C orientations was omitted.

This theorem closes the full S/S leaf-type branch of the
same-articulation layout. It does not close C1.3.b2: D/D and D/S at
one articulation, and the two-distinct-articulation layout, remain to
be completed. No Lean compilation or CI was run.
