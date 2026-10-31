# Parallel end-triangle reactions have positive radial work

**Status: complete hand implication; root and separate independent full hand audits passed.**
In the window
\[
                     79/40\le R\le\sqrt{1105}/16,
\tag{1}
\]
let A,B,C be an actual unit-square contact triangle, with B,C
positive degree-two circle-loaded tips. Suppose the two positive
AB,AC reactions on A are parallel. Write c_A for A's center and
M for the total circle-force vector on B,C, including all positive
corner weights.

Then
\[
                              \boxed{c_A\cdot M>0.}
\tag{2}
\]
All actual side means, independently oriented tips, one-/two-circle
masks and the free normal at a tip/tip vertex junction are retained.

Together with BOWTIE_TIP_OWNED_PRESSURE.md this supplies two whole
owner/force branches of the bowtie sign route. Nonparallel reactions
with an articulation-owned normal are not covered by this theorem.

## 1. The full wall domain

Opposite parallel outward normals on A put B,C beyond opposite
support lines of A, whose gap is at least one. They cannot touch.
Thus both normals have the same sign.

If their support on A were a single vertex, both actual applications
would coincide there. In the selected physical convention, the common
inward normal points strictly into each neighboring square: at a
point-only vertex pair the normal strictly exposes both vertices,
and at a relative-side-interior point it points into its half-plane.
A sufficiently short segment in that direction would consequently
be in both B and C interiors. This is impossible.

The support is therefore an A side. Rotate and write its outward
normal as -e_x and its line as x=-s. Let the actual wall applications
be (-s,y_B),(-s,y_C), with magnitudes mu_B,mu_C>0.
Summing the two tip equations gives
\[
                       M=-(\mu_B+\mu_C)e_x.
\tag{3}
\]
The total tip origin moment is zero, so
\[
                    \mu_B y_B+\mu_C y_C=0.
\tag{4}
\]
Each tip lies in x<=-s, their wall applications lie on the same
unit side of A, and |y_B-y_C|<=1.

The mutual contact normal cannot be horizontal: two positive-width
squares with the same rightmost support coordinate cannot be
separated horizontally. Label B,C so its normal from B to C has
negative vertical component. The supporting inequalities at the two
wall points give y_B>=y_C. The corresponding circle resultants
satisfy (m_B)_y>0>(m_C)_y.

All positively weighted circle corners on B,C are pairwise acute:
this is the boundary-contact theorem, and two corners of one body
are acute as well. Their sum points strictly west by (3), so every
such corner has negative x-coordinate. The two tip resultants
are acute to each other. ACUTE_LOADED_CONTACT_GRAPH.md, TheoremA.1,
also gives, for every point p of a loaded tip S,
\[
                 m_S\cdot p>|\det(m_S,p)|.
\tag{5a}
\]
Indeed sum its two strict linear cone inequalities over the positive
circle weights.

Retain first the coincident-wall-mean case y_B=y_C. Equation (4)
makes both heights zero. The common point is (-s,0); negative x
of every positively weighted circle corner and (5a) imply s>0.
If either tip has a unique rightmost vertex, its inward horizontal
ray is strictly inside its tangent quadrant. A small perturbation
of that ray into the other tip's inward half-plane or quadrant
would lie in both interiors. Thus coincidence forces both tips
to be aligned. Neither can have the point in the relative interior
of its wall side, for the same overlap reason. Their vertical
intervals must be [0,1] and [-1,0]. Consequently their common
circle equation is R^2=(s+1)^2+1. If s<=1/2 this is at most13/4,
contrary to (1). Hence s>1/2 already proves (2) in this full
shared-mean endpoint case.

For the rest y_B>y_C. Equation (4) gives
\[
               0<y_B<1,\qquad -1<y_C<0,\qquad
               \Delta=y_B-y_C\le1.
\tag{5}
\]
Here s>0 too. Otherwise both wall points have nonnegative first
coordinate. Inequality (5a) at the upper point forces
(m_B)_y>|(m_B)_x|; at the lower one it forces
-(m_C)_y>|(m_C)_x|. This makes m_B dot m_C<0, a contradiction.

Since c_A has first coordinate 1/2-s, (2) is equivalent to s>1/2.
We now assume
\[
                              0<s\le1/2
\tag{6}
\]
and exclude the entire remaining wall domain.

## 2. A uniform small corner box is strictly circle-clear

Put
\[
                         Y=\sqrt{R^2-(s+1)^2}.
\]
The assumptions give
\[
                 Y^2\ge(79/40)^2-(3/2)^2
                        =2641/1600>(41/32)^2.
\tag{7}
\]
Every unit square with rightmost support x=-s and top support
y=Y-1 is strictly circle-clear.

To verify the assertion, its four vertices have the form
\[
 (-s,Y-1-a),\quad(-s-b,Y-1),\quad
 (-s-a-b,Y-1-b),\quad(-s-a,Y-1-a-b),
\tag{8}
\]
where a,b>=0 and a^2+b^2=1. The first two have horizontal absolute
coordinate at most s+1 and vertical absolute coordinate less than Y.

For the left vertex, the deficit below R^2=(s+1)^2+Y^2 is
\[
\begin{split}
 D_L&=2s(1-a-b)-2ab+2Y(1+b)-1-2b-b^2\\
 &>\frac{41}{16}-\left(a+\frac7{16}b+b^2+2ab\right)>0.
\end{split}
\tag{9}
\]
Here 2s<=1, a+b>=1 and (7) give the first strict bound.
For an exact verification of the last one, take
\[
 Q=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
 \ell=(1,7/16),\quad H=(33/16)I-Q.
\]
The matrix H is positive definite: its first diagonal entry is
positive and det H=305/256>0. Completing the square, for any
unit vector w,
\[
 w^TQw+\ell\cdot w
 \le\frac{33}{16}+\frac14\ell^TH^{-1}\ell
 =\frac{49813}{19520}
 <\frac{41}{16}.
\tag{10}
\]
The exact positive gap is207/19520.

For the bottom vertex the deficit is
\[
 D_D=2s(1-a)+(2Y-1)+2(Y-1)(a+b)-a^2-2ab.
\]
It is greater than4Y-3-2>1/8, since a+b>=1,
a^2+2ab<=2, and Y>41/32. This proves the assertion.

## 3. Every aligned tip, including all wall means, is excluded

Suppose one tip is aligned, so its right support is a side.
Reflect vertically and interchange the names if necessary so it is B.
Its positive upper circle resultant and Y>1 force
\[
                     B=[-s-1,-s]\times[Y-1,Y].
\tag{11}
\]
In particular y_B>=Y-1>0. If C were aligned too, its negative
circle load would put it in
[-s-1,-s] times [-Y,1-Y]. Because Y>1 the two rectangles could
not touch. Thus C has a unique rightmost vertex (-s,y_C).

Let n be the actual BC normal, directed B to C, with n_y<0.
If n_x<0, its support on B is the lower-left vertex. That point
minimizes n on C; the strict support-span lemma makes C's rightmost
coordinate less than -s, a contradiction.
If n_x>0, its support on B is the lower-right vertex (-s,Y-1).
This would be C's unique rightmost vertex, giving y_C=Y-1>0.
If n_x=0, C has right support x=-s and top support y=Y-1;
Section2 makes it strictly circle-clear.

This covers every actual shared-side wall mean, without choosing
an endpoint for that mean.

## 4. The complete two-vertex section chart

Both wall supports are now unique vertices. Write
\[
\begin{split}
 B&=(-s,y_B)+[0,1](-a,b)+[0,1](-b,-a),\\
 C&=(-s,y_C)+[0,1](-c,d)+[0,1](-d,-c),
\end{split}
\tag{12}
\]
with positive components, a^2+b^2=c^2+d^2=1.
Put a=cos theta,b=sin theta,c=cos psi,d=sin psi.
Reflection across the horizontal axis followed by exchanging B,C
lets us assume b<=c.

At horizontal depth x into the common wall, the lower boundary of B
and upper boundary of C are
\[
 \ell_B(x)=
 \begin{cases}y_B-(a/b)x&x\le b,\\
 y_B-1/a+(b/a)x&x\ge b,\end{cases}
\]
\[
 u_C(x)=
 \begin{cases}y_C+(d/c)x&x\le c,\\
 y_C+1/d-(c/d)x&x\ge c.\end{cases}
\tag{13}
\]
Both breakpoints lie in the common depth interval. Nonoverlap and the
downward separator give ell_B>=u_C, with equality at a contact.

If b<c and theta<=psi, the minimum difference is at x=c and
requires Delta=(1+ad-bc)/a>1, contradicting (5).
Otherwise, in the strict b<c case,
\[
 \theta>\psi,\qquad
 \Delta=a+\frac{bd}{c}\le1,\qquad
 T=(-s,y_B)+(-b,-a)=(-s,y_C)+\frac bc(-c,d).
\tag{14}
\]
The actual BC normal is (-d,-c), owned by C.
Equation (14) gives tan psi<=tan(theta/2), while b<c gives
theta+psi<pi/2. Hence
\[
                            0<\psi<\pi/6.
\tag{15}
\]

The b=c case has a=d and Delta=2a<=1. The left vertices are
the unique circle vertices of both tips: their comparisons with the
adjacent vertices give, for example, the strictly positive differences
1+2bs-2ay_B and1+2as+2by_B. Their wall vertices are unshareable
as circle points. Equal circle radius forces y_B=a,y_C=-a.
Vertical force balance gives equal circle weights, (4) gives equal
wall magnitudes, and the mutual force is vertical. Torque then requires
\[
                         a(s+a+b)=b(s+b).
\tag{16}
\]
Its left side minus right side is
s(a-b)+2a^2+ab-1<0, because a<=1/2<b. This is impossible,
for every original free normal at that vertex/vertex junction.

Thus only (14)--(15) remain.

## 5. Both physical circle masks become unique left corners

C's left vertex
\[
                  z_C=(-s-c-d,\ y_C+d-c)
\tag{17}
\]
is strictly farther than either adjacent vertex. The norm differences
are1+2ds-2cy_C>0 and1+2cs+2dy_C>1-2d>0.
Its wall vertex belongs to A and cannot be a circle point.

Furthermore -y_C>1/4. Otherwise its circle equation and (6) give
\[
 R^2\le s^2+\frac{33}{16}+\sqrt{8s^2+\frac12}
 \le\frac{37}{16}+\sqrt{\frac52}
 <\frac{39}{10}<(79/40)^2,
\tag{18}
\]
where sqrt(5/2)<127/80 gives the penultimate bound.

B's left vertex is farther than its lower one, by
1+2as+2by_B>0. Its only competing circle vertex is its upper one.
If that upper vertex touched the circle with y_B<=3/4, then
\[
 R^2\le s^2+\frac{25}{16}+\sqrt{4s^2+\frac94}
 \le\frac{29}{16}+\frac{\sqrt{13}}2
 <\frac{59}{16}<\frac{39}{10},
\tag{19}
\]
using sqrt(13)<15/4. If y_B>3/4, (18) contradicts Delta<=1.
Thus B's unique circle vertex is
\[
                  z_B=(-s-a-b,\ y_B+b-a).
\tag{20}
\]
All physical two-corner masks have been excluded by these comparisons,
rather than by setting a possible corner weight to zero.

## 6. Exact torque and the final all-angle inequality

Put S_B=s+a+b and Y_B=y_B+b-a>0.
Intersect B's horizontal wall-force line with its BC force line.
Collinearity with its unique circle vector gives exactly
\[
             \frac{a(c+d)}c\,Y_B=S_B(b-a).
\tag{21}
\]
All other factors are positive, so b>a and b>1/sqrt(2).

The corresponding intersection at C is (-s-b/c^2,y_C).
Write v=c-d,w=c+d,x=b/c^2. Its circle collinearity gives
\[
                         -y_C=\frac{v(s+x)}{w-x},
                         \qquad w-x>0.
\tag{22}
\]

For every 0<=psi<=pi/6,
\[
                  \frac{3(1+c-d)}{4c^2}-(c+d)\ge0.
\tag{23}
\]
Here is a short full-interval proof. The derivative of the left side is
\[
 \frac{3(-1-d^2+cd+2d)}{4c^3}-(c-d).
\]
The numerator N=-1-d^2+cd+2d increases on this interval, because
N'=2c(1-d)+(c^2-d^2)>0. Its maximum is
(sqrt(3)-1)/4 at pi/6, while c^3>=3sqrt(3)/8.
The fraction is therefore at most
(sqrt(3)-1)/(2sqrt(3)), strictly below the minimum
(c-d)=(sqrt(3)-1)/2. The derivative is negative.
At pi/6 the expression in (23) is zero, proving (23).

If b>=3/4, equations (6),(23) give
\[
 v(s+x)-(w-x)=vs+(1+v)b/c^2-w>0.
\]
Equation (22) would make -y_C>1, contrary to (5).

Thus b<3/4, a>sqrt(7)/4 and b/a<3/sqrt(7)<8/7.
Equation (21) now gives
\[
                  0<Y_B/S_B<1/7.
\]
Consequently its actual circle equation satisfies
\[
 R^2=S_B^2+Y_B^2
 <\frac{50}{49}(1/2+\sqrt2)^2
 <\frac{550}{147}<\frac{39}{10}.
\tag{24}
\]
For the middle inequality use sqrt(2)<17/12.
This contradicts (1), and completes every two-vertex alternative.

The assumption 0<s<=1/2 is impossible. Hence s>1/2, and (3)
gives c_A dot M=(mu_B+mu_C)(s-1/2)>0, as claimed.

## 7. Scope

This is the full parallel-reaction end-triangle sign, with all physical
contact features, masks and means. The loaded tips must each have
exactly two positive pair forces; the theorem is not asserted for a
tip with an additional positive edge.

For the bowtie, a block covered here and a block covered by
BOWTIE_TIP_OWNED_PRESSURE.md, or two blocks covered here, already
contradict M_1+M_2=0. The complete cell still requires nonparallel
articulation-owned and shared-side interfaces not reduced to these
two theorems. All four arbitrary completion squares remain.

No Lean compilation, CI, numerical certificate or post-certificate
normal adjustment is used.
