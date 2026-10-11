# Angular order of actual contact-moment cycles

## Status

This note proves a geometric restriction on **every exterior square**, not
only squares touching the containing circle or vertices of degree two.
When the disk radius is below two, a positive contact moment enters an
exterior square before the ray through its nearest point to the origin,
and leaves after that ray. Consequently any directed positive-moment cycle
which avoids the central square has positive winding around the origin.
No planarity of the square contact graph is assumed.

The result applies to the physical contact forces in
[HUMAN_CONTACT_EQUILIBRIUM.md](HUMAN_CONTACT_EQUILIBRIUM.md). The analytic
central theorem and the lower bound
[HUMAN_ANALYTIC_LOWER_BOUND.md](HUMAN_ANALYTIC_LOWER_BOUND.md) now make its
radius hypotheses available for an eight-square minimizer. The remaining
issue is to control cycles through the central square and the placement
of squares outside a selected stress cycle. This note does not yet force
the twin-transmitter scaffold or the five-corner obstruction.

Write $a\times b=a_xb_y-a_yb_x$ and $J(a_x,a_y)=(-a_y,a_x)$.
All squares have side one, have disjoint open interiors, and lie in the
closed disk $D_R$ centered at the origin.

## 1. Every contact line lies less than one unit from the origin

Let two squares touch at $z$, and let $n$ be any unit separating normal,
directed from the first square to the second. Their common support line is

$$
n\cdot x=d,\qquad d=n\cdot z.
$$

The projection width of a unit square in every unit direction is at least
one. The first square's projection interval therefore extends at least
one unit below $d$, and the second square's extends at least one unit
above $d$. Both intervals lie in $[-R,R]$. Hence

$$
1-R\le d\le R-1.                                      \tag{1}
$$

In particular, for $R<2$,

$$
\boxed{|n\cdot z|<1.}                                 \tag{2}
$$

This assertion does not need either square to own the chosen normal. It
also applies to a contact at a vertex and to any effective contact point
obtained by averaging forces along a shared segment.

## 2. Every contact point lies in a smaller concentric disk

The separate point bound is

$$
\boxed{|z|^2\le R^2-1.}                               \tag{3}
$$

To prove it, choose a separating normal $n$ owned by the first square,
directed toward the second. Such an owner exists by the separating-axis
theorem. Since $z$ is on the first square's supporting edge,
$z-n$ belongs to that square. If $z\cdot n\le0$, then

$$
R^2\ge |z-n|^2=|z|^2+1-2z\cdot n\ge |z|^2+1.
$$

If $z\cdot n>0$ and the second square has a parallel supporting edge,
$z+n$ belongs to it and gives the same conclusion. Otherwise the second
square's support face is the vertex $z$. Let $u,v$ be its orthogonal unit
edge vectors directed into that square. Because it lies in
$n\cdot(x-z)\ge0$, both $n\cdot u,n\cdot v$ are nonnegative. The
identity

$$
z\cdot n=(n\cdot u)(z\cdot u)+(n\cdot v)(z\cdot v)>0
$$

shows that at least one of $z\cdot u,z\cdot v$ is positive. The
corresponding endpoint $z+u$ or $z+v$ has squared norm greater than
$|z|^2+1$ and belongs to the second square. This proves (3) in every
case.

Unlike a numerical enclosure of contact coordinates, (3) holds uniformly
for all orientations and all possible contact pairs.

## 3. The nearest-point ray orders incoming and outgoing moments

A square is called **exterior** here if its closed set omits the origin.
Let $v$ be its unique nearest point to the origin, and put
$\theta=\arg v$. Since $v$ minimizes squared distance on a convex set,

$$
v\cdot(z-v)\ge0\qquad(z\in S).                       \tag{4}
$$

In particular $v\cdot z\ge|v|^2>0$. There is therefore a unique lift
of the argument of every point of $S$ to
$(\theta-\pi/2,\theta+\pi/2)$.
The projection interval in the direction $v/|v|$ starts at $|v|$, has
width at least one, and ends at most at $R$. Consequently

$$
0<|v|\le R-1<1.                                         \tag{4a}
$$

### Angular-order theorem

Suppose $R<2$. At any actual contact point $z$ of the exterior square
$S$, let $n$ be a unit **outward** separating normal of $S$. With the
argument lift just specified,

$$
\begin{aligned}
z\times n>0&\quad\Longrightarrow\quad \arg z\ge\theta,\\
z\times n<0&\quad\Longrightarrow\quad \arg z\le\theta.
\end{aligned}                                           \tag{5}
$$

The normal need not be an axis of $S$. At a vertex it may be any actual
separating normal in that vertex's outward normal cone.

#### Proof: the origin is opposite a corner

Choose square coordinates so that

$$
S=[x,x+1]\times[y,y+1],\qquad x>0,\ y>0.
$$

Its nearest point is $(x,y)$. The far right and far top faces cannot
contain a contact in their relative interiors: their outward normals
give $n\cdot z=x+1>1$ or $y+1>1$, contrary to (2). Nor can the far
vertex $(x+1,y+1)$ be a contact. At that vertex $n=(a,b)$ has
$a,b\ge0$ and $a^2+b^2=1$, so

$$
n\cdot z=a(x+1)+b(y+1)>a+b\ge1.
$$

On the near bottom face, $n=(0,-1)$, so $z\times n=-z_x<0$ and
$\arg z\le\arg(x,y)$. On the near left face, $n=(-1,0)$, so
$z\times n=z_y>0$ and $\arg z\ge\arg(x,y)$.

At the bottom-right vertex the normal cone has $n_x\ge0,n_y\le0$;
its moment is strictly negative and its argument is below $\theta$.
At the top-left vertex both conclusions reverse. The nearest vertex
itself has argument exactly $\theta$, so either sign of moment there
satisfies (5). This exhausts the boundary.

#### Proof: the nearest point is on a side, including its endpoints

Choose coordinates so that

$$
S=[x,x+1]\times[y,y+1],\qquad x>0,\quad y\le0\le y+1.
$$

The nearest-point ray is the positive horizontal axis. The far right
face again cannot have a contact in its relative interior, by (2).
On the left face the moment for the outward normal $(-1,0)$ is $z_y$,
which has the same sign as $\arg z$. The bottom face has strictly
negative moment and nonpositive argument; the top face has strictly
positive moment and nonnegative argument. The near left vertices have
the same respective signs, by their outward normal cones.

It remains to check the two far right vertices; their normals may be
owned by the other square. At the upper vertex write

$$
z=(X,Y),\quad X=x+1>1,\quad Y=y+1\ge0,
\qquad n=(\cos\phi,\sin\phi),\quad0\le\phi\le\pi/2.
$$

If $z\times n\le0$, then $\phi\le\arg z$ and

$$
n\cdot z=|z|\cos(\arg z-\phi)
          \ge |z|\cos(\arg z)=X>1,
$$

contradicting (2). Thus any actual contact there has positive moment,
as (5) requires. Reflection in the horizontal axis gives a negative
moment at any contact at the lower right vertex. This also handles
$Y=0$ or $y=0$. The theorem follows.

The proof used neither circle contact nor force balance. In particular,
it covers force-free exterior squares with three or more positive
stress edges.

## 4. Directed exterior contact cycles wind around the origin

Direct an actual contact from square $S_i$ to square $S_j$ when its
selected normal points from $S_i$ to $S_j$ and

$$
z_{ij}\times n_{ij}>0.                                  \tag{6}
$$

For physical stresses this is exactly the orientation of a positive
moment: the force on the source has negative torque and the force on
the target has positive torque. A contact entering a square has
negative moment when expressed using that square's outward normal;
a contact leaving it has positive moment.

Consider a directed cycle of distinct exterior squares. In each square
join its incoming contact point to its nearest point, and that nearest
point to its outgoing contact point, using straight segments. All these
segments lie in the square and avoid zero. By (5), the argument is
nondecreasing from the incoming contact through the nearest-point ray
to the outgoing contact. On a straight segment this follows also from

$$
\frac{d}{ds}\arg(a+s(b-a))
   =\frac{a\times b}{|a+s(b-a)|^2},
$$

and from the fact that the two endpoint arguments differ by less than
$\pi$, by (4).

Concatenating these paths gives a closed curve in the union of the
cycle squares, with nondecreasing lifted argument. Its total argument
change is an integer multiple of $2\pi$. That multiple is positive,
as the following degeneracy check shows.

### A cycle cannot have zero total argument change

If the total change were zero, all its contacts and all its nearest
points would lie on one fixed ray. The boundary classification in
section 3 says that an actual contact on the nearest-point ray is
either the nearest vertex itself, or lies on a square side along that
ray. A nearest point in the relative interior of a transverse side has
zero moment and so cannot occur in (6).

At a nearest vertex the ray directed away from zero belongs to the
square's inward wedge. If it is in the interior of that wedge, a
second square with the same nearest-point ray cannot touch there:
its local inward wedge contains that ray too, giving an open overlap.
This remains true if the second square has a side along the ray,
because its local half-plane or near-endpoint wedge occupies one side
of the ray and intersects the first wedge. The far endpoint of that
side has radius greater than one, while the first square's nearest
vertex has radius less than one by (4a), so that exceptional endpoint
cannot coincide with it. Thus at every contact in the
hypothetical zero-change cycle, both squares must have sides along the
ray and frames parallel to it.

Two such squares on the same side of the ray can separate at a contact
on the ray only in the radial direction, which has zero moment. For a
positive moment they must lie on opposite sides of the ray, and the
normal must point from its clockwise side to its counterclockwise
side. A square on the counterclockwise side cannot then be the source
of the next positive-moment edge on that ray. There is no directed
cycle of such contacts. This contradiction proves strict positivity.

We have established:

$$
\boxed{\text{Every directed positive-moment cycle of exterior squares
has positive winding about zero.}}                       \tag{7}
$$

This assertion is about a geometrically constructed closed curve. It
does not infer planarity of the abstract contact graph. Repeated
contact points and crossings at a point shared by several squares are
allowed; the argument lift and the zero-change exclusion cover them.

### The whole central square has the same positive winding

If another square $C$ contains zero in its open interior, that open
interior is disjoint from every closed exterior square in the cycle.
Indeed a common point in the open set $C$ could be approximated from
the exterior square's interior, contradicting interior disjointness.
The constructed curve therefore avoids $\operatorname{int}C$.
Moving the base point from zero to any point of $\operatorname{int}C$
along their segment cannot change the winding number: it is an integer
and varies continuously while the base point stays off the curve.
Thus the cycle winds positively around every point of the open central
unit square, not merely around its center.

As a small consequence, such a cycle contains at least four squares.
Replace each two-segment path inside one exterior square by the straight
segment joining its two contacts. Convexity gives a homotopy avoiding
$C$, so the winding around $C$ is unchanged. A three-square cycle would
give a triangle containing $C$ in its bounded region. Each side of that
triangle has length at most the square diagonal $\sqrt2$. Its area is
at most $\sqrt3/2<1$ (the maximum for three sides bounded by $\sqrt2$
is the equilateral triangle), whereas it would contain the unit-area
square $C$. This is impossible. Cycles of one or two squares are not
cycles in the simple positive-stress graph.

## 5. What the result removes, and what it still leaves

At an eight-square minimizer the analytic results now give

$$
\sqrt2+\tfrac12<R_8<2
$$

and one square whose open interior contains zero. Every other closed
square omits zero. The physical stress theorem supplies a nonzero
moment circulation. Its finite directed flow decomposition supplies
positive-moment cycles. Any one that avoids the central square is
covered by (7), even if some of its exterior vertices have higher
degree or carry no circle force.

This eliminates a possible angular reversal at an exterior force-free
branch. It does **not** assert that a particular stress has a cycle
avoiding the central square. Indeed the known construction can carry
its stress around a cycle through a central horizontal transmitter;
the second, exterior transmitter may have zero weight in that stress.
Choosing or forcing the second transmitter is a substantive remaining
step.

Nor does winding by itself count the squares outside a chosen cycle or
force their frames to agree. A sharp lower-bound proof still needs an
argument that either produces the shared-neighbor pair of interior
degree-two squares, or gives an equally strong projected-width
obstruction in every remaining contact structure.

## 6. A local force-free branch that the angular theorem permits

The angular-order theorem does not make every force-free exterior square
a straight transmitter. The following exact four-square example records
why that additional step needs global minimality or further packing
information.

Let

$$
K=[1/10,11/10]^2.
$$

Let $L$ have center $(-3/5,6/5)$ and frame
$n=(-3/5,4/5),Jn=(-4/5,-3/5)$. Let $M$ be its reflection in the line
$x=y$. Their centers and the vertices of $L$ are

$$
p_M=(6/5,-3/5),\qquad
(-1/2,19/10),\ (-13/10,13/10),\
(-7/10,1/2),\ (1/10,11/10).
$$

Finally let $C$ have frame
$((1,1)/\sqrt2,(-1,1)/\sqrt2)$ and center

$$
p_C=\left(\frac1{10}-\frac1{2\sqrt2},
          \frac1{10}-\frac1{2\sqrt2}\right).
$$

The square $C$ contains zero in its open interior. It touches $K$ at
$(1/10,1/10)$ and is strictly below $L$ and strictly to the left of $M$:
its largest coordinate is $1/10+1/(2\sqrt2)<1/2$.
The squares $K,L$ touch at $(1/10,11/10)$, with normal
$(-3/5,4/5)$ directed from $K$ to $L$; reflection gives the $K,M$
contact at $(11/10,1/10)$. The squares $L,M$ are separated horizontally,
since $L$'s rightmost coordinate is $1/10$ and $M$'s leftmost is $1/2$.
These observations check all six pairs.

All four squares lie in the disk of squared radius

$$
\frac{193}{50}=3.86<\frac{9789}{2500}.
$$

The largest squared vertex norm of $L$ or $M$ is
$1/4+361/100=193/50$; for $K$ it is $121/50$.
For $C$, putting $a=1/10-1/(2\sqrt2)$, the vertex norm squares are
$(a\pm1/\sqrt2)^2+a^2<2$, so its containment is strict as well.

Assign the following outward contact normals and weights on $K$:

$$
\begin{array}{c|c|c}
\text{contact point}&\text{outward normal}&\text{weight}\\ \hline
(1/10,11/10)&(-3/5,4/5)&1\\
(11/10,1/10)&(4/5,-3/5)&1\\
(1/10,1/10)&(-1,-1)/\sqrt2&\sqrt2/5.
\end{array}
$$

Their weighted normal sum is zero. Their moments are respectively
$37/50,-37/50,0$, and hence also sum to zero. Thus the circle-free
exterior square $K$ has an exactly balanced three-force branch. Its
outward normals do not lie in an open half-plane, and its two nonradial
forces are not opposite.

This example is not a radius-minimizing eight-square packing and does
not assert equilibrium at the other three squares. It disproves the
stronger local assertion that disk containment, a central square, and
force and moment balance at one exterior square already force a
degree-two transmitter.
