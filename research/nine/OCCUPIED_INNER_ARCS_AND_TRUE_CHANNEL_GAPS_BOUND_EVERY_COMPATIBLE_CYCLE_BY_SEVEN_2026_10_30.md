# Occupied inner arcs and actual channel gaps bound every compatible cycle by seven

**Date:** October 30, 2026 UTC. **Status:** complete proposed geometric
metric budget and full marked-cycle theorem, awaiting independent full
review. All earlier frozen angular sources remain unchanged.

The main result is uniform in the number of boundary marks, internal
orientations, endpoint degrees and cyclic run placements. Every compatible
physical marked cycle has at most seven actual bodies. In particular
every eight- and nine-body simple positive cycle is excluded across all
load counts in this same-certificate scope. The proof accounts for real
occupied arcs of boundary squares and real set gaps between them; it
does not assign a fictitious inner arc to a circle-clear transmitter.

## 1. Geometry and the force-free metric statement

Let a finite family of actual unit squares have pairwise disjoint open
interiors and lie in the disk centered at O with radius

    79/40<=R<=sqrt(Q), Q=1105/256.

Put

    rho=5/4, tau=rho*pi/4=5*pi/16.

A boundary square physically touches the containing circle, irrespective
of its selected circle weight. Choose any t>=2 distinct boundary squares
S_1,...,S_t, choose one actual outer circle corner on each, and list them
in the cyclic order of those corners. Subscripts are cyclic. Define

    D_i=dist(S_i,S_(i+1)).

**Theorem 1 (actual boundary-gap budget).**

    sum_i D_i < tau*(8-t).                               (1)

The squares may have arbitrary independent orientations and need not
be physically adjacent. All other packing squares remain present.
The chosen corner order is independent of which circle corner is used
on a square, as proved below. It also agrees with center angular order.

Since tau<1, integer lower bounds on these actual consecutive set gaps
have an immediate count consequence. This is the mechanism used for
the complete cycle theorem.

## 2. Complete occupied-arc input, including connectivity

The starting arc estimate is Theorem A of
`CYCLIC_GLOBAL_CONTINUATION.md`, frozen SHA256
`e319e541254f50aceff0d72775386187f1505a5edf817d7f3e5b10ce27bc4984`.
Its full §§2--4 proof is reconstructed here, including all endpoints
and the full connected intersection, so the assembly does not rely
only on its headline conclusion.

### 2.1 The actual square intersects the inner circle in one closed arc

Choose one actual outer circle corner z. Choose **outward** orthonormal
own axes and exchange them so that in those coordinates

    z=(a,b), a>=b>=1/2,
    S=[a-1,a] x [b-1,b], a^2+b^2=q=R^2.                (2)

The bounds a,b>=1/2 follow by comparing the two adjacent corners
with z. These are coordinates with respect to the unchanged disk
origin, not a translation of the disk or square.

Put A=a-1 and B=b-1. The radius window gives

    R<25/12,
    a>11/8>rho,
    a<81/40,
    b<3/2,

and hence

    3/8<A<41/40, -1/2<=B<1/2.                           (3)

Indeed `Q<(25/12)^2`; `a^2>=R^2/2>=6241/3200>121/64`;
`a^2<=R^2-1/4<589/144<(81/40)^2`; and
`b^2<=R^2/2<(25/12)^2/2<9/4`.

The inner-circle intersection lies in the own right halfplane,
because A>0. Parameterize it by
`rho*(cos(phi),sin(phi))` with `-pi/2<phi<pi/2`. Set

    alpha=acos(A/rho),
    beta=asin(B/rho),
    gamma=asin(min(b/rho,1)).

The upper constraint x<=a is redundant because a>rho. The other
three constraints give the exact closed interval

    [max(-alpha,beta), min(alpha,gamma)].

But

    A^2+B^2<(41/40)^2+1/4=2081/1600<rho^2.

If B>=0, then beta>-alpha directly. If B<0, the last strict norm
comparison gives the same conclusion by positive squaring. Thus
the full actual intersection is the single closed arc

    J_S=[beta,min(alpha,gamma)].                        (4)

Its relative interior is in the square's open interior. Its two
limiting endpoints belong to the closed square and may be on its
sides; they are not asserted to be interior.

### 2.2 The two inner faces give an angular width greater than pi/4

The decisive inequality is

    E:=A^2+B^2+sqrt(2)*A*B<25/32=rho^2/2.                (5)

At fixed q, put w=a+b. Since `ab=(w^2-q)/2`,

    E=(1-1/sqrt(2))*q+w^2/sqrt(2)
        -(2+sqrt(2))*w+2+sqrt(2).

This expression is convex in w. The allowed interval runs from
`1/2+sqrt(q-1/4)` to `sqrt(2*q)`, corresponding respectively
to b=1/2 and a=b. This follows from the monotonicity of
`sqrt(q-b^2)+b` for b<=a. It suffices to bound E at those two
endpoint configurations.

At b=1/2, using sqrt(2)>7/5 and (3),

    E=A^2+1/4-(sqrt(2)/2)*A
      <A^2+1/4-(7/10)*A
      <933/1600<25/32.

The polynomial is increasing for A>3/8 and has value 933/1600
at A=41/40. At a=b=R/sqrt(2), using R>sqrt(2) and R<25/12,

    E=(2+sqrt(2))*(R/sqrt(2)-1)^2
      <(626-287*sqrt(2))/288<25/32.

The last comparison is equivalent to `401<287*sqrt(2)`, whose
positive square test is `160801<164738`. This proves (5).

Also `sqrt(2)*A+B>0`, since `sqrt(2)>4/3`, A>3/8 and B>=-1/2.
Squaring positive sides in (5) therefore gives

    sqrt(2)*A+B<sqrt(rho^2-B^2),
    A<rho*cos(beta+pi/4).

Here `|beta|<=asin(2/5)<pi/4`, so beta+pi/4 lies in (0,pi/2).
Monotonicity of cosine implies

    alpha-beta>pi/4.                                    (6)

### 2.3 The parallel strip gives the same strict width

For 1/2<=b<rho, the function

    asin(b/rho)-asin((b-1)/rho)

is nondecreasing. Its derivative is

    1/sqrt(rho^2-b^2)-1/sqrt(rho^2-(b-1)^2)>=0,

because b>=|b-1|. Continuity includes b=rho. Consequently

    gamma-beta>=2*asin(2/5)>pi/4.                       (7)

The strict comparison follows from
`sin(pi/8)=sqrt(2-sqrt(2))/2<2/5`; positive squaring follows,
for example, from sqrt(2)>7/5. If b>=rho, then gamma=pi/2
and beta<pi/4, so gamma-beta>pi/4 directly.

Combining (4),(6),(7), the full closed inner-circle intersection
J_S has angular length strictly greater than pi/4. Its entire
relative interior belongs to the actual open square. This proves
the complete occupied-arc input, not merely the existence of two
test points.

## 3. Every actual boundary corner and the center have their directions in this arc

Let z=(a,b) be any actual outer circle corner, in its outward own
frame (2). The point

    Z=(rho/R)*z

lies in the open square. Each of its two inward own-coordinate
amounts from z is positive and is at most

    (1-rho/R)*R=R-rho<25/12-5/4=5/6<1.

Thus both own coordinates are strictly between their square-side
endpoints. The point Z has norm rho and the same direction as z.
It is in the relative interior of the single arc J_S. This works
for either physical circle corner and for zero selected weights.

For completeness, the center direction is also in that same
relative interior. The farthest-corner inequality gives

    |C|<M=91/60,

with exact excess `31/57600` over Q at M. A physical boundary
center has

    |C|>=R-1/sqrt(2)>rho.

Therefore the radial point `P=rho*C/|C|` is at distance

    |C|-rho<M-rho=4/15<1/2

from C. It lies in the square's open incircle and hence in the
relative interior of J_S.

For each selected boundary square, choose a closed trimmed subarc
I_S of J_S satisfying all of the following:

* its angular length is still strictly greater than pi/4;
* every point of I_S is in the square's open interior;
* it contains the direction of the chosen actual circle corner
  and the center direction in its relative interior.

This is possible because J_S is a single interval of length
greater than pi/4 and both specified directions are strictly
inside it. Trim sufficiently small positive amounts from its
two limiting endpoints. No square or contact point is moved.

The I_S for different actual squares are pairwise disjoint compact
arcs on the same inner circle. Their circular order is therefore
the order of their chosen outer-corner directions and also their
center directions. Any alternative outer corner of the same
square lies in the same J_S, so it cannot change that cyclic order.
This proves the order assertion used in Theorem 1 without a
centered-arc or corner-angle estimate.

## 4. Sum actual occupied arcs and actual gaps

List the selected arcs I_i in this circular order. Let lambda_i
be their angular lengths and delta_i the intervening positive
angular gap from the end of I_i to the beginning of I_(i+1),
with the last gap closing the circle. Then

    lambda_i>pi/4,
    sum_i(lambda_i+delta_i)=2*pi.                       (8)

There may be other actual squares in these angular intervals;
they are merely gaps between the selected occupied arcs, not
asserted empty regions of the physical packing.

The two endpoints of an intervening gap belong to their respective
actual squares S_i,S_(i+1). Their chord distance is at least D_i.
The length rho*delta_i of the intervening circular arc is at least
that chord distance, whether delta_i is below or above pi. Hence

    D_i<=rho*delta_i.

Summing and using the strict occupied lengths in (8) gives

    sum_i D_i<=rho*(2*pi-sum_i lambda_i)
               <rho*(2*pi-t*pi/4)
               =(5*pi/16)*(8-t).

This proves Theorem 1 with its complete set-gap scope. No minor-
angle replacement is made for a large directed gap.

The constant tau=5*pi/16 is strictly less than one. For an exact
elementary verification, `pi<22/7<16/5`; the first inequality
follows from

    22/7-pi=int_0^1 x^4*(1-x)^4/(1+x^2) dx>0.

Polynomial division gives
`x^6-4*x^5+5*x^4-4*x^2+4-4/(1+x^2)`, verifying this identity.

## 5. The complete compatible physical marked-cycle theorem

Let C be a simple cycle of m distinct actual bodies in one retained
physical contact graph. Mark t>=2 of its vertices. Every marked
body physically touches the containing circle. Assume:

1. Each marked-to-marked run has one signed unit direction
   supporting all its successive actual contacts from its first
   endpoint toward its second endpoint.
2. The same actual graph has a compatible physical embedding:
   start with the actual center-to-contact strands and resolve
   their finitely many contact junctions inside arbitrarily small
   disks and strand tubes, without crossings and respecting the
   geometric cyclic order of the incident square sectors.

Marked bodies may have arbitrary additional positive contacts,
chords or attachments. Let j_i count the unmarked internal bodies
on run i, so

    m=t+sum_i j_i.                                      (9)

No upper bound on j_i is assumed or needed in this proof.

### 5.1 The actual cycle order is the actual boundary-corner order

Choose one actual circle corner z_i on each marked body. A circle
point belongs to at most one packing square: at such a corner,
both inward side directions u,v obey `z_i.u,z_i.v<=-1/2` by
containment. Nearby points `z_i-epsilon*z_i` are then in the
square's open interior. Two owners would overlap there.

Join each marked center to its chosen circle corner. The open
spoke lies inside its original square, and different spokes are
disjoint. Each meets the initial center-to-contact drawing only
at its own center. Indeed distinct rays from an interior center
cannot meet away from it, and an actual contact point on the
same ray would have to equal the uniquely owned circle corner.

The finite contact junctions lie strictly inside the containing
disk. Choose their local resolution disks and strand tubes small
enough to avoid all marked spokes. Near a marked center, each
spoke has a direction different from all incident contact rays,
so strand separation preserves its angular sector. Thus the
compatible full graph drawing can retain all spokes, including
at marked vertices with additional edges.

The embedded simple cycle is a Jordan curve strictly inside the
containing circle. Every marked spoke meets it only at its own
center and reaches the outer circle. The open spoke therefore
lies in the exterior of that Jordan curve. These disjoint arcs
across the resulting annulus preserve their cyclic endpoint order.
One proof cuts the annulus along one spoke; a reversal of the
remaining endpoint order in the resulting disk would force two
arcs to cross by Jordan separation. The case t=2 gives the two
complementary orders directly.

Consequently the marked cycle order is the order of the chosen
physical circle corners, up to common reversal. Section 3 now
identifies it with the actual occupied-arc order used in Theorem 1.
No claim that the origin lies inside the drawn cycle is required.

### 5.2 Actual support gaps pay for the actual internal bodies

For a run from marked S_i to marked S_(i+1) with common signed
normal n, actual support equalities telescope to

    n.(c_(i+1)-c_i)=h_i(n)+h_(i+1)(n)
                       +sum_(internal U) 2*h_U(n).

Define its actual internal width reserve

    W_i=sum_(internal U) 2*h_U(n)>=j_i.

For every x in S_i and y in S_(i+1), support inequalities give

    n.(y-x)>=W_i.

Thus their actual set distance satisfies

    D_i>=W_i>=j_i.                                      (10)

This statement retains every actual internal orientation and
contact mean. No collinearity of means, discrete width type or
moment equation is used.

Apply Theorem 1 in the actual order established above:

    sum_i W_i <=sum_i D_i < tau*(8-t).                  (11)

Its left side is nonnegative, so t<8. Since tau<1, (9)--(11)
therefore imply

    m-t=sum_i j_i<=sum_i W_i<8-t,
    m<8.

**Theorem 2 (complete compatible cycle bound).**

    m<=7.                                               (12)

The continuous width-reserve inequality (11) is also retained.
It is stronger than the integer consequence when some actual
internal support widths exceed one.

## 6. Complete physical force caller and original body scope

For a physical translational contact/circle stress, suppose every
unmarked cycle body is unloaded and has true positive degree two
in the entire same retained graph. Its full two-force balance
makes its two positive forces equal and opposite. Propagating
along each run supplies precisely the common signed supporting
normal assumed in Section 5. Actual tight contacts give (10).

All positive forces at marked endpoints remain in the full graph.
Their true degrees may be arbitrary, and their selected circle
weights may be zero provided they physically touch the circle.
The actual normals, means, loads, full degrees and compatible
embedding refer to one retained certificate. A degree-two vertex
only of the displayed cycle cannot replace the full-degree premise.

No torque is required. The theorem applies directly to a compatible
translational certificate and also to a compatible force-and-torque
certificate. It does not identify independently selected stresses.
Examples of compatible drawing constructions are Section 4 of
`PLANAR_STRESS_CORE.md` and Section 5 of
`PHYSICAL_BODY_GRAPH_UNCROSSING.md`; the explicit compatibility
premise above is what the present proof uses.

### 6.1 Every compatible simple positive component has at most seven bodies

If an entire positive component is a simple cycle, mark its
positive-circle-weight bodies. Every unmarked body is then
genuinely unloaded of full degree two.

There are at least two marks. Dot the complete body force
equations with their centers and sum over the component. Actual
tight support gaps give

    2*sum_(circle atoms) lambda*c.z
       =sum_(positive pairs) mu*(h_i+h_j)>0,

so some circle weight is positive. Summing the force equations
without center factors gives `sum lambda*z=0`. This cannot be
supported on only one boundary body: its radius is greater than
5/4>1/sqrt(2), and every corner z has

    c.z>=|c|*(|c|-1/sqrt(2))>0.

Dotting with that body's center would contradict the zero sum.
Thus t>=2, and Theorem 2 applies.

**Every such entire simple positive-cycle component has at most
seven bodies.** This excludes every eight- and nine-body simple
cycle simultaneously over all load counts, load masks, square
orientations, normals and actual physical application means in
the stated compatible single-certificate scope.

### 6.2 The same theorem covers marked chorded cycles

The displayed cycle need not be the whole component. Additional
positive chords and attachments at physically boundary marked
bodies are allowed. Whenever every unmarked body is genuinely
unloaded of full degree two, an eight- or nine-body such cycle
is excluded by the same proof.

Equivalently, mark every physical boundary vertex of a displayed
positive cycle. If all remaining circle-clear cycle vertices
have full degree two, there cannot be zero or one marks: common-
normal support telescoping around the whole cycle, or the single
mark-to-itself run, would equate a strictly positive total gap
to zero displacement. Thus the marked set has at least two
members and Theorem 2 applies.

Accordingly, every surviving compatible eight- or nine-body
cycle must contain a circle-clear vertex with an additional
positive edge beyond its two cycle edges. This is an explicit
remaining branch, not a closure of all chorded blocks.

## 7. What is closed and what remains

The theorem closes the whole compatible simple C8 family, including
the six-, seven- and eight-mark remainders left by the earlier
41/93-degree budget. It also rederives the whole compatible C9
exclusion and covers the broader marked chorded-cycle scope above.

The seven-body record orbit `(2,0,1,0)` is preserved: it has four
marks and total internal reserve three, and
`3<(5*pi/16)*(8-4)=5*pi/4`. Nothing here claims a contradiction
for that sharp seven-body family or for arbitrary large cyclic
blocks with circle-clear branching vertices.

Every original square remains physically present. Extra units are
not assumed inside a ring, aligned, touching, loaded or unstressed.
The proof's accounting charges the real intervening arc lengths
to the real endpoint set gaps. It does not assert that a generic
circle-clear square occupies a quarter-turn inner arc.

No original fine/coarse ledger credit is assigned automatically.
No pose search, finite orientation table, Lean compilation, CI run,
stress replacement, metadata edit or remote publication is asserted.

## 8. Verification and source boundary

The occupied-arc input was read in full and its exact proof was
reconstructed in Sections 2--3, correcting its axis description
to the outward convention used by `[a-1,a] x [b-1,b]`. The full
closed intersection, its relative-interior status, trimmed closed
arcs, actual circle-corner order, large directed gaps and strict
sum have all been stated explicitly.

The physical annular-order and complete force callers are proved
again here at their exact required scope. Thus the mathematical
argument is self-contained apart from elementary Euclidean convex
geometry, elementary trigonometry and Jordan separation. Earlier
frozen manuscripts retain their original bytes and conclusions.
