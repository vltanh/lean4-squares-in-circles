# Contact kernels at a small corner of an origin-containing square

Date: October 27, 2026.

**Status: complete proposed uniform geometric theorems, frozen for full
root and separate independent review.** No original graph, certificate,
shared ledger or remote file is changed.

Keep actual interior-disjoint unit squares in the circle centered at O,
with

    sqrt(17)/2 <= R <= sqrt(Q), Q=1105/256.

Let the actual square H contain O closed and have an actual vertex P
with |P|<1/40. Take its inward own axes as the coordinate axes, so

    H=[-a,1-a] times [-b,1-b],
    P=(-a,-b), 0<=a,b<1/40.

All claims below concern the original physical units and contacts. No
degree, equilibrium, circle multiplier or normal-selection premise is
used in Sections 1--2. Section 3 uses only its explicitly stated two
unchanged positive forces.

## 1. The opposite corner admits no strictly exposing contact

Put W=(1-a,1-b). Suppose an actual contained unit E touches H at an
actual separating normal n=(c,s) from H to E with c,s>0 and
c^2+s^2=1. Its H maximum is the singleton W. Thus W is an actual
minimum-n point of E.

For any unit square with a minimum-n point z, the point z+n belongs
to that unit. At a vertex, the two coefficients of n in its inward
orthonormal axes lie in [0,1]; at an own side, this is the point one
unit directly across the square. These statements retain the full
side and vertex normal-cone endpoints.

Consequently W+n belongs to E, but

    |W+n|^2
      >=2(39/40)^2+1+2(39/40)(c+s)
      >=2(39/40)^2+1+2(39/40)
      =Q+3423/6400>Q.

This contradicts containment. In particular, **no actual unit,
whether physically boundary or clear, can have a contact that strictly
exposes the corner opposite P.**

This is also the opposite-corner calculation in Section 6 of
ROOTED_SMALL_ORIGIN_CORNER_TWO_BOUNDARY_NEIGHBORS.md, SHA256
6ebda6299f692af6380ad36b98420aeb3155cf95a6b586e1df3848807d4cf467.
The present formulation explicitly retains its degree-free scope.

## 2. Physical boundary neighbors of H cannot touch one another

The same complete physical theorem, Sections 2--6, puts the center
of every physical boundary neighbor of H into exactly one of

    C_SE=(9/8,91/60) times (-11/15,3/20),
    C_NW=(-11/15,3/20) times (9/8,91/60).

Its full feature proof includes arbitrary separating normals, both
owners, actual side means, all side endpoints and physical circle
corners whose original weights may be zero. It gives

    |c_E|^2>183/100

for each such actual boundary unit. Each displayed rectangle has
squared diameter

    2689/2880=1-191/2880<1.

Distinct actual unit centers have distance at least one. Thus two
distinct boundary neighbors must occupy different rectangles.

For a center (x,y) in C_SE, in fact

    x-y>1.                                           (1)

If x-y<=1, then x>9/8 implies y>1/8>0, while y<3/20 gives
x<=1+y<23/20. Hence

    x^2+y^2<(23/20)^2+(3/20)^2
             =269/200<183/100,

with exact positive difference 97/200, contradicting the actual
boundary-center lower bound. This proves (1). Interchanging the
coordinates shows y-x>1 for every center in C_NW.

If C is in C_SE and D is in C_NW, it follows that

    (C-D).(1,-1)>2,
    |C-D|>sqrt(2).

Physical contact of two unit squares gives center distance at most
sqrt(2), since a common point is within 1/sqrt(2) of either center.
Therefore **two distinct physical boundary neighbors of H cannot
physically touch each other.**

This strengthens the count of at most two boundary neighbors. It
does not assert that H has at most one boundary neighbor: a pair
in the two different rectangles is retained, with its mandatory
strict noncontact proved above.

## 3. A two-edge resultant with one normal in the small-corner cone

Let N_1,N_2 be the actual outward own axes at P. Suppose two original
positive H forces are mu*f and nu*g, with mu,nu>0 and actual unit
normals f,g. Suppose

    f.N_1>=0, f.N_2>=0.

Equivalently, f belongs to the actual normal cone of H at P. Write
M=mu*f+nu*g for these two unchanged forces only; all other H forces
may remain arbitrary.

Then the two strict inequalities

    M.N_1<0, M.N_2<0                                (2)

are impossible. Indeed (2) would force g.N_i<0 for i=1,2. Thus g
strictly exposes the actual opposite corner W, contrary to Section 1.

No equation at H was used. In particular H was not assigned degree
two, and neither force was identified with their sum. This statement
requires both signs in (2) to be strict; no extra assertion is made
about a resultant on one of the boundary rays of the inward quadrant.

## 4. Obtaining the cone premise from an unchanged small contact

Suppose O belongs to int H, 0<epsilon<1/60, and an unchanged positive
H contact has application p and actual normal f, with

    0<h_H(f)=p.f<=epsilon.

If f is an actual own axis of H, it must be N_1 or N_2: each of the
opposite axes has support height at least 39/40>epsilon. Therefore
the cone premise of Section 3 holds without a bound on this side's
original application or mean.

Otherwise f strictly exposes an H vertex, necessarily p. If in
addition |p|<3/8, then p=P. Every other actual H vertex has norm
at least 1-|P|>39/40, since distinct vertices are at distance at
least one. Thus again f belongs to the P normal cone, now strictly.

This proof includes an endpoint-valued application on an owned side:
it belongs to the first case. It never replaces the actual normal by
an incident face normal. The own axes are used only to describe its
unchanged cone and support heights.

## 5. Exact scope and dependency

The only external mathematical source is
ROOTED_SMALL_ORIGIN_CORNER_TWO_BOUNDARY_NEIGHBORS.md at the exact pin
in Section 1. Its physical full-feature bounds supply the rectangles
and boundary-center bound in Section 2. The new noncontact extension
and the two-force statements are proved completely above.

The source exists byte-for-byte at the publication boundary
3ab01d0c60aca0125e7700f7c8575be81828a09b. No older missing signed-vertex
theorem, genuine terminal block, true two-force private star or
unstated positive concurrence is an input here.

No numerical pose, force replacement, Lean run, CI operation, remote
action or original-cell closure is asserted by this geometric file.
