# A corner-only exterior square cannot wrap both positive rays from a centered corner

## Theorem (exact geometric obstruction, no numerical sampling)

Let C be an axis-parallel unit square containing zero in
its open interior, with center (a,b), and put

    A=a+1/2>0,      B=b+1/2>0.

Let S be another unit square with disjoint open interior,
whose pair C,S has **no separator on either central axis**
and whose unique outward, own-square separating normal
points into the *northeast* quadrant. Thus, for some
c,s>0 with c^2+s^2=1, the own side normal is n=(c,s)
and S is separated northeast from C.

If the open interior of S intersects **both**
positive origin coordinate rays

    {(x,0):x>0} and {(0,y):y>0},                       (1)

then necessarily

    **sqrt(A)+sqrt(B) < sqrt(2).**                   (2)

In particular, if a>=0 and b>=0, **no** such
northeast corner-only square can cross both
positive rays through its open interior.
The same statement holds for each other
central corner after reflecting the signed
coordinate axes: replace A,B by the two
positive distances of its outward central
side lines from the disk origin.

The result depends only on the unit-square
diameter and genuine own-axis support separation.
It does not require disk containment, contact,
a chosen physical stress, or a candidate layout.
It is a **continuous subcase rejection**, not
an exclusion of every corner-only NE status.

## Hand proof

The northeast vertex of C is v=(A,B).
Because n=(c,s) is the own **side normal**
of S pointing outward from C, the
separating-axis inequality says

    inf_(z in S) n dot z >= n dot v =c*A+s*B.        (3)

This follows as well by writing the
full square supports:
n dot(p_S-p_C)>=h_C(n)+h_S(n),
where h_C(n)=(c+s)/2 and h_S(n)=1/2.

Choose interior points of S on both rays (1),

    P=(x,0),      Q=(0,y),       x,y>0.

Applying (3) to P and Q yields

    x>=A+(s/c)*B,
    y>=B+(c/s)*A.                                   (4)

For t=s/c>0, add the two inequalities:

    x+y>=A+B+t*B+A/t
        >=A+B+2*sqrt(A*B)
        =(sqrt(A)+sqrt(B))^2.                        (5)

The middle inequality is ordinary AM-GM
and remains valid when the separator is
not tangent but has positive slack.

But P and Q are two points of the **open
interior** of a unit square. Their mutual
distance is strictly less than its
diagonal diameter sqrt(2): only
opposite vertices of the closed square
can be sqrt(2) apart. Here

    |P-Q|^2=x^2+y^2,

and Cauchy--Schwarz gives

    x+y<=sqrt(2)*sqrt(x^2+y^2)<2.                  (6)

Equations (5)--(6) imply
(sqrt(A)+sqrt(B))^2<2, proving (2).

If a,b>=0 then A,B>=1/2, and
sqrt(A)+sqrt(B)>=2*sqrt(1/2)=sqrt(2),
contradicting (2). Reflection proves
the variants for the other three
corner-owned statuses. QED.

## What this prunes and what it does not

For a centered central square C, all four
corner-only statuses NE,NW,SE,SW can occur
as pairwise geometric types, but **none**
can be simultaneously an open-interior
crosser of the two origin rays bordering
its assigned corner. Therefore a global
angle/ray routing must use other squares
to cover at least one of those rays
whenever the central center is centered.

More generally the exact curved boundary
sqrt(h_x)+sqrt(h_y)=sqrt(2)
gives a necessary central-center offset
for any proposed double-ray-wrapping
corner-only square, where h_x,h_y are
the positive central side offsets
toward that corner. One may use a
weaker rational exclusion region by
bounding those square roots, but no
such approximation is needed in the
theorem.

The result does **not** say a corner-only
square lies wholly in its corner quadrant;
it may cross one cardinal ray or neither.
It does not count a square center as a
whole-quadrant square, and it must not
be used to exclude the valid candidate's
single-side or double-side contact
members. The full sharp lower bound
R8>=Rhat remains unproved.
