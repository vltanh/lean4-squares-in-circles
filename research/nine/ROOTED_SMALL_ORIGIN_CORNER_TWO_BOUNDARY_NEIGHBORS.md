# A small origin corner permits at most two physical boundary neighbors

Date: October 27, 2026.

**Status: complete proposed geometric theorem, frozen for full independent
review.** This is a fresh proof after the executor rollback. It does not
claim the mathematical pin of the lost signed-small-vertex source.
No original ledger or load gate is changed.

## 1. Statement and force-free scope

Let actual unit squares have pairwise disjoint interiors and lie in the
closed circle centered at O with

    sqrt(17)/2 <= R <= sqrt(Q), Q=1105/256.

Choose actual own axes of one square H so that

    H=[-a,1-a] times [-b,1-b],
    0<=a,b<=1/40.                                      (1)

Then **at most two distinct physical boundary squares can touch H**.

A physical boundary square is one with an actual circle corner. No
circle multiplier, pair multiplier, degree, or equilibrium hypothesis
is imposed on any of the squares in this theorem. Both a=0 and b=0,
all shared-side means, and point-only contacts are included.

The proof puts every possible neighbor center into one of two explicit
rectangles, each of diameter strictly less than one:

    C_SE=(9/8,91/60) times (-11/15,3/20),
    C_NW=(-11/15,3/20) times (9/8,91/60).               (2)

The assertion is about physical neighbors, including any unstressed
contacts. Arbitrarily many other actual squares remain.

## 2. Uniform center and contact estimates

Write C for an arbitrary contained unit center. In its own orthonormal
axes, the maximum squared corner radius is

    |C|^2+1/2+|C_1|+|C_2|
       >= |C|^2+|C|+1/2.

Consequently

    |C|<M=91/60,                                      (3)

since M^2+M+1/2-Q=31/57600>0.

If that square is physical boundary, a true circle corner is at
distance 1/sqrt(2) from C. Hence

    |C| >= R-1/sqrt(2),
    |C|^2 >=19/4-sqrt(17/2)>183/100.                   (4)

For the strict last comparison, sqrt(17/2)<73/25 and
(73/25)^2-17/2=33/1250.

Any point p of a physical boundary unit satisfies |p|>=R-sqrt(2),
by the square's actual diameter. Also every point p of an arbitrary
unit satisfies

    |C-p|<=1/sqrt(2)<17/24.                            (5)

Distinct actual unit centers have distance at least one: their open
inscribed disks of radius 1/2 are disjoint.

We shall use another elementary square fact. If p is an actual
minimum-support point of a unit for an inward unit normal n, then

    p+n belongs to that same actual unit.              (6)

For a side point this is the point one width across the square. At a
vertex write n in the two orthogonal inward edge directions. Both
coefficients lie in [0,1], so (6) follows, including either zero
coefficient.

## 3. A complete wall estimate at height 39/40

Suppose an arbitrary contained unit E lies in x>=39/40. We prove

    |C_E,y|<3/20.                                     (7)

Choose its frame parameter c>=s>=0, c^2+s^2=1. Its x width is c+s.
The maximum x-coordinate is at most R, and

    c+s<=R-39/40
       <133/64-39/40=353/320.

Here (133/64)^2-Q=9/4096>0. On s in [0,1/sqrt(2)] the function
sqrt(1-s^2)+s is increasing. If s>=1/9, it is at least
(4sqrt(5)+1)/9, which exceeds 149/135 because sqrt(5)>67/30.
But

    149/135-353/320=1/1728>0.

Thus s<1/9 and c>=1-s^2.

Suppose C_E,y>=3/20. For the two possible signs of the square's tilt,
there is respectively an actual upper far corner Z with

    Z_x>=39/40+c,       Z_y=C_E,y+(c+s)/2,

or

    Z_x>=39/40+c+s,     Z_y=C_E,y+(c-s)/2.

In the first case the positive coordinates satisfy

    Z_x>=79/40-s/9,
    Z_y>=13/20+4s/9.

In the second they satisfy

    Z_x>=79/40+8s/9,
    Z_y>=13/20-5s/9>0.

The respective squared lower bounds are

    6917/1600+(5/36)s+(17/81)s^2,

and

    6917/1600+(251/90)s+(89/81)s^2.

Both already exceed Q at s=0 because

    6917/1600-Q=43/6400>0.

This contradicts containment. Reflection in the x-axis handles
C_E,y<=-3/20. This proves (7), including both frame endpoints and
without any physical boundary hypothesis.

## 4. Strict southeast contacts

Take any separating line at a physical H-E contact whose normal
from H into E is

    n=(c,-s), c,s>0, c^2+s^2=1.

Its actual H point is

    P=(A,-b), A=1-a in [39/40,1].                     (8)

Thus P belongs to E. From (3)--(5),

    C_x >
      [133/100+A^2+b^2-2bM]/(2A).                    (9)

Indeed expansion of |C-P|^2<=1/2 gives
2A C_x>=|C|^2+A^2+b^2-1/2+2bC_y, and C_y>-M.

Put K_b=133/100+b^2-2bM. It is larger than one throughout
0<=b<=1/40. Thus (A^2+K_b)/(2A) decreases with A on [39/40,1].
At A=1 it decreases with b. Evaluating at b=1/40 gives

    C_x>10823/9600=9/8+23/9600>9/8.                  (10)

Also (5) gives

    C_y>=-b-1/sqrt(2)>-11/15.                        (11)

It remains to prove C_y<3/20. We retain all actual E features.

### 4.1. P is an E vertex

The open tangent quadrant of H at P points northwest. The open
right-angle tangent sector of E cannot intersect it. The two
orthogonal inward E edges therefore either both have nonnegative
x-coordinate, or both have nonpositive y-coordinate. This is the
complete interval cover for a right-angle sector disjoint from the
open northwest quadrant; edge-on-axis cases belong to the same cover.

In the first case write the actual inward edges as

    (r,-t), (t,r), r,t>=0, r^2+t^2=1.

The far actual corner is Z=P+(r+t,r-t). Since r+t>=1 and r-t<=1,

    |Z|^2
      =A^2+b^2+2+2A(r+t)-2b(r-t)
      >=(39/40)^2+2+2(39/40)-1/20
      =Q+3419/6400>Q.

This is impossible. In the second case the center y-coordinate is
-b minus half the sum of two nonnegative components whose squared
sum is one. In particular C_y<0. Thus C_y<3/20 in every vertex case.

### 4.2. P is in the relative interior of an E side

Now E owns the normal n. Put j=(s,c). For an actual slider
-1/2<k<1/2 its center is

    C=P+(1/2)n+k j.

Suppose C_y>=3/20. Then

    k=(C_y+b+s/2)/c>0,

and the actual corner Z=C+(n+j)/2 has

    Z_x=A+c+(k+1/2)s,
    Z_y=C_y+(c-s)/2.                                 (12)

Using c+s^2/(2c)>=1 and c<=1 gives

    Z_x>=A+1+(C_y+1/2)s
       >=79/40+(13/20)s.                             (13)

If s>=1/2, this exceeds 23/10>R. If 0<s<=1/2, use
c>=1-s^2 and s^2/2<=s/4 to obtain

    Z_y>=13/20-3s/4>0.

Equations (12)--(13) therefore give

    |Z|^2 >=
       (79/40+13s/20)^2+(13/20-3s/4)^2
       =6917/1600+(637/400)s+(197/200)s^2>Q.          (14)

This contradiction completes the side-interior case. Side endpoints
were already included in Section 4.1.

Every strict southeast contact consequently puts C in C_SE.

## 5. Both adjacent axial directions

### 5.1. East normal

If the separating normal is e_x, E lies in x>=1-a>=39/40.
Section 3 gives |C_y|<3/20. Its center x-coordinate is at least
1-a+1/2>=59/40>9/8. Together with (3), this puts it in C_SE.

This uses the entire actual shared-side segment or point, and does
not require that a chosen contact mean be in its relative interior.

### 5.2. South normal

If the normal is -e_y, E lies below H's bottom side and

    -11/15<C_y=-b-width_y(E)/2<=-1/2.

Equations (3)--(4) imply

    C_x^2>183/100-(11/15)^2
          =(9/8)^2+383/14400.

At an actual contact p=(p_x,-b), p_x>=-a, (5) gives
C_x>=p_x-1/sqrt(2)>-11/15. It therefore cannot be the negative
solution with |C_x|>9/8. Hence C_x>9/8, again placing it in C_SE.

No side alignment between H and E is assumed in this argument.

## 6. The other quadrants and the final count

Interchanging x and y in Sections 4--5 puts every northwest contact,
including north and west axes, in C_NW.

A strict southwest normal exposes S=(-a,-b). By (1),
|S|<=sqrt(2)/40, so |S|+sqrt(2)<2<=R. Section 2 shows that S cannot
belong to any physical boundary unit.

A strict northeast normal exposes W=(1-a,1-b). By (6), the actual
neighbor would contain W+n, but

    |W+n|^2
       >=2(39/40)^2+1+2(39/40)
       =Q+3423/6400>Q.

Thus all possible actual contact normals are covered by the two
rectangles in (2). Each rectangle has squared diameter

    (91/60-9/8)^2+(3/20+11/15)^2
       =2689/2880
       =1-191/2880<1.                                (15)

At most one actual center lies in each rectangle, because distinct
actual unit centers are at distance at least one. There are therefore
at most two physical boundary neighbors of H, as claimed.

## 7. Exact intended use and limitation

If an actual origin-containing H has a vertex of norm less than
1/40, take that vertex as (-a,-b) in the two inward H directions.
Then (1) holds, and the theorem applies.

In particular a genuine hub-rooted terminal diamond at such H is
impossible whenever its three true private bodies have been proved
physical boundary from their unchanged stars: it would give three
distinct boundary neighbors of H.

This theorem does not assert the same result for a small vertex of
a square avoiding O. The signed-coordinate extension is a different
statement and is not needed for the present reconstruction. Nor does
a small H corner alone exclude every terminal C4; that caller retains
its additional full root-resultant direction and private-load
hypotheses separately.

