# Four-square cap exclusion at the sharp eight-square search ceiling

## Theorem (all orientations, no contact assumptions)

Let four unit squares with pairwise disjoint open interiors lie in a
disk centered at the origin of radius

    R <= 99/50.

Suppose that for a unit vector n they all lie wholly beyond the
straight line

    n dot x = h,            h >= 1/100.

This is **impossible**.

The theorem holds for completely independent square orientations,
with no assumptions about which squares touch, and needs only one
horizontal chord-length calculation. It therefore applies throughout
the exact eight-square search ceiling

    R_8 <= sqrt(9789)/50 < 99/50.

In particular, if an open central square C has a side whose
supporting line has signed distance h>=1/100 from the disk center,
then at most **three other squares** may admit their whole-square
separation on that side. Any hypothetical population of four beyond
one central side must have h<1/100, i.e. its side must pass extremely
close to the disk center.

A *whole-square* cap membership is necessary. Four center locations
in a half-plane, without the corresponding entire-square
containments, do **not** meet this theorem's hypothesis.

## 1. Reduce to one fixed vertical slice

Rotate so n=(1,0). Since h>=1/100, it is enough to exclude
four squares in the **larger**, fixed cap

    D_rho intersect {x>=h0},
    rho=99/50,       h0=1/100.

Choose the common vertical slice at the exact rational abscissa

    X=(rho+h0)/2=199/200.

Consider one unit square S contained in this cap.
By reflection and quarter-turn symmetry its unsigned frame tilt
may be written as 0<=theta<=pi/4. Put

    c=cos(theta), s=sin(theta),
    L=c+s, D=c-s.

Its complete horizontal width is L, and

    1<=L<=sqrt(2),    c*s=(L^2-1)/2.              (1)

Let l and r be the leftmost and rightmost x coordinates of S.
The cap and disk constraints give

    h0<=l,       r<=rho,       r-l=L.

Therefore

    X-l >= L-(rho-h0)/2 = L-197/200,
    r-X >= L-197/200.                               (2)

Both are strictly positive because L>=1.
Thus x=X passes through the **open interior**
of each square, and its intersection with
that square is a vertical chord of positive length.

## 2. Every vertical chord has length greater than 6/7

For theta=0 the chord has length exactly one.
Suppose theta>0. Let delta denote the
horizontal difference between the square's
center and X. Elementary intersection of the
line x=X with the four sides of the square
gives the **exact chord formula**

    length(S intersection {x=X})
      = 1/c                         if |delta|<=D/2,
      = (L/2-|delta|)/(c*s)          otherwise.    (3)

In the plateau branch 1/c>=1>6/7.
In the other branch, (2) implies

    L/2-|delta|
       =min(X-l,r-X) >= L-197/200.

So it suffices to check

    L-197/200 >(6/7)*c*s
               =(3/7)*(L^2-1)                     (4)

for 1<=L<=sqrt(2). Define

    F(L)=L-197/200-(3/7)*(L^2-1).

This quadratic is **strictly concave**, so its
minimum on the interval occurs at an endpoint.
At L=1 its value is

    F(1)=3/200>0.

At L=sqrt(2),

    F(sqrt(2))=sqrt(2)-1979/1400>0,

because the last inequality is exactly the
positive integer square comparison

    2*1400^2 - 1979^2
       =3920000-3916441=3559>0.

Consequently (4) holds over the entire
orientation range. In either branch of
(3), the chord has length **strictly
greater than 6/7**. No angle samples
or numerical lower-bound certificates
are involved.

## 3. Four disjoint chords do not fit in the disk slice

The four squares have disjoint open interiors,
and x=X cuts the **open** interior of
each square. Thus the interiors of their
four vertical chord intervals are disjoint.
Their combined length is strictly greater than

    4*(6/7)=24/7.                                    (5)

However all those intervals lie on the one
vertical chord of D_rho at x=X, of length

    2*sqrt(rho^2-X^2)
       =sqrt(117215)/100.                           (6)

The exact computation is

    rho^2-X^2
      =(99/50)^2-(199/200)^2
      =117215/40000.

The strict comparison between (5) and (6)
is equivalent, after squaring the positive
quantities, to the single integer inequality

    576*10000=5760000
       >117215*49=5743535.

Thus the disk slice is **shorter** than
24/7, contradicting the four chord lengths.
No four such packed squares can exist. QED.

## 4. Explicit impact on central-side occupancy patterns

Let C contain the disk center in its open interior.
For any one of its signed side normals n, write

    h_C(n)=n dot p_C+1/2,       0<h_C(n)<1.

If four *distinct* other squares are separated
from C along the outward central-owned n axis,
they all lie wholly in {x:n dot x>=h_C(n)}.
The theorem shows that at squared radius
q<=9789/2500 this is impossible whenever

    h_C(n)>=1/100.

Consequently a central-side population of four
could occur **only** if

    0<h_C(n)<1/100,
    n dot p_C<-49/100.                                (7)

This excludes a large, continuous family of
occupancy arrangements and is stronger than
simply limiting an outward side to a triple.
The exceptional narrow strip (7) is
**not** excluded by the slice argument,
and no conclusion about *corner-owned*
separators or squares whose centers merely
lie beyond the line is inferred.

The already proved opposite 3+2 cap
theorem excludes a triple on one central
side and a pair on its opposite side
throughout q<2257/576. Thus the surviving
central-side populations at the sharp
search ceiling obey **both** restrictions:

* a four-square side must be within 1/100
  of the disk center; and
* a three-square side cannot have two
  distinct squares on its opposite side.

Neither restriction alone forces the
candidate seven-edge separator graph.
The unrestricted n=8 sharp bound
R_8>=R_hat remains OPEN.
