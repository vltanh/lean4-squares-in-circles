# A unit near the center has a wider centered nine-eighths arc

Date: October 27, 2026.

**Status: complete force-free hand theorem, independently ACCEPTED**
in REVIEW_NEAR_CENTER_NINE_EIGHTHS_ARC_ROOTED_BLOCKS_2026_10_27.md.
Root review remains separate. Every coordinate and center is that
of the original physical square. No circle-contact, load, stress,
neighbor or selected-normal premise is used.

## 1. Exact statement and the complete actual coordinate cover

Let E be any actual closed unit square satisfying

    dist(O,E)>=1/5,       |c_E|<=5/6.

Put

    rho=9/8,       alpha=atan(2/5).

Then the entire closed circle arc

    {rho e_theta : |theta-arg(c_E)|<=alpha}

lies in the open interior of E. The strict interior conclusion
includes both arc endpoints and every actual square orientation.

Choose only the signs and order of E's actual own axes so its
center has coordinates

    (a,b),       a>=b>=0,
    E=[a-1/2,a+1/2] times [b-1/2,b+1/2].

If b>=1/2, put A=a-1/2 and B=b-1/2. Then

    A,B>=0,       A^2+B^2>=1/25,
    |c_E|^2=1/2+A+B+A^2+B^2
       >=1/2+1/5+1/25=37/50>25/36,

a contradiction. Hence b<1/2. The exact nearest-point formula
now gives

    a>=7/10,
    7/10<=r:=|c_E|<=5/6,
    a=r cos(phi), b=r sin(phi),       0<=phi<=pi/4.     (1)

This covers the nearest-side, nearest-vertex and weak-clearance
possibilities; the vertex branch was excluded by the radius bound,
not silently discarded.

The exact trigonometric values are

    cos(alpha)=5/sqrt(29),       sin(alpha)=2/sqrt(29),
    0<alpha<pi/4,
    rho cos(alpha)>5/6.                                  (2)

For the final inequality, 54>8sqrt(29), whose squared reserve
is 1060.

## 2. The first own-coordinate deviation is strictly below one half

For any -alpha<=t<=alpha, the actual circle point in center
direction plus t has coordinates

    (rho cos(phi+t), rho sin(phi+t)).

Its positive first-coordinate deviation is at most

    rho-a<=9/8-7/10=17/40<1/2.                         (3)

On the other side, |phi+t|<=pi/4+alpha<pi/2, so

    rho cos(phi+t)
       >=rho cos(pi/4+alpha)
        =27/(8sqrt(58))>27/64,

using sqrt(58)<8. Since a<=5/6, its negative first-coordinate
deviation is strictly below

    5/6-27/64=79/192<1/2.                               (4)

Thus the full first-coordinate interval, not merely its two
endpoints, lies strictly inside E.

## 3. One global concavity bound handles the second coordinate

The sine is increasing on the entire interval
[-alpha,pi/4+alpha], which lies in (-pi/2,pi/2).
The positive second-coordinate deviation is therefore at most

    rho sin(phi+alpha)-r sin(phi)
       <=F(phi):=rho sin(phi+alpha)-(7/10)tan(phi),       (5)

because a=r cos(phi)>=7/10.

For 0<=phi<=pi/4,

    F''(phi)
      =-rho sin(phi+alpha)
         -(7/5)sec^2(phi)tan(phi)
      <=-rho sin(alpha)<-2/5.                           (6)

The last inequality is 9/(4sqrt(29))>2/5, with squared
reserve 45^2-8^2*29=169>0.

At the interior comparison angle phi=alpha,

    F(alpha)=719/1450,
    F'(alpha)=77/29000.

These follow directly from sin(2alpha)=20/29,
cos(2alpha)=21/29 and sec^2(alpha)=29/25.
The global Taylor bound supplied by (6), followed by one completed
square, gives

    F(phi)<=F(alpha)+F'(alpha)(phi-alpha)
                         -(1/5)(phi-alpha)^2
      <=719/1450+(5/4)(77/29000)^2
       =333621929/672800000
       =1/2-2778071/672800000<1/2.                     (7)

This is a uniform whole-angle inequality; no sample or local
angle restriction is used.

The most negative second-coordinate deviation occurs at t=-alpha.
Using (2),

    b-rho sin(phi-alpha)
      =(r-rho cos(alpha))sin(phi)
          +rho sin(alpha)cos(phi)
      <=rho sin(alpha)=9/(4sqrt(29))<9/20<1/2.          (8)

Equations (5)--(8) include phi=0, phi=pi/4 and the actual
clearance and center-radius endpoints.

## 4. Conclusion and precise export

Both own-coordinate deviations of every point in the stated
closed arc are strictly between -1/2 and 1/2. This proves the
whole arc belongs to int(E).

The actual center is nonzero by (1). Its exact direction is the
center of the arc; no artificial radial direction is used.
The halfwidth alpha is strictly greater than pi/9, since

    tan(pi/9)<sqrt(31)/15<2/5,

using the accepted elementary cos(pi/9)>15/16 bound and
31<36. Thus this actual centered arc is wider than forty
degrees in total.

The theorem itself does not assert that E's entire circle
intersection is connected. A caller needing that property must
also use the full connected-arc theorem at
dist(O,E)>=1/5>1/8. Nor does this source claim a path order,
a circle load, an original graph-family closure or a change in
any contact. It supplies only the explicit complete centered
arc at the literal physical scope stated above.

No pose, original unit, actual mean, selected normal, force,
shared metadata, remote state, compilation or CI is changed.

