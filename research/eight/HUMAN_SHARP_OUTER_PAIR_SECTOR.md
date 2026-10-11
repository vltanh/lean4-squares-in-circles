# A sharp angular-sector common-point theorem for two outer squares

## Theorem and equality

Put `q0=5/2+sqrt(2)`, `t=pi/8`,
`lambda=(2+sqrt(2))/3`, and `w=(lambda,0)`.
Every unit square contained in the closed disk `D_sqrt(q0)`
whose center has norm at least one and argument in `[-t,t]`
contains the **same point** `w`.

The only such squares with `w` on their boundary are the two
axis-parallel squares centered at

    ((1+sqrt(2))/2, 1/2),   ((1+sqrt(2))/2, -1/2).

Consequently two disjoint-interior unit squares with center norms
at least one in `D_sqrt(q0)` have center angular separation at
least `pi/4`. Equality in angular separation is possible only
for the displayed parallel touching pair, up to rotation.

This is a sharp **two-square conditional theorem**; `q0` is slightly
smaller than the proposed optimal eight-square squared radius. It
does not prove the unrestricted eight-square lower bound.

## 1. Center variables and the exact disk constraint

Choose a quarter-turn of the square's frame so that its center is

    p=r*(cos(phi),sin(phi)),  r>=1,  -t<=phi<=t,

and the frame directions are

    e=(cos(phi+alpha),sin(phi+alpha)),   f=Je,
    -pi/4<=alpha<=pi/4.

Put `beta=|alpha|`, `c=cos(beta)`, `s=sin(beta)`,
`L=c+s`, and `Q=q0-1/2=2+sqrt(2)`.
The exact farthest-vertex formula says

    r^2+r*L <= Q.                                       (1)

Let `m(beta)>0` be the unique root of `m^2+m*L=Q`.
Then `1<=r<=m(beta)`. Since `L` increases on
`[0,pi/4]`, `m` decreases; `m(0)=sqrt(2)`.
At `beta=pi/4`, `m>5/4`, because

    Q-[25/16+(5/4)*sqrt(2)]
      =7/16-sqrt(2)/4>0.

Thus throughout the interval

    5/4<m<=sqrt(2)<3/2,   1<=L<3/2.                    (2)

Write the coordinates of `w-p` in the square frame:

    A=lambda*cos(phi+alpha)-r*cos(alpha),
    B=-lambda*sin(phi+alpha)+r*sin(alpha).              (3)

We must show `|A|,|B|<=1/2` and determine all equalities.

## 2. The two longitudinal bounds

Since `r>=1` and `cos(alpha)>=1/sqrt(2)`,

    A<=lambda-1/sqrt(2)
      =(4-sqrt(2))/6<1/2.                              (4)

For the other sign, use `r<=m(beta)` and
`cos(phi+alpha)>=cos(t+beta)` to obtain

    -A<=H(beta):=m(beta)*cos(beta)
                          -lambda*cos(t+beta).          (5)

Here and below all trigonometric angles in the cosine comparison have
absolute value below `pi/2`.

The derivative of `m^2+m*L=Q` is

    m'=-m*(cos(beta)-sin(beta))/(2*m+L).                (6)

Define `b=m/(2m+L)`. From (2) and `L>=1`,

    b<=sqrt(2)/(2*sqrt(2)+1)<37/100,

where the last comparison is `26*sqrt(2)<37`.
The following two rational bounds will be used:

    lambda*sin(t)>43/100,
    m-lambda*cos(t)<37/100.                             (7)

For verification, `141/100<sqrt(2)<283/200`.
Thus `lambda>341/300`,
`sin(t)>19/50` (square the formula
`sin(t)^2=(2-sqrt(2))/4`), and
`cos(t)>923/1000` (square
`cos(t)^2=(2+sqrt(2))/4`).
The first product is `6479/15000>43/100`;
for the second,
`sqrt(2)-lambda*cos(t)
 <283/200-(341/300)*(923/1000)
 =109757/300000<37/100`.
Every displayed comparison is between positive rationals after the
given square tests.

Differentiating H and applying (6)--(7), with `c=cos(beta)`,
`s=sin(beta)`, gives

    H'=(lambda*sin(t)-b*(c-s))*c
                        -(m-lambda*cos(t))*s
      > [43*c-37*c*(c-s)-37*s]/100
      = [6*c+37*(c-s)*(1-c)]/100 >0.                  (8)

Finally `m(pi/4)<13/10`, since
`(13/10)^2+(13/10)*sqrt(2)>Q`;
also `1/sqrt(2)<5/7` and `cos(3*pi/8)=sin(t)`.
Therefore

    H(beta)<=H(pi/4)
      <(13/10)*(5/7)-43/100
      =349/700<1/2.                                   (9)

Both bounds on A are strict. Sections 3--4 treat B and all equality
conditions, without assuming that any square orientations agree.
