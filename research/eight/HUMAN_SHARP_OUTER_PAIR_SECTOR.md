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


## 3. The transverse bound for nonnegative relative angles

Differentiate `B` from (3) with respect to `phi`:
`B_phi=-lambda*cos(phi+alpha)<0`, since
`|phi+alpha|<=3*pi/8<pi/2`.
Reflection `(phi,alpha)->(-phi,-alpha)` changes the sign of B.
It suffices to bound `-B` when `phi=t`.

First suppose `alpha>=0`. From `r>=1`,

    -B <= lambda*sin(t+alpha)-sin(alpha)
        =u*cos(alpha)+v*sin(alpha),
    u=lambda*sin(t),  v=lambda*cos(t)-1.                (10)

We have `0<v<3/20`: indeed `lambda>10/9`,
`cos(t)>9/10`, and `lambda<23/20`.
Also `0<u<23/50`, since `sin(t)<2/5`.
These elementary bounds follow by squaring the half-angle formulas;
for example `sqrt(2)>7/5` gives
`sin(t)^2=(2-sqrt(2))/4<3/20<4/25`.
Cauchy--Schwarz therefore gives

    -B <=sqrt(u^2+v^2)
         <sqrt((23/50)^2+(3/20)^2)
         =sqrt(2341/10000)<1/2.                        (11)

So neither boundary equality nor a violation is possible here.

## 4. The negative relative angles: strict one-variable concavity

Now let `alpha=-beta<=0`. The position restriction `r<=m(beta)`
reduces the remaining check to

    -B<=G(beta):=lambda*sin(t-beta)+m(beta)*sin(beta).
                                                               (12)

We prove `G(beta)<=1/2` on the **complete** interval
`0<=beta<=pi/4`, with equality only at `beta=t`.

Put `L=cos(beta)+sin(beta)`, `L'=cos(beta)-sin(beta)`
and `D=2m+L`. Twice differentiating the defining equation
`m^2+mL=Q`, or substituting `m'=-mL'/D`, gives the identity

    m''/m = L/D + 2*(m+L)*(L')^2/D^3.                 (13)

The bounds in (2), `L>=1`, and `0<=L'<=1` imply

    (2m-L)*D^2
      > 1*(7/2)^2=49/4
      > 12 > 4*(m+L)*(L')^2.

By rearranging (13), this is exactly `m''<m/2`.
Also `m'<=0`. Therefore

    G''=-lambda*sin(t-beta)+(m''-m)*sin(beta)
                            +2m'*cos(beta)
       < -lambda*sin(t-beta)-(m/2)*sin(beta).          (14)

For `0<=beta<=t` the right side is negative.

For `t<=beta<=pi/4`, use
`sin(beta-t)/sin(beta)=cos(t)-cot(beta)*sin(t)
 <=cos(t)-sin(t)` and `m/2>5/8`.
Moreover

    lambda*(cos(t)-sin(t))<5/8.                        (15)

Here is a rational proof of (15). Since `sqrt(2)<99/70`,
we have

    (cos(t)-sin(t))^2=1-1/sqrt(2)
      <29/99<(13/24)^2.

Using `lambda<23/20` yields the strict bound
`lambda*(cos(t)-sin(t))<(23/20)*(13/24)
=299/480<5/8`. Hence (14) is negative also for
`beta>=t`: `G` is strictly concave throughout the interval.

At `beta=t`, the equation `m^2+mL=Q` gives
`m(t)=L(t)=cos(t)+sin(t)`, because
`2L(t)^2=2+sqrt(2)=Q`. Thus

    m'(t)=-(cos(t)-sin(t))/3,
    G'(t)=-lambda+m'(t)*sin(t)+m(t)*cos(t)=0.

The last equality is the exact identity

    lambda=[3*cos(t)^2+2*sin(t)*cos(t)+sin(t)^2]/3
           =(2+sqrt(2))/3.

Also `G(t)=m(t)*sin(t)=1/2`.
Strict concavity now proves `G(beta)<=1/2`, with
equality only at `beta=t`.

Together with (4), (9), and (11), this establishes
`|A|,|B|<=1/2` at every allowed square: the claimed
fixed common point w belongs to every square.

## 5. Equality cases and the sharp pair consequence

All A inequalities and the alpha>=0 transverse inequality are strict.
Equality in the remaining transverse inequality requires all of:

    phi=t, alpha=-t, beta=t, r=m(t)=cos(t)+sin(t).

Reflecting gives the only other boundary configuration
`phi=-t, alpha=t, r=m(t)`. Both have global frame angle
`phi+alpha=0`, and their centers are, respectively,

    ((1+sqrt(2))/2, 1/2), ((1+sqrt(2))/2,-1/2).

The fixed point `w` is on their common horizontal side.
The two squares touch along that side and their farthest vertices
have squared norm exactly `q0`.

Now take any two packed squares with center norms at least one and
smaller center angle `delta<=pi/4`. Rotate coordinates to the
bisector of their center rays. The theorem puts `w` in both closed
squares. If one contains w openly, it must overlap the other's open
interior, since an open neighborhood inside the former meets the
interior of the latter. Thus, for disjoint interiors, both must be
boundary equality cases, so `delta=pi/4` and the touching pair is
the displayed one up to rotation.

At any squared radius **strictly below** `q0` these equality cases
are excluded by their circle-contact vertices, so the center angular
separation is strictly greater than `pi/4`. The equality construction
proves the threshold `q0=5/2+sqrt(2)` is sharp.

This is not the missing n=8 theorem. The five-corner candidate has
squared radius slightly **above** this two-square threshold. A sharp
eight-square argument must use the other squares and their contacts;
a uniform `pi/4` pair gap cannot simply be inserted at the candidate.
