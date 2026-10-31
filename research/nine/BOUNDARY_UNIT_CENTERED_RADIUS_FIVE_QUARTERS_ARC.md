# A uniform forty-degree centered inner arc in every physical boundary unit

Date: October 28, 2026. Author: return_scalar_assembly continuation.

**Status: complete proposed force-free hand theorem, frozen for full
root and separate independent review.** This controls every actual
physical boundary unit simultaneously, without a degree, contact-owner,
force, normal, or circle-weight premise. It also records an exact
`4/5` lower bound for the already-proved sharp extra-square arc length.
No original graph gate or certificate retirement is claimed here.

## 1. Statement

Put

    Q=1105/256,     rho=5/4,     eta=pi/9.

Let an actual closed unit square S be contained in the disk of radius R
about the unchanged origin O, where

                         2<=R<=sqrt(Q).

Assume S physically touches that circle. A touching corner may have
zero individual weight, and the square may have zero total circle load.
Let c be its actual center, and theta its center direction.

**Theorem.** The entire closed angular interval

                          [theta-eta,theta+eta]

on the radius-rho circle lies in the open interior of S. In particular
both endpoints are strictly interior points of this actual square.
The result applies independently to all orientations and all physical
one-corner or two-corner masks.

Write, as in the sharp quarter-clear arc theorem,

    D=sqrt(1105/512)-1,
    Lambda=pi/2-2*asin(D/(5/4)).

An additional exact consequence proved below is

                              Lambda>4/5.                 (1)

The centered subarc theorem does not assert any routing of additional
units into a free interval. Such routing remains a separate geometric
obligation of a caller.

## 2. Complete center and own-frame bounds

Let d=|c|. Physical circle contact and the half-diagonal bound give

    d>=R-1/sqrt(2)>=2-1/sqrt(2)>5/4.                     (2)

Choose signs and the order of S's own axes so

    c=d*(cos(psi),sin(psi)),    0<=psi<=pi/4.

Set

    u=sin(psi),    v=cos(psi),
    0<=u<=1/sqrt(2),   v=sqrt(1-u^2),
    S=[d*v-1/2,d*v+1/2] times[d*u-1/2,d*u+1/2].

The farthest actual corner gives

                    d^2+d*(u+v)+1/2<=Q.                  (3)

Since `u+v>=1`,

    d<=sqrt(Q-1/4)-1/2<91/60,
    (121/60)^2+1/4-Q=31/57600>0.                        (4)

For later use define

                       S_d=(Q-1/2-d^2)/d.

It strictly decreases for `d>0`, and (3) says `u+v<=S_d`.
These bounds retain the axis-aligned endpoint `u=0` and the diagonal
endpoint `u=v`.

## 3. Exact elementary bounds at eta=pi/9

We use

           1/3<sin(eta)<343/1000,    cos(eta)>939/1000.   (5)

Here is a direct check. Since `0<eta<pi/6`, its sine is in `(0,1/2)`
and the function `3*s-4*s^3` strictly increases there. The triple-angle
identity gives

                        3*sin(eta)-4*sin(eta)^3=sqrt(3)/2.

At `s=1/3` the left side is `23/27<6/7<sqrt(3)/2`.
At `s=343/1000` it is `867585572/1000000000`, greater than
`867/1000`, whereas `(867/1000)^2-3/4=1689/1000000>0`.
This proves the sine bounds in (5).

For cosine, `cos(eta)>1/2`, the function `4*c^3-3*c` increases
there, and its value at the actual cosine is `cos(pi/3)=1/2`.
At `c=939/1000` its value is `494744076/1000000000<1/2`.
This proves the cosine bound in (5).

## 4. Both angular endpoints lie strictly in the original square

Consider the two radius-rho points at angles `psi+eta` and `psi-eta`.
Put

    m=d-rho*cos(eta),
    n=rho*sin(eta).

Equations (2), (4), and (5) give

    0<m<823/2400,
    5/12<n<343/800,
    n>m.

The coordinate differences between these two points and c are

    (-m*v-n*u, -m*u+n*v),
    (-m*v+n*u, -m*u-n*v).

Because `v>=u>=0` and `n>m>0`, the largest absolute coordinate
difference among the four displayed coordinates is

                              m*u+n*v.                    (6)

We show it is strictly less than `1/2` over three full continuous
center-radius intervals. This is an elementary estimate on the whole
domain, not a finite enclosure program or sampled-angle argument.

### 4.1. d<=57/40

By (5), `m<201/800` and `n<343/800`. Cauchy--Schwarz gives

    m*u+n*v<sqrt((201/800)^2+(343/800)^2)<1/2,
    1/4-[(201/800)^2+(343/800)^2]=39/12800>0.             (7)

### 4.2. 57/40<=d<=59/40

Equation (3) gives

    u+v<=S_(57/40)=11429/9120<3/10+sqrt(91)/10.

For the final comparison both sides after subtracting `3/10` are
positive, and the exact squared reserve is

    91/100-(11429/9120-3/10)^2=24091/16634880>0.

The function `u+sqrt(1-u^2)` increases on `[0,1/sqrt(2)]`, so
`u<3/10`. Also `m<241/800` and `n<343/800`. The function

                  (241/800)*u+(343/800)*sqrt(1-u^2)

increases for `0<=u<=3/10`: its derivative is positive since
`sqrt(1-u^2)>=sqrt(91)/10>9/10`. Consequently

    m*u+n*v
      <(241/800)*(3/10)+(343/800)*(191/200)<1/2,           (8)

where `sqrt(91)/10<191/200`, and the last reserve is
`27/160000>0`.

### 4.3. d>=59/40

Here (3) gives

    u+v<=S_(59/40)=10501/9440<223/200
                            <1/8+sqrt(63)/8.

The first reserve is `123/47200`; the last comparison uses
`sqrt(63)/8>99/100`, whose square comparison is positive.
Monotonicity again gives `u<1/8`. By (4)--(5),

    m*u+n*v
      <(823/2400)*(1/8)+343/800
       =9055/19200<1/2.                                 (9)

Equations (7)--(9) cover the entire center-radius range including both
split endpoints. Each of the two original angular points therefore
has both coordinate differences strictly between `-1/2` and `1/2`.
It lies in `int(S)`.

Every point of the physical boundary unit S has distance at least
`R-sqrt(2)>1/4`. The complete strict-clearance arc theorem therefore
gives one connected open radius-rho arc in `int(S)`, containing its
radial center point. The two endpoint points just proved to be interior
belong to this same arc. All angles here lie in S's own strict positive
first-axis half-plane, since `d*v-1/2>0`; there is no wraparound
ambiguity. The entire closed interval between the two points is thus
in `int(S)`. This proves the centered subarc theorem.

## 5. An exact rational lower bound for the sharp extra arc

For `D=sqrt(1105/512)-1`,

    sqrt(1105/512)<191/130,
    (191/130)^2-1105/512=943/2163200>0,
    D/(5/4)<122/325.                                    (10)

The standard global lower tangent estimate for sine on `[0,1]` gives

    sin(77/200)>=77/200-(77/200)^3/6>122/325,
    77/200-(77/200)^3/6-122/325=65071/624000000>0.         (11)

For completeness the rational pi bounds used here and by the later
capacity comparison are `157/50<pi<22/7`. The upper bound follows
directly from

             integral_0^1 x^4*(1-x)^4/(1+x^2) dx=22/7-pi>0.

For the lower bound use Machin's exact identity
`pi=16*atan(1/5)-4*atan(1/239)`, the lower bound
`atan(1/5)>1/5-1/(3*5^3)`, and `atan(1/239)<1/239`.
They give

    pi>16*(1/5-1/375)-4/239>157/50,
    16*(1/5-1/375)-4/239-157/50=107/179250>0.

Machin's identity follows by the tangent addition formula with all
angles in their indicated first-quadrant ranges. The sine estimate
in (11) follows, for example, by integrating `cos(t)>=1-t^2/2`.

Now `77/200<pi/4-2/5`, and all these angles lie in `(0,pi/2)`.
Equations (10)--(11) imply

    asin(D/(5/4))<77/200<pi/4-2/5,
    Lambda=pi/2-2*asin(D/(5/4))>4/5.

This proves (1) with fully printed exact reserves.

## 6. Operative input and scope

The sole non-elementary operative input is the already-proved complete
actual-square arc theorem:

| Source | SHA-256 | Use |
| --- | --- | --- |
| `SHARP_QUARTER_CLEAR_RADIUS_FIVE_QUARTERS_ARC_AND_INTERVAL_CAPACITY.md` | `bca528af5320cc8314839eb0d53cf6f15ec381ac42d5bd353f62a27a47101f67` | Connected whole actual arc under strict quarter clearance, and the exact definition and lower bound by Lambda for each additional unit |

The main centered-subarc endpoint inequalities are otherwise proved
above directly from the square's farthest physical corner. All actual
corners remain physical irrespective of weights. This source changes
no graph, mean, normal, load, force equation, or degree, and supplies no
completion allocation. Exact rational arithmetic was used only to check
the printed elementary reserves. No numerical grid, certificate replay,
Lean/Lake invocation, CI, workflow, commit, or remote mutation is part
of this proof.
