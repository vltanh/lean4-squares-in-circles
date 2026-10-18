# A sevenfold-symmetric contact ring cannot fit inside radius two

## Statement and scope

**Theorem.** Let seven pairwise interior-disjoint unit squares be the
successive images of one unit square under rotations about the disk
origin through multiples of `2*pi/7`. The enclosing disk centered
at that origin has radius **strictly greater than 2**.

There is no assumption that the squares touch, nor any numerical
optimization. The proof considers every orientation of the original
square and uses the separating-axis theorem and rational elementary
trigonometric bounds. This excludes a highly symmetric seven-outer
ring, **not** every seven-outer contact cycle; irregular cycles and
outer paths with inner attachments remain open in the n=8 proof.

## 1. Exact two-square separator for a symmetric ring

Put `x=pi/7` and `theta=2*x`, so `0<x<pi/4`.
The first center can be written `p=(r,0)`, r>0, and the next is
`q=r*(cos(theta),sin(theta))`.
By square quarter-turn symmetry and reflection, the first side-frame
angle may be taken `alpha in [0,pi/4]`, and the second square's
side-frame is rotated by theta.

The four signed separating projections on axes of the two squares
have absolute values

    2*r*sin(x)*|sin(x-alpha)|,
    2*r*sin(x)*cos(x-alpha),
    2*r*sin(x)*sin(x+alpha),
    2*r*sin(x)*cos(x+alpha).

All four corresponding sums of support half-widths have the common
value

    b=(1+cos(2*x)+sin(2*x))/2
      =cos(x)*(cos(x)+sin(x)).                           (1)

The largest absolute projection is
`2*r*sin(x)*cos(x-alpha)`. Indeed
`|sin(x-alpha)|<=cos(x-alpha)` because
`|x-alpha|<pi/4`,
`cos(x+alpha)<=cos(x-alpha)`, and

    cos(x-alpha)-sin(x+alpha)
      =(cos(x)-sin(x))*(cos(alpha)-sin(alpha))>=0.

Since adjacent squares have disjoint open interiors, at least one
separating projection is at least b. Therefore

    r >= b/[2*sin(x)*cos(x-alpha)].                      (2)

Put `t=tan(x)` and `k=(1+t)/(2*t)`. Equation (2) becomes

    r >= k/[cos(alpha)+t*sin(alpha)].                    (3)

The farthest squared vertex norm for each unit square is exactly

    Q=r^2+r*(cos(alpha)+sin(alpha))+1/2.                 (4)

Thus it is enough to prove Q>4 for all alpha in [0,pi/4].

## 2. Rational bounds on tan(pi/7) and cos(pi/7)

Use the classical rational upper bound `pi<22/7`.
Thus `0<x<u:=22/49<1`. Alternating Taylor bounds give
for `0<=v<=u`

    sin(v) <= v-v^3/6+v^5/120,
    cos(v) >= 1-v^2/2+v^4/24-v^6/720.

The sine upper polynomial is increasing and the cosine lower
polynomial decreasing on [0,u]. Evaluating at the rational u yields

    (241/500)*(1-u^2/2+u^4/24-u^6/720)
       -(u-u^3/6+u^5/120)
       =56673140981/311428962022500>0,

    (1-u^2/2+u^4/24-u^6/720)-9/10
       =1109229001/1245715848090>0.

The positive denominators and Taylor inequalities prove

    0<t<241/500,      cos(x)>9/10,
    k=(1+t)/(2*t)>741/482.                             (5)

For monotonicity needed below, note also
`t> x>3/7`, using `pi>3` and `tan(v)>v` for v>0.

## 3. Small relative frame angles

First suppose `0<=alpha<=1/6`. The denominator
`D(alpha)=cos(alpha)+t*sin(alpha)` in (3) increases here, since

    D'(alpha)=t*cos(alpha)-sin(alpha)
      >(3/7)*(71/72)-1/6>0.

Alternating Taylor bounds at the rational angle 1/6 give

    D(alpha) <= cos(1/6)+t*sin(1/6)
      < 1-1/72+1/31104+(241/500)/6
      =4146461/3888000.

Hence (3) and (5) imply

    r > (741/482)/(4146461/3888000) > 36/25.          (6)

The last difference is the positive rational
`37904364/24982427525`. Using the trivial
`cos(alpha)+sin(alpha)>=1`, (4) gives

    Q > (36/25)^2+36/25+1/2
      =5017/1250 >4.                                   (7)

## 4. Larger relative frame angles

Now suppose `1/6<=alpha<=pi/4`. Cauchy--Schwarz gives

    D(alpha)<=sqrt(1+t^2)=1/cos(x).

By (3) and (5),

    r >= k*cos(x) > (741/482)*(9/10)
      =6669/4820 >1383/1000.                           (8)

The function `cos(alpha)+sin(alpha)` increases on
[0,pi/4]. Taylor's inequalities give

    cos(alpha)+sin(alpha)
       >=cos(1/6)+sin(1/6)
       >1-1/72+1/6-1/1296
       =1493/1296>23/20.                               (9)

Substitute (8)--(9) in (4):

    Q > (1383/1000)^2+(1383/1000)*(23/20)+1/2
      =4003139/1000000 >4.                             (10)

The small- and large-angle intervals exhaust every square frame;
therefore every such rotationally symmetric seven-square configuration
has farthest squared vertex norm Q>4. This proves the theorem.

## Consequence and limitation

In an eight-square packing of radius less than two, the seven-outer
actual-contact-cycle branch of HUMAN_OUTER_GRAPH_REDUCTION.md
cannot be *exactly* sevenfold rotationally symmetric. The arbitrary
seven-outer-cycle case remains open, as does the outer-path alternative
containing the known tilted candidate. Symmetry cannot be assumed for
a minimizer without an independent symmetrization theorem.
