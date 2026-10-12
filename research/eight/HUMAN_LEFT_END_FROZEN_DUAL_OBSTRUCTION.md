# An exact obstruction to a frozen support-dual proof at the left end

**Status.** A fully analytical negative result for one
particular fixed-normal, circle-support dual. It explains
why the right-end orientation-rigidity proof cannot
simply be reflected onto the left end E.

Let `0<t<arctan(1/5)`,
`c=cos t`, `s=sin t`, `f=(-s,c)`,
`b=(0,1)`. Fix positive w,v with

    tan t < v/w < 1/2,

put `R=sqrt(w^2+v^2)` and define the
unit radial direction of the candidate's
bottom-left E corner by

    nu=(-w,-v)/R=(-a,-d),
    a=w/R,  d=v/R.

The positive decomposition of that radial normal
along the two local separator directions is

    nu=lambda*f-mu*b,
    lambda=a/s>0,    mu=a*c/s+d>0.                    (1)

For a unit-square frame of arbitrary angle theta,
write its centered support function as h_theta.
Consider the associated frozen weighted support sum

    W(theta)=lambda*h_theta(f)
                +mu*h_theta(b)+h_theta(nu).      (2)

**Theorem.** The candidate's axis-aligned frame
theta=0 is **not** the global minimizer of (2).
In fact the exact other orientation theta=t has

    W(t)<W(0).                                       (3)

The hypotheses hold at the least five-corner
stationary family root: its analytical bounds
give `1/2<v<589/1000`, `w>17/10`,
`w<48/25`, and `tan t<1/5`.
Thus `v/w> (1/2)/(48/25)=25/96>1/5>tan t`
and `v/w<(589/1000)/(17/10)<1/2`.
No numerical root box is used.

## Hand proof

Let `L=c+s`, and `z=tan(t/2)`.
Since `0<t<pi/4`, we have `L>1`
and `0<z<1`.
The exact support values at theta=0 are

    h_0(f)=L/2,
    h_0(b)=1/2,
    h_0(nu)=(a+d)/2.                                (4)

At theta=t, the f direction is a side
normal of the rotated square, and

    h_t(f)=1/2,
    h_t(b)=L/2.

Because `d/a=v/w>tan t=s/c`,
the two components of nu in the
rotated e,f frame are both negative.
Their absolute values give

    h_t(nu)=((a+d)*c+(d-a)*s)/2.                 (5)

Substitute (4)--(5) into (2).
Using (1) and `c^2+s^2=1`,
a direct cancellation yields

    W(t)-W(0)
      = d*(L-1)-a*L*(1-c)/s
      = (L-1)*(d-a*K(z)),                          (6)

where the positive coefficient is

    K(z)=L*(1-c)/(s*(L-1))
        =(1+2*z-z^2)/(2*(1-z)) >1/2.             (7)

For the last strict comparison, simply note

    (1+2*z-z^2)-(1-z)=z*(3-z)>0.

Our hypothesis gives `d/a=v/w<1/2`,
so the last expression in (6) is strictly
negative. This proves (3). QED.

## What this does and does not obstruct

The right-end theorem
HUMAN_ANCHORED_END_RIGIDITY.md proves its
weighted support sum has a unique minimum
at the aligned frame. The analogous
left-end sum (2) does **not**: the
tilted frame `theta=t` strictly
reduces the linear support expression.

This does **not** construct a unit square
of smaller containing radius satisfying
the two left-end separators. The full
disk objective is the maximum Euclidean
norm over **four** actual vertices, not
a single chosen radial support projection;
rotating E may make a different vertex
farthest and violate the disk. The
theorem disproves only the frozen
linear-support inequality `W(theta)>=W(0)`.
A global proof could still use a
theta-dependent radial support, multiple
complementary inequalities, or a
simultaneous geometric argument.

In particular the theorem does not
refute the sharp Cantrell candidate
and does not prove or disprove
unrestricted `R8=R_hat`.
