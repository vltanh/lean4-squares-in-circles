# Exact end-square frame rigidity from two fixed separators and a disk vertex

**Status.** Complete elementary hand proof of an **anchored
local uniqueness theorem**. Unlike a purely infinitesimal
stationarity calculation, it excludes every alternative
orientation over the entire square frame circle. It
does **not** force the required neighboring contact
pattern in arbitrary eight-square minimizers.

## Theorem

Let `r,u,R,t` satisfy

    r^2+u^2=R^2,
    r>17/10,    0<u<1,    0<t<arctan(1/5).

Set `c=cos t`, `s=sin t`,
`e=(c,s)`, `b=(0,1)`, and

    p0=(r-1/2,1/2-u),    v=(r,-u)/R.

Thus `v` is the outward unit radial direction of
the **bottom-right vertex** of the axis-parallel
unit square centered at p0, which lies on D_R.

Let S be **any** unit square centered at p, with
arbitrary orientation and entirely contained in D_R.
Suppose its center obeys both directed support
constraints

    b dot p <= b dot p0 +1/2-h_S(b),                (1)
    e dot p >= e dot p0 +h_S(e)-(c+s)/2.           (2)

These are exactly the constraints obtained by
holding fixed the relevant support lines of
two candidate neighboring squares: (1) is the
A-B vertical gap, and (2) is the A-G oblique gap.
They do not assume that S touches either neighbor.

**Conclusion:** S is the axis-parallel square
centered exactly at p0. That is, its side frame
is horizontal/vertical up to signs and quarter
turns, and p=p0.

The proof requires **no** tiny numerical
isolating box for R or t, no circle-contact
stress, and no sample of frame angles.

## 1. A positive two-support decomposition of the radial normal

Write

    a=r/R,    d=u/R,    so a^2+d^2=1, a>d>0.

The unit vector v=(a,-d) has the exact positive
decomposition

    v=lambda*e-mu*b,
    lambda=a/c>0,    mu=d+a*tan t>0.                (3)

The bounds imply `u/r<10/17` and
`tan t<1/5`. Therefore the angle
`alpha=arctan(u/r)` satisfies

    tan(alpha+t)
      < (10/17+1/5)/(1-(10/17)*(1/5))
      =67/75<1,

so

    -pi/4<phi:=-alpha<0<t<pi/4,
    alpha+t<pi/4.                                  (4)

The frame angle of S can, by square symmetry,
be chosen `theta in [-pi/4,pi/4]`.

## 2. Disk containment becomes a weighted support inequality

For a unit square of frame angle theta write

    h_theta(n)=(|n dot e_theta|+|n dot f_theta|)/2,

where `e_theta=(cos theta,sin theta)`,
`f_theta=(-sin theta,cos theta)`.

Its full support in direction v is
`v dot p+h_theta(v)`. Since S lies in D_R,

    R>=v dot p+h_theta(v).                          (5)

Constraints (1)--(2) and (3) give

    v dot p
      >=v dot p0
          +lambda*(h_theta(e)-h_0(e))
          +mu*(h_theta(b)-h_0(b)).                  (6)

The fixed reference square has its bottom-right
vertex at Rv. Hence

    v dot p0+h_0(v)=R.                              (7)

Define the purely one-angle weighted width

    W(theta)=lambda*h_theta(e)
             +mu*h_theta(b)+h_theta(v).

Equations (5)--(7) immediately yield

    0>=W(theta)-W(0).                               (8)

We prove the opposite inequality strictly
unless theta=0, forcing that orientation.

## 3. Strict concavity reduces all angles to four checks

For any fixed unit direction `n` at angle psi,

    h_theta(n)=
      (|cos(psi-theta)|+|sin(psi-theta)|)/2.

On each angular interval where the two absolute
value signs have fixed arguments, its second
derivative is `-h_theta(n)`. Since lambda,mu>0,

    W''(theta)=-W(theta)<0                            (9)

on every such open interval.

By (4), the **only** non-smooth interior
angles of W in `[-pi/4,pi/4]` are

    phi=-alpha,  0,  t.

Strict concavity on each of the four resulting
intervals places the minimum at an endpoint.
The frames theta=-pi/4 and theta=+pi/4 describe
the same square orientation, so their W values
are equal. We therefore need to check only
theta=phi, theta=t, and theta=pi/4
against theta=0.

The exact value at the reference frame is

    W(0)=a+mu.                                        (10)

The three endpoint differences, by direct
support-function substitution and
`a^2+d^2=c^2+s^2=1`, simplify to

    W(t)-W(0)
       =(1-c)*[a*(1-s)/c-d],                          (11)

    W(phi)-W(0)
       =(1-a)*[1-d-a*tan t],                          (12)

    W(pi/4)-W(0)
       =[(sqrt(2)-1)/sqrt(2)]*[sqrt(2)*a-mu].         (13)

For clarity, the substitutions used here are

    h_0(e)=(c+s)/2, h_0(b)=1/2,
    h_0(v)=(a+d)/2,

    h_t(e)=1/2, h_t(b)=(c+s)/2,
    h_t(v)=((a+d)*c+(a-d)*s)/2,

    h_phi(e)=((a+d)*c+(a-d)*s)/2,
    h_phi(b)=(a+d)/2, h_phi(v)=1/2,

    h_(pi/4)(e)=c/sqrt(2),
    h_(pi/4)(b)=1/sqrt(2),
    h_(pi/4)(v)=a/sqrt(2).

The sign information in (4) makes every
listed absolute-value branch valid.

All three differences are **strictly positive**:

* For (11), since `s<1/5`,
  `r*(1-s)>(17/10)*(4/5)>1>u*c`.
  Dividing by positive R*c gives
  `a*(1-s)/c>d`. Also t>0 gives 1-c>0.
* For (12), `a<1` because u>0. Moreover
  `d=u/R<u/r<10/17`, so
  `1-d>7/17>1/5>a*tan t`.
* For (13), `mu/a=u/r+tan t
   <10/17+1/5=67/85<1<sqrt(2)`.

By strict concavity (9), every angle
other than theta=0 has W(theta)>W(0):
the four open intervals lie above
their endpoint minima, and all the
other endpoint values exceed W(0).

Equation (8) therefore forces
`theta=0` modulo right-angle square
symmetry. This proves **global frame
rigidity**, not merely local stiffness.

## 4. The square center is unique too

With theta=0, constraints (1)--(2)
reduce to

    b dot p <= b dot p0,       e dot p>=e dot p0.

By (3),

    v dot(p-p0)
      =lambda*e dot(p-p0)-mu*b dot(p-p0)>=0.

But (5) and (7), now with the same
support function h_0, give
`v dot(p-p0)<=0`. Both inequalities
therefore have equality. As
lambda,mu>0, each of the two original
signed projection differences must be
zero. Since e and b are linearly
independent (c>0), we get p=p0.
The theorem is proved.

## 5. Application and remaining global gate

The exact least-five-corner configuration
already satisfies `r>17/10`,
`0<u<1` and `0<t<arctan(1/5)`
by HUMAN_FAMILY_CLOSURE.md. Its right-hand
square A and neighboring B,G realize
the two support bounds (1)--(2)
with equality and have their
bottom-right disk vertex Rv.

Therefore, **if B and G retain their
candidate supporting lines**, no
alternative position or orientation of
A can fit the same disk while maintaining
those two necessary separators.

This makes a piece of the candidate
rigid while its independent sliders
remain free. However the theorem
holds the two neighboring support
thresholds fixed. A general
eight-square minimizer is not known
to contain those neighbors or those
two coherently directed separators,
and they could move collectively.
Nothing here proves unrestricted
`R8>=Rhat`. The orientation
classification is conditional on the
displayed real geometric constraints.
