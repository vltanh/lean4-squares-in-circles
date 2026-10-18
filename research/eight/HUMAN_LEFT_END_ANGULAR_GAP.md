# A one-sided orientation lock for the left end of the sharp chain

**Scope:** exact hand theorem for a *fixed-neighbor* two-separator
problem, directly targeting the remaining aligned-end assumption in
HUMAN_TWO_ALIGNED_ENDS.md. It is not a global n=8 theorem.

Let w>v>1/2, R=sqrt(w^2+v^2), and 0<t<arctan(1/5)
with tan(t)<v/w<1/2. Write c=cos(t), s=sin(t),
b=(0,1), f=(-s,c), and p0=(1/2-w,1/2-v).
The axis-parallel square at p0 has its bottom-left
vertex (-w,-v) exactly on the radius-R circle.

Let S be any unit square with frame angle
theta in [-pi/4,pi/4], center p, and S subset D_R.
Assume its two *directed, full-square* supporting
projections satisfy

    b dot p <= b dot p0 + 1/2 - h_theta(b),
    f dot p >= f dot p0 + h_theta(f) - h_0(f).       (1)

The thresholds in (1) are fixed from the two
neighbor support lines of the candidate left-end
square E, but the square S is free to translate
and rotate. As usual h_theta(n) is the centered
unit-square support in unit direction n.

**Theorem.**

1. No angle -pi/4 <= theta < 0 is feasible.
2. If 0 < theta <= t is feasible, then necessarily

       tan(theta/2) >= v/(w+v+w*c/s).               (2)

Thus the entire negative half of the square's
frame circle, and an explicit interval of small
positive rotations, is ruled out by the *exact
disk constraint* and only the two projections
in (1). The positive-tilt region beyond (2)
and the sector theta>t require an additional
support direction or a nonlinear comparison;
they are not excluded by this theorem.

## Hand proof

Put a=w/R, d=v/R. Thus a>d>0 and a^2+d^2=1.
Let the outward unit radial normal of the
bottom-left reference disk vertex be

    nu=(-a,-d).

It has the positive decomposition

    nu=lambda*f-mu*b,
    lambda=a/s>0,
    mu=a*c/s+d>0.                                   (3)

Multiplying (1) by lambda and mu in their
respective directed senses gives

    nu dot p >= nu dot p0
        +lambda*(h_theta(f)-h_0(f))
        +mu*(h_theta(b)-h_0(b)).                     (4)

Since S fits D_R, its support in direction nu
obeys

    nu dot p+h_theta(nu) <=R.

The reference support is exactly tight:

    nu dot p0+h_0(nu)=R,

because the point (-w,-v)=R*nu belongs to
the reference square. Combining these
identities yields the necessary inequality

    W(theta)<=W(0),
    W(theta)=h_theta(nu)
                 +lambda*h_theta(f)+mu*h_theta(b).   (5)

We evaluate this function on the indicated
angle intervals, without numerical sampling.

Set C=cos(theta), S=sin(theta). For every
theta in [-pi/4,t], the local projections
of nu in the rotated square frame are both
strictly negative. Indeed

    nu dot e_theta=-a*C-d*S<0
    nu dot f_theta= a*S-d*C<0,

using a>d, |S|<=C when theta<=0, and
tan(t)<d/a when theta>=0. Also
0<t-theta<pi/2, so

    h_theta(nu)=((a+d)*C+(d-a)*S)/2,
    h_theta(f)=((c+s)*C+(s-c)*S)/2.                (6)

The vertical support has the two forms

    h_theta(b)=(C-S)/2  when theta<=0,
    h_theta(b)=(C+S)/2  when theta>=0.

Substitute in (5) and simplify using (3).
The exact value at zero is

    W0:=W(0)=a+d+a*c/s.

The entire variable dependence collapses to

    W(theta)=W0*C-(a*c/s)*S,  -pi/4<=theta<=0,
    W(theta)=W0*C+d*S,         0<=theta<=t.          (7)

For negative theta, W(theta)<=W0 would require

    (a*c/s)*sin(|theta|)
       <=W0*(1-cos(|theta|)).

Dividing by the positive sine gives

    tan(|theta|/2) >= (a*c/s)/W0
                   =1/[1+(1+v/w)*tan(t)].

The last quantity exceeds

    1/[1+(3/2)*(1/5)]=10/13,

whereas tan(|theta|/2)<=tan(pi/8)=sqrt(2)-1<1/2.
This contradiction proves (1).

For 0<theta<=t, the second expression in
(7) and the necessary condition (5) give

    d*sin(theta)<=W0*(1-cos(theta)).

Dividing by sin(theta)>0 and using
(1-cos(theta))/sin(theta)=tan(theta/2),
we obtain

    tan(theta/2)>=d/W0
       =v/[w+v+w*c/s].

This is (2) and completes the proof.

## Exact use and remaining task

The least five-corner stationary parameters
satisfy the displayed hypotheses by
HUMAN_FAMILY_CLOSURE.md and
ANALYTIC_EXACT_CONSTRUCTION.md:
w>17/10, v>1/2, v<589/1000, w<48/25,
and 0<t<arctan(1/5). In particular
v/w>(1/2)/(48/25)=25/96>1/5>tan t
and v/w<(589/1000)/(17/10)<1/2.

Thus **the exact candidate left end E cannot
rotate to any negative-frame angle, nor through
the initial explicit positive interval,
while its two neighbor support thresholds
are held fixed and the radius stays Rhat.**

This is not yet full anchored E rigidity:
a small interval of positive tilts survives
the single radial normal test, because a
different disk vertex becomes controlling.
More importantly, the unrestricted n=8
problem does not prescribe these two
neighbor support lines. Its global
lower-bound gate R8>=Rhat remains open.
