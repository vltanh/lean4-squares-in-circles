# Sharp orientation losses at the two end squares of the five-corner chain

**Status:** complete analytic point-selection lemma, sharp for every
`0<=t<=pi/4`. This extends HUMAN_TWO_ALIGNED_ENDS.md to arbitrary
orientations of the end squares **with precisely quantified losses**.
It does NOT prove the unrestricted optimal packing radius: at positive
tilt these losses need additional geometric slack to be recovered.

Write `a=(1,0)`, `b=(0,1)`,
`e=(cos t,sin t)`, `f=(-sin t,cos t)`, and
`z=tan(t/2)`.

## The sharp two end-cap point lemmas

Let S be any unit square centered at p with arbitrary orientation,
and let `h_S` be its centered support function. There exist points
`X_+(S,t)` and `X_-(S,t)` of S (not necessarily identical) such that

    b dot(X_+-p) <= h_S(b)-1,
    h_S(e)+e dot(X_+-p) >= 1-z,                    (1)

and

    b dot(X_--p) <= h_S(b)-1,
    h_S(f)+f dot(X_--p) >= 2*z/(1+z).             (2)

Both lower constants are the **best possible universal** ones
for each fixed tilt t. A square whose e-side frame has angle t
to a gives equality in (1) at its maximizing eligible point.
The same square gives equality in (2).
At t=0 the sharp constants are 1 and 0; for positive tilt
the losses relative to aligned square corner projections
are respectively

    epsilon_A(t)=cos t-(1-z)
                 =sin t*(1-sin t)/(1+cos t),

    epsilon_E(t)=sin t-2*z/(1+z)
                 =(1-cos t)*(1-sin t)/cos t.     (3)

In particular `0<=epsilon_E<=epsilon_A`, with strict inequality
for `0<t<pi/4`. Formula (3) follows by substituting
`z=sin t/(1+cos t)`. The comparison reduces to
`sin t<=cos t`.

### 1. Reduction to signed square-frame angles

By quarter-turn symmetry choose the side-frame angle
`theta in [-pi/4,pi/4]`. Put `gamma=|theta|`,
`C=cos gamma`, `S=sin gamma`, `L=C+S`,
`beta=tan(gamma/2)`, and

    m=1-L/2,       d=(L-1)/C=2*beta/(1+beta).

Here `0<=beta<=b0:=tan(pi/8)=sqrt(2)-1`,
`0<=d<1`, and `h_S(b)=L/2`.
Translate p to zero. The required vertical cap is simply

    y<=-m.                                             (4)

Let `E_theta=(cos theta,sin theta)` and
`F_theta=(-sin theta,cos theta)`.

When theta=+gamma choose

    X_+-p=(1/2-beta)*E_theta-(1/2)*F_theta,
    X_--p=-(1/2)*E_theta+(-1/2+d)*F_theta.        (5)

When theta=-gamma choose

    X_+-p=(1/2)*E_theta+(-1/2+d)*F_theta,
    X_--p=(-1/2+beta)*E_theta-(1/2)*F_theta.     (6)

All four local coordinates lie in [-1/2,1/2], so each
selected point belongs to S. The identity
`beta*S=1-C` for (5) and `d*C=L-1` for (6)
show directly that every selected point has
`b dot(X-p)=-m`. Thus all satisfy the vertical
cap (4) with equality. It remains only to estimate
the other projections.

### 2. The A-type e-projection for nonnegative frames

Suppose theta=gamma>=0. Since `0<=t,gamma<=pi/4`,
the e-projected half-width is

    h_S(e)=(cos(t-gamma)+|sin(t-gamma)|)/2.

For X_+ in (5), direct dot products give
`J_+(gamma,t)=h_S(e)+e dot(X_+-p)` equal to

    (1-beta)*cos(t-gamma),                         gamma<=t,
    (1-beta)*cos(gamma-t)+sin(gamma-t),             gamma>=t.   (7)

On [0,t] the first expression is concave in gamma.
Indeed `beta'=(1+beta^2)/2>0`, `beta''=beta*beta'>=0`;
writing `v=t-gamma` gives

    J_+''=-(1-beta+beta'')*cos v-2*beta'*sin v <0.

Its minimum is therefore at gamma=0 or gamma=t.
The endpoint values are `cos t` and `1-z`.
The former is at least the latter, since

    cos t-(1-z)=z*(1-z)^2/(1+z^2)>=0.               (8)

On [t,pi/4] the second expression in (7) is also
strictly concave. With `v=gamma-t`,

    J_+''=-(1-beta+beta'')*cos v+beta^2*sin v<0,

because `sin v<=cos v` and
`1-beta>beta^2` for `0<=beta<=sqrt(2)-1`.
Thus it suffices to check its endpoints gamma=t
and gamma=pi/4.

At gamma=t its value is 1-z. At gamma=pi/4 put
`b0=sqrt(2)-1`; the value is

    D(t)=(1-b0)*cos(pi/4-t)+sin(pi/4-t).

Direct use of `cos t=(1-z^2)/(1+z^2)` and
`sin t=2z/(1+z^2)` gives the exact factorization

    (1+z^2)*(D(t)-(1-z))
      =(z-b0)*
        [z^2-(1+sqrt(2)/2)*z-(1-sqrt(2)/2)].      (9)

The first factor is nonpositive. The bracket is
strictly negative: since `z<=b0<1/2`,
`z^2<=z/2`, so the bracket is bounded above by
`-(1+sqrt(2))z/2-(1-sqrt(2)/2)<0`.
Hence `D(t)>=1-z`. Concavity proves (1)
for every nonnegative frame angle.

### 3. The A-type e-projection for negative frames

Now theta=-gamma<=0 and choose X_+ from (6).
The same dot-product calculation, using
`d=2*beta/(1+beta)`, gives

    J_-(gamma,t)
      =cos(t+gamma)+d*sin(t+gamma).               (10)

Differentiate:

    dJ_-/dgamma =
      [2*beta/(1+beta)^2]*
      [(1+beta)*cos(t+gamma)-sin(t+gamma)].       (11)

The sign of the bracket changes at most once
from positive to negative, because
`tan(t+gamma)-(1+beta)` is strictly increasing
where `t+gamma<pi/2`:

    d/dgamma [tan(t+gamma)-(1+beta)]
       =sec^2(t+gamma)-beta'>0,

as `beta'<1`. At gamma=0, `tan t<=1`.
Thus J_- first increases and then decreases
(or is monotone), and its minimum is at one of
gamma=0, gamma=pi/4.

The endpoint values are `cos t` and the
same D(t) from section 2, because at pi/4
the two signed frames describe the same square.
Both are at least `1-z` by (8)--(9).
This completes the hand proof of (1).

### 4. The E-type f-projection for nonnegative frames

For theta=gamma>=0 choose X_- from (5). Then
`h_S(f)+f dot(X_--p)` is

    J_E(gamma,t)=d*cos(t-gamma)+sin(t-gamma),      gamma<=t,
    J_E(gamma,t)=d*cos(gamma-t),                   gamma>=t.  (12)

On [0,t], differentiating the first expression gives

    J_E'=[2*beta/(1+beta)^2]*
          [(1+beta)*sin(t-gamma)-cos(t-gamma)] <=0.

For the sign, `tan(t-gamma)<=tan(pi/4-gamma)`
and, writing `T=tan gamma=2*beta/(1-beta^2)`,

    (1+beta)*tan(pi/4-gamma)
       =(1+beta)*(1-T)/(1+T)<=1,

since `(2+beta)T>=beta`. The derivative is
nonpositive, so the first branch decreases to
`d(t)=2z/(1+z)`.

On [t,pi/4], differentiating the second gives

    J_E'=d'*cos(gamma-t)-d*sin(gamma-t)>=0.

Indeed `d'=(1+beta^2)/(1+beta)^2>=d`
because `1-2beta-beta^2>=0` on
`[0,sqrt(2)-1]`, and
`cos(gamma-t)>=sin(gamma-t)`.
This branch increases from `d(t)`.
Thus (2) holds for every nonnegative frame.

### 5. The E-type f-projection for negative frames

For theta=-gamma<=0 choose X_- from (6). Then

    J_E^-(gamma,t)=(1-beta)*sin(t+gamma).           (13)

Its second derivative in gamma is

    -(1-beta+beta'')*sin(t+gamma)
            -2*beta'*cos(t+gamma)<0,

so its minimum occurs at gamma=0 or gamma=pi/4.
The first endpoint is `sin t>=2z/(1+z)`,
the difference being `(1-cos t)*(1-sin t)/cos t>=0`.

The other endpoint is
`(1-b0)*sin(t+pi/4)=b0*(cos t+sin t)`.
The exact factorization

    (1+z^2)*(1+z)*
      [b0*(cos t+sin t)-2z/(1+z)]
     =-(sqrt(2)+1)*(z-b0)*
       [z^2+(3*sqrt(2)-4)*z+(sqrt(2)-1)] >=0          (14)

proves the other endpoint comparison.
Indeed `z-b0<=0` and every coefficient in the
last bracket is nonnegative (strictly positive
except possibly at z=0). This establishes (2).

### 6. Sharpness of the two constants

For fixed t choose the square with side frame
`E_t=(cos t,sin t)`, `F_t=(-sin t,cos t)`
and center at zero. Its vertical cap (4) is
`b dot x<=h_S(b)-1`.

Write `x=xi*E_t+eta*F_t` with
`|xi|,|eta|<=1/2`. The cap gives

    sin t*xi+cos t*eta<=h_S(b)-1.

For t>0, using `eta>=-1/2` implies
`xi<=1/2-z`, so `h_S(e)+e dot x<=1-z`.
The chosen X_+ from (5) attains equality.
Similarly using `xi>=-1/2` gives
`eta<=-1/2+d(t)`, so
`h_S(f)+f dot x<=d(t)`; X_- attains equality.
For t=0, the same constants are achieved
on the bottom edge of the axis-aligned square.
Thus both constants are optimal.

## Conditional consequence for an arbitrary-frame five-corner chain

Keep the six directed outer-chain and oblique **full-square
separating projections** (1)--(2) of
HUMAN_TWO_ALIGNED_ENDS.md, but remove the assumption
that A and E have parallel side frames. All six
square frames may now be arbitrary.

Choose the canonical upper/right point in B,
the canonical upper/left point in D, and the
special lower/right or lower/left cap points
`P1=X_+(A,t)`, `P4=X_-(E,t)`.
Their vertical projections satisfy the original
A--B and D--E two-unit inequalities, because
`b dot(P1-p_A),b dot(P4-p_E)<=h(b)-1`.
The B--D three-unit horizontal inequality
continues to hold by the canonical point lemma.

Choose `P5` in H using the simultaneous
two-axis point of HUMAN_TWO_ALIGNED_ENDS.md.
The same sum of the e-directed and f-directed
separator inequalities now yields the explicit
**unconditionally rotated-end** projected chain

    b dot(P2-P1)>=2,
    a dot(P2-P3)>=3,
    b dot(P3-P4)>=2,
    f dot(P4-P5)>=1+2*z/(1+z),
    e dot(P1-P5)>=3-z.                                (15)

These are valid five disk points for every allowed
orientation of all six source squares. At t=0
the bounds equal the original sharp five-corner
oblique thresholds. For t>0 they are weaker by
the sharp losses (3), and therefore the already
proved sharp conditional optimization theorem
cannot simply be invoked: its hypotheses use
`1+sin t` and `2+cos t`, respectively.

A global n=8 theorem must recover those losses
from additional packing constraints, force
the aligned-end branch, or prove a sharp
alternative. **This note does not establish
R8>=Rhat.**


## Exact orientation-sensitive slack criterion

The proof above actually gives useful **orientation-specific**
thresholds, rather than only the universal worst cases.
Let `theta_A,theta_E in [-pi/4,pi/4]` be the
signed end-square frame angles relative to a.
Define `J_A(theta,t)` by the explicit formulas
(7) for `theta>=0` and (10) for `theta<0`.
Define `J_E(theta,t)` by (12) for
`theta>=0` and (13) for `theta<0`.
These are the `h(e)+e dot(X-p)` and
`h(f)+f dot(X-p)` values of the **explicit**
selected points (5)--(6), not fitted bounds.

Put

    delta_A(theta,t)=max(0,cos(t)-J_A(theta,t)),
    delta_E(theta,t)=max(0,sin(t)-J_E(theta,t)).

The proved universal bounds give

    0<=delta_A(theta,t)<=epsilon_A(t),
    0<=delta_E(theta,t)<=epsilon_E(t).               (16)

For aligned end frames theta_A=theta_E=0,
both deficits are zero, as required for the
original exact five-corner equality model.
The worst-case `theta=t` attains both upper
bounds in (16), so they cannot be improved
without retaining more geometric information.

**Corollary (sharp-family obstruction with slack).**
Allow all six square frames A,B,D,E,G,H to
be arbitrary. Assume the three outer-chain
separating projections from HUMAN_TWO_ALIGNED_ENDS.md
and choose one coherent e,f frame.
Suppose the oblique projected gaps have
nonnegative extra reserves `sigma_e,sigma_f`
beyond the basic full-square support sums,
with

    e dot(p_A-p_H)
       >=h_A(e)+2*h_G(e)+h_H(e)+sigma_e,
    f dot(p_E-p_H)
       >=h_E(f)+h_H(f)+sigma_f.

(The first displayed reserve follows if the
two successive e separators A-G and G-H
have total slack `sigma_e`.)

If

    sigma_e>=delta_A(theta_A,t),
    sigma_f>=delta_E(theta_E,t),                      (17)

then the five points selected above satisfy
**all five original sharp** five-corner
inequalities, not only the weakened (15).
The exact family theorem therefore gives
`R>=R_hat`.

**Proof.** The first three projections are
unchanged. The extra e reserve increases
the bound in (15) from
`2+J_A(theta_A,t)` to
`2+J_A(theta_A,t)+sigma_e>=2+cos t`.
The f reserve similarly increases its
bound from `1+J_E(theta_E,t)`
to `1+J_E(theta_E,t)+sigma_f>=1+sin t`.
The same P5 is used throughout. QED.

Condition (17) is a **sufficient conditional
criterion**; an arbitrary minimizer is not
known to satisfy it. In the candidate's aligned
end squares the deficits and separator reserves
are all zero, recovering equality. For rotated
end squares the reserves are not automatic and
must be proved from *other* packing constraints.
This is an explicit, exact formulation of the
still missing structural compensation.
