# Stronger loaded-run angles: frozen research handoff

**Status: UNREVIEWED RESEARCH, 2026-10-31.** This records calculations
already reached when the user requested a handoff. It is not a theorem,
an exact certificate for the stronger bound, or a further case closure.

The completed result is
[LOADED_THREE_RAY_ANGLE_BOUND.md](LOADED_THREE_RAY_ANGLE_BOUND.md), with
its exact 24-row verifier. Root and an independent reviewer passed its
entire proof and independently reconstructed the table. It excludes
`C20-M08-L07-B01-T02 LLLLLLLD`. Those two files are frozen.

## Stronger target and the numerical evidence

A possible next shared target is

```text
two consecutive loaded center-ray gaps
    > pi/2-atan(1/45).
```

Together with sharper already available D-cap estimates, this may exclude
two remaining five-loaded/two-D cycles. That consequence has not been
written or checked here. Merely increasing the one-sided constant in
the completed theorem does not suffice: the two sides of the same
middle frame must be coupled.

Numerical exploration fixed the middle center ray, varied its relative
frame alpha, and optimized each neighboring loaded square independently
at squared radius 9/2. Some outputs, in degrees, were:

| Middle frame alpha | First minimum gap | Reflected minimum gap | Sum |
| --- | ---: | ---: | ---: |
| 0 | 44.62306 | 44.62306 | 89.24611 |
| 5 | 42.67094 | 46.42931 | 89.10024 |
| 10 | 41.16661 | 47.74739 | 88.91400 |
| 12.5 | 40.67518 | 48.22128 | 88.89646 |
| 20 | 40.07843 | 48.92865 | 89.00708 |
| 30 | 40.95904 | 48.36295 | 89.32199 |
| 45 | 44.94223 | 44.94223 | 89.88447 |

These floating-point probes are not lower bounds or certified minima.
They suggest both the plausibility of the stronger target and the
failure of a naive universal 90-degree two-gap claim. They must not be
used as proof premises. The exploratory script is preserved as
[explore_loaded_pair_frame.py](explore_loaded_pair_frame.py), with an explicit
non-proof warning.

## Radius reduction that may support a complete orientation table

The completed theorem only needed radial inflation when a separator
had opposite-sign center projections. A more general calculation may
remove that restriction.

For a loaded square with fixed frame and fixed center ray, its radius r
in a containing circle of radius R satisfies

```text
r^2+w r+1/2=R^2,        1<=w<=sqrt(2),
r'=R/sqrt(R^2-1/2+w^2/4).
```

Throughout the existing radius window, the known center bounds give
`5/4<r<25/16`, while `1<=r'<9/8`. Thus

```text
16/25 < g:=r'/r < 9/10.
```

For a fixed separating axis n, let
`d=n dot(c_j-c_i)>=h_i+h_j>=1`, where the directional halfwidths are
constant under this radial motion. Using the smaller of g_i,g_j as
the common coefficient leaves only one correction term, so

```text
d' >= (16/25)d-(9/10-16/25)(25/16)
    >=187/800>0.
```

This suggests that a fixed separating-axis inequality cannot cross
downward through its threshold during inflation to `R=3/sqrt(2)`.
A complete writeup should state and verify the continuation argument
for every original pair separator. No standalone reviewed theorem for
this general inflation has been added.

## Why the completed small-offset argument cannot simply be reused

The stronger target permits one individual gap near 49 degrees. The
completed proof inferred `|separator offset|<1/2` from a gap below
45 degrees; that inference is unavailable here. This is a real proof
obligation, even though the numerical minimizing configurations above
seem to have useful separators.

In the lower-neighbor convention of the completed proof, write

```text
n=(sin(beta),cos(beta)),
A(alpha,beta)=r(alpha)sin(beta)
 -(abs(sin(beta+alpha))+abs(cos(beta+alpha)))/2.
```

When the neighboring center has nonpositive projection on n, its
largest possible inward support offset can still be bounded by the
axis-parallel cap function B(gamma), with the correct reflected angle
gamma. If the proposed cap offset is at most -1/2, the corresponding
upper bound is automatic; otherwise the reviewed extended cap theorem
applies. The full beta domain and the angle reflections still need to
be handled explicitly.

For the same-sign case `beta>=delta`, root suggested the necessary
bound

```text
A(alpha,beta)-sqrt(2)sin(beta-delta)-1/2 >=0.
```

It uses the neighboring loaded center's radius at least sqrt(2) at the
largest containing radius and its halfwidth at least 1/2. On every
fixed absolute-value branch this is an explicit sinusoid minus 1/2;
its maximum can be bounded exactly. This could complement a rational
table for the opposite-sign region. No covering table has been made.

## A possible convexity reduction for a coupled frame table

At squared radius 9/2 put `w=cos(alpha)+sin(alpha)` for
`0<=alpha<=pi/4`. The radius function obeys

```text
r''=(1/2)[w-(w^4+32w^2-32)/(w^2+16)^(3/2)].
```

The existing differentiation proves r''>0. A further calculation
suggests the useful bound r''<1/2. Squaring the positive quantities
needed for that comparison yields

```text
(w^4+32w^2-32)^2-(w-1)^2(w^2+16)^3
 =2z^7+29z^6+228z^5+919z^4+3442z^3-213z^2+136z+1,
z=w-1 in [0,sqrt(2)-1].
```

Since z<1/2, the last quadratic/linear pair has positive sum for z>0,
and the constant is positive. This is a candidate exact proof of the
upper bound.

If verified, on every smooth absolute-value branch one obtains

```text
partial_alpha^2 A = r'' sin(beta)+h >0,
h=(abs(sin(beta+alpha))+abs(cos(beta+alpha)))/2>=1/2.
```

The maximum over an alpha interval would therefore occur at an endpoint
or at an intervening side-normal kink. The kink values also need to be
included; omitting them would invalidate the reduction. This may reduce
a coupled frame certificate to a finite collection of one-dimensional
separator tables, with suitable lower bounds for both neighboring gaps
on each frame interval. Those tables and the final coupling are the
unfinished work.

The 14 pure-S whole-cycle obligations remain open. The new triple bound
alone does not supply their missing completion capacity or longer-run
stress constraints. No further master-leaf status follows from this note.
