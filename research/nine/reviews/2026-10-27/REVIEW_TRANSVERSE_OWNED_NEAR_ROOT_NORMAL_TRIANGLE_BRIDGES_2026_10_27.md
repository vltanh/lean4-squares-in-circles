# Independent validation of the transverse-owned near-root calculation

Date: October 27, 2026.

Reviewer: triangle_bridges. **Decision: ACCEPTED, with no correction.**

This is a separate independent validation of the calculation supplied by
root and recorded in Section 1 of
`GENUINE_S_THREE_FORCE_ROOT_TWO_NEAR_NEIGHBORS_FRESH_DOMAIN.md`, SHA-256
`5dba416ea7bfd8500daf6f33bcecd56521dd7013f2357b9442964d2c49edb480`.
It does not call my own remaining sections of that source independently
reviewed. Its scope is precisely the full North/South calculation below.

## 1. Original hypotheses and unchanged applications

Let an actual unloaded genuine S root of true degree three have the aligned
frame

    B=[epsilon,1+epsilon] x [-b,a],
    a,b>=0, a+b=1, 0<epsilon<1/60.

Its real leaf force is beta East, beta>0, with radial application
(1+epsilon,0). Both other actual neighbors contain a point of the closed
epsilon disk. Consequently the support of each original B-outward contact
normal is at most epsilon. This uses the physical neighbor half-plane,
not any force or degree premise at either neighbor.

Suppose the first actual normal is North and its positive magnitude is mu.
Its original mean is (x,a), with epsilon<=x<=1+epsilon, and its support
gives a<=epsilon. Thus b=1-a>59/60.

## 2. Independent full force and torque derivation

The entire three-force balance gives the second nonleaf force

    (-beta,-mu).

Both components are strictly negative, so its actual B application is the
fixed lower-left vertex (epsilon,-b). No contact mean is replaced. About
the original circle origin, the two nonzero moments are

    mu*x,             -mu*epsilon-beta*b.

The leaf has zero moment. Their sum is zero, so, putting k=beta/mu>0,

    x=epsilon+b*k.

The original top-side mean bound x<=1+epsilon now gives

    k<=1/b<60/59.

This retains both endpoints of the permitted mean interval. In particular
no midpoint, side-interior, neighbor adjacency or proper-concurrence premise
has entered the argument.

The unit direction of the second force is (-k,-1)/sqrt(1+k^2). Its actual
support at the lower-left vertex is therefore

    (b-epsilon*k)/sqrt(1+k^2).

The numerator is strictly greater than 59/60-1/59>0. Independently,

    9/4-(1+3600/3481)=3005/13924>0,

so the denominator is strictly less than 3/2. The support consequently
satisfies

    h_B(n_C) > (59/60-1/59)/(3/2)
             =3421/5310
             >1/60>epsilon.

I recomputed these identities with exact fractions. The reserve over 1/60
is 1333/2124. This contradicts the original near-neighbor support bound.

Reflection in the horizontal axis supplies the complete South case. It
reflects the actual top/bottom mean and the entire force system, so all
corresponding endpoint cases are included.

## 3. Accepted scope

The root-authored calculation is sound for arbitrary actual degrees,
loads and circle masks of the other two neighbors, without an edge between
them. It keeps the genuine leaf and all three original root forces. The
actual graph may remain part of the original nine-square certificate; no
other force, normal, application, square or weight is modified.

This independent record accepts that local calculation only. A whole
attachment still needs the remaining feature cover and its actual callers.
