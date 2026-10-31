# Root review: two proper ports and a forbidden nonpositive resultant ray

Date: October 26, 2026.

**Decision: ACCEPT the complete uniform local geometric theorem.**
Its explicit negative-concurrence and two-proper-port premises must be
proved separately in every original terminal-block application.

Reviewed source: `ROOTED_NONPOSITIVE_RAY_PROPER_PORT_CAP_EXCLUSION.md`.
Exact mathematical source pin before acceptance-status edits:

    73c0f974372e3ea6a58e673cb3e9194431c92af252413193aa90c3437c830ab4

I read and checked the whole source, including its continuous own-frame
feature cover, actual moment identity, center-cap estimate and stated
application limits. No assertion about an unspecified root equation or
an individual neighbor load is used.

## 1. The ray and convex-combination step

Nonparallel positive root forces have nonzero sum M. The given
q=-tM, t>0, belongs to the excluded ray and hence is outside closed K.
Both proper lengths a_i are strictly positive, since a zero would put
q at a real port in K. The positive weighted average of the actual ports
with weights mu_i/a_i gives exactly q+M/W in K. Its coefficient of M
must be strictly positive by the excluded-ray premise. Thus K contains
a point rM, r>0, while O is outside K.

An own coordinate interval of the actual square consequently misses O
strictly. Reflect it to [a,a+1], a>0. The positive-ray point makes
M_x>0, and q_x<0 makes both outward normals have positive x-component.
Both ports therefore lie on the same far side x=A=a+1>1. This common
side is forced from the actual support geometry, not selected afresh.

## 2. Every normal feature and the moment inequality

Two positive (or two negative) transverse normal components would put
both ports at the same far-side vertex, forcing their genuine
nonparallel concurrence into K. Thus the components have opposite
signs or one is zero. Properness then places q_y between the actual
port heights. The positive-ray point rM has opposite weak transverse
sign, so the own transverse interval contains zero. Each nonzero
transverse normal component has the sign of its actual endpoint height.

The zero origin moment follows directly from concurrence at -tM.
It makes k=M_y/M_x a positive weighted mean of y_i/A. The actual
normal slope is the displayed convex combination of y_i/A and k.
For an upper endpoint it is at most y_i/A; for a lower endpoint it is
at least y_i/A. Multiplication by the corresponding signed transverse
normal gives in both cases

    y_i(n_i)_y >= A (n_i)_y^2/(n_i)_x.

For an axis normal both sides vanish. Therefore h_i>=A/(n_i)_x.
The universal contained-neighbor support bound h_i<=d<61/60 gives
(n_i)_x>60/61 and |(n_i)_y|<11/61. This covers all owned side means,
their endpoints and strict vertices; no mean is replaced by a midpoint.

## 3. Both actual neighbor centers lie in a set of diameter less than one

Every neighbor has halfwidth at least 1/2, hence c_i.n_i>3/2, while
|c_i|<91/60. Its transverse coordinate relative to n_i is less than
sqrt(181)/60<27/120 in magnitude. The normal bounds give

    (c_i)_x > (3/2)(60/61)-(11/61)(27/120)=3501/2440=L.

Both original centers lie in the same rectangle
L<x<91/60, |y|<sqrt((91/60)^2-L^2). Its squared diameter is exactly

    52124381/53582400=1-1458019/53582400<1.

The two distinct physical unit incircles require center distance at
least one, a contradiction. There is no load, orientation, degree or
boundary-touching hypothesis on these two neighbors in this argument.

## 4. Exact verification and limits

Independent Fraction arithmetic verified 1-(60/61)^2=121/3721,
(91/60)^2-9/4=181/3600, the reserve 1/2880 for the transverse rational
bound, the exact horizontal threshold L, and both the displayed
rectangle diameter and its strict reserve. This is arithmetic checking
of a continuous proof, not a sampled cover or numerical certificate.

A root with one improper port is not excluded. Nor can a ray theorem
for G_K+M, with a possible root circle force G_K, be applied to M alone
without proving G_K=0. No whole graph/load gate or coarse cell is closed
here. No force, body, actual mask or side mean is discarded. No Lean
compilation, CI or shared-ledger mutation was performed.
