# Independent full review of the near-center centered nine-eighths arc

Date: October 27, 2026.
Reviewer: rooted_blocks, independently of author triangle_bridges.

**Decision: ACCEPTED in full, with no correction requested.**

Reviewed source:

    NEAR_CENTER_UNIT_CENTERED_NINE_EIGHTHS_ARC.md
    SHA256 c3d39e0b3b2104cc9e696a1215ff0d14364b3fe62154d4c94b9818ff5bb51585

The theorem is purely physical. An actual unit E with
dist(O,E)>=1/5 and |c_E|<=5/6 contains in its open interior
the entire closed radius9/8 arc centered on its own center
direction with halfwidth atan(2/5). I independently read and
re-derived the complete coordinate cover, both coordinate
deviations and the single global concavity estimate.

## 1. The nearest-point alternatives are exhaustive

Changing only signs and order of the actual unit axes gives
center(a,b), a>=b>=0. If b>=1/2, the nearest point has
coordinates(A,B)=(a-1/2,b-1/2), both nonnegative.
Clearance gives A^2+B^2>=1/25 and hence A+B>=1/5.
The resulting center norm squared is at least37/50,
which exceeds25/36 by41/900. Thus this full vertex
alternative, including b=1/2, is impossible.

In the remaining b<1/2 case, clearance requires a>=7/10.
It follows that7/10<=r<=5/6 and0<=phi<=pi/4.
The argument does not infer strict clearance or discard an
axis orientation. In particular the center is nonzero.

The exact sine and cosine of alpha=atan(2/5) are correct.
The comparison rho*cos(alpha)>5/6 is strict, including the
center-radius endpoint. Squaring54>8sqrt(29) gives1060>0.

## 2. Both first-coordinate sides have strict reserves

For every actual angle t in[-alpha,alpha], the positive
first-coordinate displacement is at most rho-a<=17/40.
The lower first coordinate is at least
rho*cos(pi/4+alpha)=27/(8sqrt(58))>27/64.
Subtracting from a<=5/6 gives the strict bound79/192.
Both are below1/2, uniformly on the full closed angle
interval. Neither argument relies only on endpoint samples.

## 3. The second-coordinate maximum is controlled globally

The entire angular interval lies within(-pi/2,pi/2), so the
sine is increasing there. The positive deviation is bounded
by

    F(phi)=(9/8)sin(phi+alpha)-(7/10)tan(phi).

The inequality r*sin(phi)>= (7/10)tan(phi) is exactly
a=r*cos(phi)>=7/10, including phi=0.

Direct differentiation gives the stated second derivative.
Both its summands have the required nonpositive sign and
sin(phi+alpha)>=sin(alpha); the exact comparison
9/(4sqrt(29))>2/5 has squared reserve169. Therefore
F''<-2/5 throughout the whole comparison interval.

I recomputed independently

    F(alpha)=719/1450,
    F'(alpha)=77/29000.

The global quadratic Taylor upper bound follows by integrating
the second-derivative inequality on either side of alpha.
Completing that actual quadratic gives

    719/1450+(5/4)(77/29000)^2
      =333621929/672800000
      =1/2-2778071/672800000.

Thus the positive second-coordinate displacement is strictly
below1/2 for every actual angle and orientation.

For the negative deviation, rho*cos(alpha)>r makes the first
term nonpositive in the manuscript's exact identity. The
remaining term is at most9/(4sqrt(29))<9/20<1/2.
This also covers every weak endpoint.

## 4. Exact exported scope

Both actual own coordinates of every point in the closed arc
are strictly between their unit's two side coordinates.
Consequently the closed arc lies in int(E), including both
arc endpoints, clearance equality and center-radius equality.

The halfwidth comparison against pi/9 uses only the accepted
cos(pi/9)>15/16 bound:
tan(pi/9)<sqrt(31)/15<2/5.
It is valid and strict. The source correctly does not claim
that this is E's entire circle intersection or that such an
intersection is connected. A caller requiring connectedness
must separately use the complete dist>1/8 arc theorem.

No circle contact, force, degree, normal selection, pose or
numerical sample entered the proof. This review accepts the
whole literal physical theorem and does not by itself close
an original graph family. No shared metadata, remote state,
compilation or CI was changed.

## 5. Accepted-status readback

The author subsequently changed only the status/review-reference
wording. I read back those changes and the final source hash:

    727deebc984dfbf06dffa9aa2da5532fd9a0f2a7b2b46322fc7da7cc229fdee3.

The mathematical statement, complete coordinate proof and all exact
reserves remain as reviewed above. Full independent acceptance
continues at this final status-only pin.

