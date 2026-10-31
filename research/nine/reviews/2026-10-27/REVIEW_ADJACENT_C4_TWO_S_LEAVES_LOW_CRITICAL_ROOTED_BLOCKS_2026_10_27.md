# Independent review: adjacent C4 S leaves through the critical radius

Date: October 27, 2026.

Reviewer: rooted-blocks agent, independently of the author and root reviewer.

**Verdict: ACCEPTED for the entire stated strict-low and critical domain.**
No correction or additional hypothesis is required. This review does not
close the high-radius portion of the original fine gate.

Reviewed complete source:

    ADJACENT_TWO_S_LEAF_C4_LOW_AND_CRITICAL_EXCLUSION.md
    SHA-256 23c11c22e3eaa21ba542fea0af320f485210edb18882c2733b4ce90222a8212c

The exact original caller is

    M6.B4L2.C4.ADJACENT.LCD.SS, with d<=1.

The cycle remains A--B--C--D--A, with genuine S leaves at A and B,
true degrees A3,B3,C2,D2,L1,M1, and positive total circle loads at
both C and D. All nine original physical units remain.

## 1. Strict-low geometry

I checked the complete origin-containment reduction. At d<1 a tilted
genuine S root contains O openly; an aligned root fails to contain O
openly only when zero is a transverse endpoint. Since the other root
contains O closed, neither root can have O in its interior. Their
occupied tangent half-planes at O are opposite, and the two genuine
leaf axes are therefore parallel. Equal directions would repeat the
same actual radial S leaf. The normalized staggered pair in Section 1
is consequently exhaustive.

The original A3 and B3 force equations, including both genuine leaf
forces, make AD strictly northwest and BC strictly southeast. Their
actual ports are the displayed opposite upper and lower vertices.
The support-point span bound used here is physical and degree-free:
at a minimum-n vertex with n_y>0, at most one inward orthogonal side
can point downward, and its downward component is at most |n_x|;
at a side point the downward tangent distance is at most the same
quantity. Endpoints remain covered. Thus D lies strictly above y=0
and C strictly below y=0. Their actual edge CD is impossible.

## 2. Critical moment and frame cover

I reread FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md, Lemma 1.1. Its boundary
edge moment is nonzero for any actual contact mean and compatible
physical separating normal. It imposes no degree-two hypothesis on
the pair. In this caller the original C2/D2 torques and the zero
origin moments of the two real radial leaves transport that nonzero
moment through all four cycle edges. In particular the original AB
mean is not O.

The two roots contain both O and that nonzero mean. Their actual
intersection therefore has positive length along a common side line
through O; their frames agree and their actual AB normal is its own
perpendicular axis. The leaf-axis cover retains every endpoint:
equal tangential directions repeat the leaf, while opposite tangential
directions allow only the point O in common. The only remaining
possibilities are opposite inward normal directions and one inward
normal together with one tangential direction toward the nonzero mean.

## 3. Opposite normal directions

The two full root equations force the other cycle normals to be
horizontal. The outward alternative would be at support d=1 and
would identify the neighbor with the original genuine S leaf by the
sharp contained-unit support equality. Thus C and D occupy opposite
closed half-planes through O.

Their actual circle points have strictly opposite horizontal signs.
A circle corner cannot lie on the zero-coordinate support line:
its inward radial direction enters the open square, whereas here
that direction would remain in the line. Hence their positive total
circle resultants have strictly opposite horizontal signs. Full
component balance makes the vertical components opposite, giving a
strictly negative dot product. ACUTE_LOADED_CONTACT_GRAPH.md,
Sections 1--2, gives a strictly positive dot product for the touching
boundary pair. I checked this directly for nonnegative individual
corner weights, including zeros. No artificial two-force root is used.

## 4. Perpendicular directions and all C contact features

The exact A torque is mu*s+nu*y=0, with s>0. Since the actual AD
point belongs to boundary D, |y|>=r. This gives the complete endpoint
bound 0<s<=h<=1-r<1/2. After the quarter-turn change of coordinates,
the full B3 force and torque give a/b=s at its actual BC port (0,1).

I reread TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1. Its
positive proper concurrence applies exactly to C2 because D is a
physical boundary neighbor; it does not require B to be degree two
or boundary. In the present orientation it gives q_C=P+t*n, t>=0,
and positive radial proportionality to the actual full C resultant.

If P is a C vertex, both adjacent corners have norm at most 2<R.
The only possible circle corner is the opposite one, with
Z_y=13/8 and |Z_x|=sqrt(103)/8. Its coordinate ratio exceeds 1/2,
whereas positive proper concurrence makes that ratio strictly less
than a/b=s<1/2. This includes the contact at an endpoint of a side.

For the remaining relative side interior, the full frame
P+[0,1]n+[-rho,1-rho]k retains 0<rho<1. The positive normal support
places all circle corners on the far normal side. Two such corners
would force b=1,a=0, so there is exactly one. Its tangent sign is
negative by the unchanged concurrence, making it the actual negative
endpoint. Positive radial proportionality also gives rho<=a/b=s.
The displayed norm expansion then gives exactly

    R^2<=2+s^2+2/b=(1+sqrt(1+s^2))^2.

I checked the final strict radical comparison:

    (R-1)^2-1-(1-r)^2=2*sqrt(2)*(R-1)-3>0,
    17/4-(1+3*sqrt(2)/4)^2=(17-12*sqrt(2))/8>0.

The last sign follows from 289>288. All quantities squared are
positive. Thus the weak endpoint inequalities produce a strict
contradiction throughout the critical domain.

## 5. Scope

The proof covers all original means and physical circle masks at
d<=1, with the genuine higher-degree A3/B3 equations unchanged.
It does not export its critical loaded-pair argument to a single-load
cycle, and does not claim LCD.SS at d>1 or any mixed S/D gate.
No numerical pose, force deletion, new normal selection, Lean
compilation, CI run, remote write or shared-metadata change was used
for this review.
