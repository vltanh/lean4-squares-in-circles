# Independent complete review of opposite supports without side ownership

Date: October 28, 2026. Reviewer: recovery_audit.

**Verdict: PASS, complete for the entire stated general physical domain.**
I read the whole new source and independently rederived its full endpoint
feature cover, all physical-circle-mask implications, actual angular
lift, and continuous support-span inequality. No source correction was
needed. This is a fresh review of the exact new bytes.

Reviewed source:

    SHORT_BOUNDARY_PATH_OPPOSITE_SUPPORTS_WITHOUT_SIDE_OWNERSHIP.md
    bytes: 7430
    SHA-256: 699995c7434d2b448c16831f874bc2b36a2df356532bbd1c085cc8c15c9b96d9
    Git blob: e1ab7db4be53b706cee719b0f10529b50664c2e9

The theorem is force-free and applies for every R>=2, with no upper
radius bound or degree assumption. Neither endpoint support normal is
required to be an axis of its actual square. It changes no original
fine/coarse ID, gate, metadata, source or force system.

## 1. Actual statement and complete endpoint frame cover

The original path consists of two through four actual boundary units
with pairwise disjoint open interiors and consecutive physical contacts.
Its center directions have an explicitly assumed counterclockwise
increasing lift, total advance below 2pi, with each step below pi.
That real geometric order remains a caller obligation.

The actual left and right support points are (-X_L,h_L) and (X_K,h_K),
with X_i>-1/2, h_i>=0, outward opposite parallel support half-planes,
and X_L+X_K<=1. The heights need not be equal. The endpoint resultants
are arbitrary nonzero nonnegative combinations of their own actual
physical circle corners, with nonnegative vertical components.

For the right endpoint, a genuinely tilted square's minimum-East face
is a unique vertex. Every such frame can be written exactly

    K=P+[0,1](c,s)+[0,1](s,-c),
    P=(X,h), c,s>0, c^2+s^2=1.

The two inward axes have positive horizontal components and opposite
vertical signs; choosing the upward one first gives this form without
an omitted tilt interval. Axis endpoints are handled by the separate
aligned case, not by division through a vanishing component.

## 2. Entire negative-center-height physical mask implication

Suppose the tilted center height h+(s-c)/2 is negative. Then c>s and
0<=h<(c-s)/2. The lower adjacent corner has height h-c<-(c+s)/2<0;
the opposite corner has height h+s-c<-(c-s)/2<0.

The upper adjacent corner has larger squared norm than P:

    |P+(c,s)|^2-|P|^2=1+2Xc+2hs>0.

For X>=0 the positivity is direct. For -1/2<X<0 its value exceeds
1-c>=0. Thus this comparison includes the entire permitted negative-X
range and h=0.

I independently expanded the second strict comparison:

    |P+(c+s,s-c)|^2-|P+(c,s)|^2
      =1+2Xs-2hc
      >1+2Xs-c(c-s)
       =s(2X+s+c)>0.

The final sign uses s>0, 2X>-1 and s+c>1 for a genuine tilt.
Therefore neither nonnegative-height corner P or P+(c,s) can be a
farthest corner. Every possible physical circle corner is one of the
two strictly negative-height corners. Since the unit is contained in
the disk and touches its circle, its physical circle corners are
exactly among its farthest corners. Any nonzero nonnegative combination
of them has strictly negative vertical component, contradicting the
stated full-resultant sign.

This treats a unique physical circle corner and a tie between the
two remaining farthest corners equally. Either individual coefficient
may vanish; no positive coefficient is presumed at every physical
corner.

For an aligned square K=[X,X+1]x[B,B+1], X>-1/2 makes the far
normal side x=X+1. If its center height B+1/2 is negative, its
unique farthest tangent coordinate is B<0. All physical circle corners
again have negative height. The original support point can be anywhere
on the entire real minimum-East side, including either endpoint; no
point or mean is replaced to obtain this conclusion.

Thus in both complete frame cases the endpoint resultant sign forces
actual center height at least zero. Its horizontal coordinate is
X+w/2>0 because the real horizontal width w is at least one.
Reflecting the left endpoint across the vertical axis preserves its
height, physical masks and resultant sign, and gives negative actual
horizontal center coordinate there.

## 3. All actual path-angle and zero-height endpoints

The actual endpoint angles therefore have representatives

    alpha_L=pi-delta_L, alpha_K=delta_K,
    0<=delta_L,delta_K<pi/2.

Center height zero is retained, including both delta values zero.
Every boundary center has radius at least R-1/sqrt(2)>5/4. A contact
gives center distance at most sqrt(2). The cosine law consequently
gives each minor contact angle less than theta=acos(9/25). This
strict inequality also holds when the numerator
distance^2-(r-r')^2 is nonpositive.

The assumed original counterclockwise lift has exactly endpoint
advance pi+delta_L+delta_K. Indeed the direct representative
difference delta_K-(pi-delta_L) lies in [-pi,0), and the unique
positive advance below 2pi is obtained by adding 2pi. Thus no
extra turn or change of path orientation is hidden. With at most
three contacts,

    delta_L+delta_K<alpha=3theta-pi.

Since pi/3<theta<pi/2, one has 0<alpha<pi/2. I checked the exact
triple-angle identity

    cos(alpha)=13959/15625,
    cos(alpha)-89/100=211/62500>0.

For a path with one or two contacts the actual advance, which is at
least pi, already contradicts its upper bound of at most 2theta<pi.
The printed common inequality is valid for the remaining three-contact
case and is sufficient for the subsequent estimate.

## 4. Continuous support-span contradiction without ownership

The original support coordinate is exactly

    X_i=r_i cos(delta_i)-w_i/2,

where the actual horizontal width satisfies 1<=w_i<=sqrt(2).
This identity is valid for tilted vertices and aligned side means;
it does not identify the support normal with an own axis. The
nonnegative cosine and original radius bound give

    X_i>=(R-1/sqrt(2))cos(delta_i)-1/sqrt(2).

For nonnegative x,y with x+y<alpha<pi/2,

    cos(x)+cos(y)>=1+cos(x+y)>1+cos(alpha).

The first inequality follows from the displayed cosine identity and
|x-y|<=x+y. It remains true when either angle vanishes; strictness of
the second comparison comes from the real path bound, even when both
angles are zero. Summing the two unchanged endpoint support inequalities
therefore gives

    X_L+X_K
      >(2-1/sqrt(2))(1+cos(alpha))-sqrt(2)
      >(129/100)(189/100)-71/50
       =10181/10000>1.

Both radical comparisons are strict by squaring:
1/sqrt(2)<71/100 and sqrt(2)<71/50. All factors used in multiplying
the lower bounds are positive. The exact rational reserve above one
is 181/10000. This contradicts the actual support-span hypothesis
throughout the complete continuous domain.

## 5. Exact input relation, acceptance and limits

Every mathematical ingredient of this narrower-span theorem is proved
in its own text. Its single related-source pin matches the current
file:

| Related source | SHA-256 |
| --- | --- |
| FOUR_BOUNDARY_PATH_OWNED_ENDPOINT_TANGENT_SIGN_OBSTRUCTION.md | 5e8cba82367da03c15710cd6060c3a009323413465a78acaf965f4b07ff29536 |

I had also independently reviewed that complete earlier theorem, but
the present approval does not borrow endpoint side ownership from it.
The present source really covers unowned opposite support directions,
different nonnegative endpoint heights and all permitted negative X_i.

A graph caller still must prove the actual path order, both real
support half-planes, their original-circle coordinates, both full
resultant signs and the support span. It cannot remove a true third
force to manufacture a sign. The source correctly claims no original
whole-family closure without those caller obligations.

No actual unit, normal, application, shared mean, physical mask or
individual coefficient was modified. No pose sample, finite numerical
certificate, Lean compilation, CI, metadata edit or remote write was
used in this independent hand review.
