# Independent full review: the four-force fan incoming-side radius obstruction

Date: October 29, 2026 UTC. Reviewer: tc_finish_v2, independently of
the author fan_finish_v2.

**Verdict: PASS at the complete stated local scope.** The target is a
whole four-force theorem, including the incoming zero-height mean,
the bottom-side mean endpoint and equality in the incoming radius
bound. No neighbor equation or circle load at X or A is needed.

## 1. Exact complete target

I read and independently audited the entire 322-line manuscript

    FOUR_FORCE_FAN_INCOMING_SIDE_RADIUS_BOUND_EXCLUSION.md
    SHA256 4367a648c322df3da5a5ab2137b26e94bfa45a04a032b8f3ab65f182cd431523.

The exact target and all six direct source pins were checked after
the mathematical audit. No frozen source was changed.

The actual unloaded H retains precisely its four original positive
neighbors X,A,B,C. Their actual degrees and other forces are arbitrary.
Only B,C must physically touch the circle, and AB,BC need only be
physical contacts. The full input is

    R^2=(2+epsilon)^2+1/4<=1105/256, 0<=epsilon<1/60,
    H=[h-1,h] times [g-1,g], |h|<=epsilon, g>4/7,
    P_HX=(h,-L), F_HX=lambda East, lambda>0, L>=0,
    (1+h)^2+L^2<=d^2, d=1+epsilon,
    F_HA=(U,V), U>=0,V>0,
    P_HA=(h-1+tau,g), 0<=tau<=1, tau=1 if U>0,
    det(P_HC,F_HC)<0.

The original HX mean is on H's actual right side, all applications
and original forces are unchanged, and the entire original mask and
coefficient data remain. I checked the proof at this full scope,
without supplying extra leaf, load, degree or mean hypotheses.

## 2. Complete direct sources and verified pins

All six complete direct sources were read during this continuation.
Their exact operative scopes, including the force-free portions of
the support and barrier inputs, were checked against this new caller.

| Source | SHA256 | Operative use audited |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full unchanged H4 equations, actual original supporting normals and means |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual HAB/HBC own-axis implications, arbitrary neighboring degrees |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md | 20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf | Only sharp physical support and opposite-vertex geometry |
| HIGH_VERTICAL_STRIP_AND_NEAR_EAST_UNIT_CENTER_EXCLUSION.md | 75def83e3a67168eb28014641ddfa3d53372028514facaab09529903ba6090f8 | Complete two-unit high-support/nearby-normal exclusion |
| HIGH_SQUARE_LOW_LEFT_PORT_BARRIER_WITH_SIGNED_SMALL_SUPPORT.md | e2463dea33c2e66b97046c5727562be354e09f3f065e3dc04028e3a79a79dc58 | Section 2 whole-unit transverse cap, including every physical mask |
| HIGH_SQUARE_CHORD_BARRIER_WITH_EXACT_LOW_PORT_CAP.md | 4e04f9fd6e9b3bae2206333817744ae0f3e624819eb6ffd125929b973782b18e | Complete actual two-point B/H barrier and its top-left endpoint |

The high-strip input's physical center bound is checked against the
current direct support source at 20a845...; no assertion of equality
between historical file hashes is needed. No loaded-tip force
equation from the support source is imported.

## 3. Complete HA/HB/HC geometry and support bounds

Putting c=1-g, original HX membership gives 0<=L<=c<3/7. This
retains L=0 and g=1 at entry. Every point of physical boundary B,C
has squared norm at least (R-sqrt(2))^2>419/1000.

If HA is North, the actual HAB own-axis triangle gives HB_y>=0.
If HA is strict NE, the complete HB feature cover has West and
South removed by their own-axis dot products, strict SW removed
by opposite-vertex geometry, and strict SE removed because its
actual point (h,g-1) has squared norm below

    1/3600+9/49<419/1000.

Thus HB_y>=0 in either complete HA feature. The full H4 vertical
equation then gives HC_y<0, with the strictly positive HA term
retained. The South HC side mean has x>0 by the actual negative
moment, hence 0<x<=h<=epsilon and the same annular contradiction.
Strict SE has that contradiction as well. HC must be strict SW,
at the actual bottom-left H corner F=(-A0,-c), A0=1-h.

For its slope k>0 the original moment gives k<c/A0 and c>0.
The actual contained C support satisfies

    (A0+c*k)/sqrt(1+k^2)>A0*sqrt(1+k^2),
    (A0+c*k)/sqrt(1+k^2)<=d.

At epsilon=0 this is already impossible, since h=0 and A0=d=1.
Otherwise it gives k^2<4 epsilon/(1-epsilon)^2<16/225. No mask
or circle coefficient was selected to obtain k<4/15.

The whole-unit cap is applied in C's actual support frame and to
every actual C point. Its literal support is at least 1-epsilon.
The resulting bounds

    C_y<49/75,
    C_x<-6397/9000<h

include the actual BC point and every possible aggregate mean.
The last inequality holds also for negative h because h>-1/60.

## 4. The entire HB slope cover and actual two-unit entries

Given HC strict SW and HB_y>=0, the actual HBC triangle removes
HB East and North by their negative own-axis dot products, and
strict NE by opposite-vertex geometry. HB is West or strict NW.

The West row has B beyond support A0>=1-epsilon and C beyond a
nearby normal with cosine positive and sine <4/15<7/20. These
are the actual full physical hypotheses of the two-unit exclusion
after an orthogonal coordinate change. Every West mean is included.

In the strict-NW row, the original HB point is W=(h-1,g) and
the force is x*(-1,l), x,l>0. Its actual support is at most d.
I checked the endpoint-minimum argument for

    ((59/60)+(4/7)*l)/sqrt(1+l^2)

on the whole interval [1/12,3/2]. Its derivative changes from
positive to negative at most once. Both endpoint bounds exceed
61/60, with the exact positive squared reserves 560711 and 19839.
Thus the original slope lies below 1/12 or above 3/2.

If l<1/12, its actual support exceeds A0, since 2g>A0*l. C's
actual support also exceeds A0. Their normal separation has positive
cosine and sine <l+k<7/20, so the same physical two-unit theorem
applies literally. No center or virtual neighbor is substituted.
The complete surviving slope therefore has l>3/2.

## 5. The exact H4 pivot, with both incoming endpoints retained

Writing HC=y*(-1,-k), the complete H4 balance is

    lambda+U=x+y,
    V+x*l=y*k.

Let delta=c-L>=0. This is the unchanged HX point's height above
H's bottom side. The complete moment about F consists of

    -lambda*delta, tau*V-U, x, 0.

Thus lambda*delta=tau*V-U+x, and elimination using only the same
full force equation gives

    lambda*(delta-k)
      =(tau-1)*V+(k-1)*U+(1-k-l)*x<0.

The first two terms are nonpositive; the third is strictly negative
because x>0,k<4/15,l>3/2. The proof therefore gives
0<=delta<k without dividing by L, delta, U or tau. North HA with
U=0 and every original mean remains, as do L=0 and delta=0.

## 6. Whole-interval radius comparison and exact scalar margins

The actual HC support function
(A0+c*t)/sqrt(1+t^2) increases up to t=c/A0. Since
0<=delta<k<c/A0, its value at delta is at most d. Adding the
incoming bound 1+h<=sqrt(d^2-L^2) gives exactly

    2<=sqrt(d^2-L^2)+d*sqrt(1+delta^2)-delta*(L+delta).

Both radicals are in their real domains; 1+h>0, and the actual
L<=c<3/7<d. Equality in the original incoming bound is allowed.

I independently checked the two estimates used on the entire stated
intervals. The first follows from sqrt(1-t)<=1-t/2-t^2/8 and
d^3<5/4. For the second, the exact positive remainder after 1+t/2
is t^2/[2*(1+sqrt(1+t))^2]; its denominator is below 10 for
t=delta^2<16/225, while d>=1. Hence

    sqrt(d^2-L^2)<=d-L^2/(2*d)-L^4/10,
    d*sqrt(1+delta^2)<=d+d*delta^2/2-delta^4/10.

Rearrangement, with c=L+delta, gives

    c^2<=4 epsilon+(epsilon/d)L^2+epsilon delta^2
                     -(L^4+delta^4)/5.

Using epsilon/d<=epsilon and completing the square separately in
L^2 and delta^2 gives

    c^2<=4 epsilon+(5/2)epsilon^2
        <97/1440<169/2500.

All signs and constants agree. Thus c<13/50 and g>37/50. No
positive parameter endpoint was assumed to justify this deduction.

## 7. The actual final chord and scope of PASS

The unchanged actual B contains both its original HB corner W and
an actual BC contact point. The latter belongs to the same actual C,
so its x coordinate is <h and its y coordinate is <49/75. Together
with g>37/50>69/100, h<=epsilon and W=(h-1,g), these are the
complete literal exact-low-port barrier hypotheses. Its horizontal
and vertical W endpoints are expressly included. The contradiction
therefore concerns the original B, not a constructed chord or port.

The theorem is valid for the entire stated H4 scope. Neighbor
equations, leaf structure and circle boundary status of X,A are
unneeded; B,C require physical boundary status only. Every actual
side mean, physical mask and individual circle-weight endpoint is
retained. I found no false degree reduction, omitted force, changed
mean, unsupported moment transfer or gap at a zero-height endpoint.

This review proves no whole original family closure. A later caller
must establish each actual rectangle, radius inequality, HA feature
and strict HC moment independently from its own original data.
No metadata, count, certificate status or publication state was
changed. No Lean, Lake, CI, numerical geometric search, staging,
commit or remote action was performed.
