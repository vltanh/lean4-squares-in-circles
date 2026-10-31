# Independent review of the both-adjacent one-radial C6 classification

Date: October 26, 2026.

**Result: PASS for the complete stated both-adjacent physical subfamily,
including its original three-slider completion join.** Reviewed source:
SIX_CYCLE_ONE_RADIAL_BOTH_ADJACENT_PORTS_CLASSIFICATION.md. This review
does not infer the full unrestricted one-radial C6 gate.

## 1. Original geometric features and direction selections

I read the complete source, the actual-channel and endpoint-center
conclusions of SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md, the local
strict-turn consequence in SIX_CYCLE_RADIAL_INCIDENT_NEAR_CORNER_ANGLE_BOUND.md,
the full shared-mean chart of SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md,
and the physical feature cover of
SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md.

The source correctly restricts the latter to its local feature consequence
after both unique turns have been independently proved strict. It does
not import the three-unique global turn proof into a one-radial component.
The two actual S-incident adjacent vertices have distance one from their
unique circle corners, supplying precisely the local near-corner premise.

The mean chart verifies that an adjacent port forces the other port to
be the opposite vertex and the chord to have length one. A genuine share
can only be the S-incident interface; its unchanged endpoint mean makes
its turn 135 degrees. Thus the B-to-C channel has the asserted two strict
opposite-vertex applications, without relabeling a genuine shared mean
as a singleton or moving an application.

On making this channel horizontal with its outer side above the origin,
the proper force triangle supplies H>0. The actual endpoint-center theorem
gives the negative left endpoint center coordinate, and the corresponding
opposite-to-circle corner lies still farther left. Proper concurrence
gives Z>=H and hence eta>=pi/4. The third concurrence is below this
horizontal edge, so the S-incident actual port is its lower adjacent
vertex. Equality of that port with its concurrence would make the unique
circle corner parallel to one own axis, contradicting its two strictly
positive own coordinates. These are actual force-direction deductions.

I reconstructed the unchanged ports and normal as

    T=(-A+C,H), Q=(-A+c,H-c),
    q=(1-t)z, V=q-Q=(tA-c,c), G=V/|V|, P=Q-G.

The reflected endpoint obeys the same formulas with the same R,H. Their
real reserve-one opposite-corner channel gives
(A_B-C_B)+(A_C-C_C)=1. Since each other summand is <R-1,
the two actual endpoint bounds A_i-C_i>2-R>-5/64 follow.

## 2. Properness and connected comparison domain

The proper opposite-port distance is lambda=C-tA. If it vanished,
the two outward normals at that unique square would be rightward and
(-s,-c); their smaller angle is at least 135 degrees, giving turn at
most 45 degrees, contrary to the strict-turn premise. Thus lambda>0.

I independently checked

    a-b=CZ-DA=Z lambda,
    x=1-ta=c lambda>0,
    L^2=x^2+t^2 b^2.

For fixed R,H, positivity of lambda is equivalent to
H>D(R/sqrt(2)-1), by squaring CZ>DA with positive quantities.
It persists on the whole interval between the two actual angles.
On this proper domain (A-C)'=D-ZC/A<0. Also

    a'=-b(1-C/A), b'=a(1-C/A).

Here a=cA+sZ>0 throughout independently of any interpolation claim.
Thus b first increases and then decreases, so its minimum occurs at
an actual endpoint. The endpoint physical uniqueness b>1/2 therefore
persists throughout. These checks validate the full comparison interval;
no interpolated configuration is assumed physically realizable.

## 3. Independent reconstruction of the scalar derivative

Let r=R^2 remain fixed and put

    L^2=1-2ta+t^2 r,
    J=(1+t)a-tr-1,
    F=r+2-2a-2J/L.

Direct independent partial differentiation gives

    (L^3/2) F_a = -[L^3+(1+t)L^2+tJ]
                = -[L^3+1-t(1+t)a+t^3 r],
    (L^3/2) F_t = (1-t)(r-a^2).

The second identity follows by expanding
-(a-r)L^2-J(a-tr)=(1-t)(r-a^2).
Since r-a^2=b^2 and a'=-b(1-C/A), these reproduce exactly

    F'=(2b/L^3)[(1-C/A) Ccal+t'(1-t)b],
    Ccal=L^3+tL^2+(1-t)(1-ta),
    t'=HC/Z^2.

All divisions are by strictly positive A,Z,L. This verifies the source's
derivative identity algebraically, without numerical differentiation.

## 4. Complete derivative sign and fixed rational bounds

The actual radial-port norm excludes c<=1/4: its exact bounds give
m=tA>413/1200>1/3, then G_x>3/10 and -P_x>75/64,
whereas |P|<23/20. Since cosine is decreasing, c>=1/4 then
holds on the whole comparison interval.

If A>=C the derivative is immediately positive. For A<C, I checked
the concavity argument in b: both endpoints of
c sqrt(R^2-b^2)+sb exceed C when c>=1/2. Hence only
1/4<=c<1/2 requires estimates. On this entire range the stated
bounds D<23/32, C>6/5, t<7/15 and Z<7/4 are valid.

The estimates for L retain every sign. In particular

    m^2<(1-2c^2)^2/2<=1/2-3c^2/2,
    m>413/2660>1/8>=c/4

give L^2=(m-c)^2+c^2<1/2. Using 0<x<=L and L<1
then gives Ccal<=L^3+L<15/14. The possible negative derivative
term is strictly above -75/826, whereas its positive term exceeds
256/2625. I independently reproduced the exact displayed reserves:

| Comparison | Exact positive difference |
| --- | --- |
| (133/64)^2 minus 1105/256 | 9/4096 |
| (23/20)^2 minus 4621/3600 | 7/180 |
| 75/64 minus 23/20 | 7/320 |
| (7/15)^2 minus the extremal t-ratio bound | 18848/4641075 |
| (7/4)^2 minus [(133/64)^2-(359/320)^2] | 1/400 |
| 256/2625 minus 75/826 | 2083/309750 |

These are fixed arithmetic consequences of the displayed inequalities,
not a sampled angular sign grid. The resulting F'>0 is strict over
the entire connected comparison domain.

## 5. Reflection, right turn, and the original completion theorem

The two real ports on the radial square have the same squared norm
d^2+1/4. Strict monotonicity at fixed R,H therefore forces equality
of the two endpoint angles. The exact reserve gives A=C+1/2,
and their reflected ports are (-x,y),(x,y) with
x=s+1/2+G_x>0. Their actual unit separation forces G_x=-s;
since G_y=c/L>0, the unit normal then has G_y=c and L=1.
Consequently tA=-D, forcing t=D=0 and eta=pi/4.

The two unique concurrences are then their actual circle corners and
their turns are 135 degrees. Their turn sum makes the radial turn a
right angle, contradicting precisely the strict branch under study.
No assumption that the radial concurrence lies in its square occurs.

I read the complete equality classification premise in
SIX_CYCLE_ONE_RADIAL_RIGHT_TURN_CLASSIFICATION.md and the retained
full slider domain and capacity theorem in
SIX_CYCLE_ONE_RADIAL_RIGHT_ANGLE_FAMILY_COMPLETION.md. Those sources
apply at exactly this right-turn endpoint, retaining both original
radial corner weights and all three actual transmitter sliders. Their
total extra capacity at most two excludes the three actual extras.

The new theorem has the advertised entire both-adjacent scope, including
genuine shared means already equal to the specified vertices. Opposite
or nonendpoint S-incident ports remain outside it. No full one-radial
roadmap gate or unrestricted equality claim is certified here. No Lean
compilation, CI or numerical pose premise was used.
