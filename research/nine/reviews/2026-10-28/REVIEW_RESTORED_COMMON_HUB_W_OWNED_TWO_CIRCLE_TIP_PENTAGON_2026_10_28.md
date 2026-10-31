# Fresh independent review of the restored W-owned two-circle-tip exclusion

Date: October 28, 2026 UTC. Reviewer: pentagon continuation.

## Decision and frozen source scope

**PASS for the complete local physical two-circle V mask and the
literal stated common-axis caller.** This is a fresh complete review
of the restored bytes, not an exact-byte recovery of the lost review
f8207756772322abfd5fbffe349a7f9520ed3044432338a6b27fc71a92194b4e.

| Source read in full | Exact SHA-256 |
| --- | --- |
| COMMON_HUB_FACE_W_OWNED_TWO_CIRCLE_TIP_EXCLUSION.md | b28c1dac6d90f960dc0415818a9e883ed95dd60768749bae10a5e4f60dca5365 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 |
| SAME_HUB_FACE_BOUNDARY_TRIANGLE_TIP_RETURN_OWNER_NORMAL_FORM.md | 5f70175b10e068bdaddcd135fdf0cf70ad48d5f256d4ca18b86e616cc3fd7eb6 |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |

I checked the full main proof and the complete operative hypotheses
of those direct inputs. The owner normal form is used only to supply
the actual selected singleton in the original caller. The local
theorem assumes that actual singleton explicitly and requires no
normal selection or equation at U or W.

The accepted domain is precisely 2<R<=sqrt(1105)/16, the actual
common own-U-axis feature, true loaded V2, physical boundary W,
a>=-1/2 and t>=0 in the stated lower-W chart. Every W frame,
original UW mean and physical circle mask is retained.

## 1. The actual W-owned chart is exhaustive

The triangle side-normal theorem applies at W to its owned outward
axis toward V and its actual outward normal West toward U. The
nonnegative dot product is exactly the claimed nonnegative East
component of the original V-to-W normal.

For nonparallel W, this leaves its two inward axes f and g.
The f choice has its minimum side entirely below P and at
x<=a+1. The vertices maximizing f on V are the upper vertex
or the right vertex, respectively above P or strictly right of
a+1. In a tie, the maximizing V face is a whole side. A V
endpoint in the relative interior of a W side on the same support
line would then create positive shared length, contradicting the
literal singleton premise. Thus the tie supplies no additional
singleton feature.

For aligned W, the candidates with nonnegative East component are
East, North and South. The first two are excluded by the actual
minimum-x line and by the vertical order, leaving South, exactly
the r=0 instance of g.

In the g case, the V-own components are (eta,-gamma).
The same singleton/side-interior reasoning excludes gamma=0.
If gamma<0, V's maximizing vertex is its right vertex at
x>a+1, beyond the actual W support side. Thus gamma>0 and the
actual VW vertex is M=P+e1.

The equations for alpha, delta and P_W are actual side coordinates,
not force-dependent replacements. For aligned W the original UW
mean is at or below its upper-left corner P_W. The same actual U
side contains that mean and P above it, hence also P_W. This
legitimizes delta<=1 without moving the original mean in any
equilibrium equation.

From delta=s+cr<=1 one obtains r<=c/(1+s). The side-interior
condition alpha<1 gives r<s/c. These imply r<1/sqrt(2)<d.
Also alpha>r, so the exact identity
alpha^2+kappa^2=1+r^2 gives 0<kappa<1. The aligned endpoint
r=0 is included and causes no loss of strictness in the needed
bounds.

I checked all rotation identities in Section 2, including

    alpha=gamma+r*eta, kappa=eta-r*gamma,
    gamma^2+eta^2=1, tau<=1-gamma.

Their signs and equality endpoint r=0 are used correctly.

## 2. Full two-circle geometry and unchanged force weighting

The weak guards a>=-1/2,t>=0 imply B>=-s/2>-1/2.
A unit at radius R>2 cannot have all four corners on the circle;
a physical two-corner mask therefore has exactly one zero own
center coordinate. Because B+1/2>0, that coordinate must be
A+1/2. The other coordinate is positive, and the circle equation
gives A=-1/2, B=d. This is the complete physical two-corner
alternative under the stated guards.

The two original pair lines intersect at q=P+l East. Its own
coordinates are exactly

    (-1/2+gamma*alpha, d+gamma*kappa).

The inequalities 0<lc<1 and 0<ls<1 place q in the actual open
interior of V. This conclusion was derived directly from the
chart; no unique-circle properness lemma was imported.

Both physical circle corners are retained in the normalized resultant

    F=(xi,d+1), -1/2<=xi<=1/2.

The full original force and torque equations make q parallel to F.
Their positive second coordinates give the positive scale
lambda=(d+gamma*kappa)/(d+1), and kappa<1 gives lambda<1.
The bound xi>=-1/2 then gives exactly

    gamma*(2*(d+1)*alpha+kappa)>=1.

Thus the necessary inequality covers the entire closed coefficient
interval, including either individual zero corner weight.

## 3. Every W mask is accounted for before using its circle equality

The actual W-center f coordinate is

    (1-gamma)/2+(d-r)*eta>0.

Therefore its minimum-f corners are strictly closer to the origin
than their corresponding maximum-f corners. Only the top and right
maximum-f corners can be physical circle corners.

The top corner's squared-radius excess is

    tau^2+tau*gamma+2d*tau*eta-2d-1.

This increases in tau>=0. At the permitted upper bound 1-gamma,
it equals -gamma+2d*((1-gamma)eta-1), which is strictly
negative. Thus the top corner is strictly inside the disk, as are
both minimum-f corners. W's actual physical boundary status forces
its unique right corner to lie on the circle.

Expanding that actual corner gives exactly

    2d*(1+gamma-tau*eta)=tau^2+tau*gamma+eta.

The denominator is positive since tau,eta<1 and gamma>0.
No W force equation or selected corner coefficient is used. This
fully covers aligned W, every initially possible W mask and all
original UW means.

## 4. Continuous scalar contradiction and its strict endpoints

At fixed gamma,eta, the last ratio increases in tau because its
derivative numerator is

    (2tau+gamma)*(1+gamma-tau*eta)
       +eta*(tau^2+tau*gamma+eta)>0.

The resulting upper bound D0(gamma) is strictly decreasing on
0<gamma<1: its numerator decreases and its positive denominator
increases. It is also increasing in the radical when gamma is fixed.
The exact radical comparison at gamma=39/100 and the printed
fraction 76550/82819 therefore prove gamma<39/100 from
d>187/200. I verified the stated positive reserve
177153/16563800.

The full-resultant inequality and the strict bounds d<61/60 and
kappa<1 imply the strict upper bound tau<T(gamma). Since
alpha<1, they first force gamma>30/151. Thus all actual
parameters lie in the proved interval; no lower cutoff is assumed.

On the enlarged closed interval
I=[30/151,39/100], the comparison T is nonnegative, increases,
and is below 5/8. The inequality eta<=1-gamma^2/2 has the
correct direction. The expression derived from the strict lower
radius bound is increasing in both tau and eta. Consequently
the actual data would require the enlarged scalar G(gamma)>0.

I independently differentiated G. The result matches Section 5.3:

    G'=A0/gamma^2*(2T+gamma+Dv)
           +T-D-gamma*(1+DT).

The discarded terms in the source's lower bound are nonnegative
over the entire interval. Lower-bounding the positive first term
and upper-bounding the final negative product give the uniform
strict reserve

    G'>8977019/89232000>0.

Its maximum is therefore its upper endpoint. Exact substitution gives

    G(39/100)=-19954435473/4948658000000<0.

This contradicts the necessary G>0 throughout the whole interval.
Both enlarged interval endpoints are included. The original radius
endpoint R=sqrt(Q), chart guards a=-1/2,t=0, and aligned W
are retained: the strict reserves used in the proof still apply.

I recomputed every printed rational identity in the radius and scalar
argument. These arithmetic checks confirm transcription; the uniform
monotonicity proof provides the exclusion.

## 5. Literal D02 entry and degree preservation

For chord02 and load mask01345, the actual assignments are

    U=2, V=1, W=0, T=3,
    boundary path 1,0,5,4,3.

The cycle edges and chord give true degrees U3,V2,W3,5_2,4_2,T2.
Both V and W are physically boundary. The accepted owner normal
form supplies the actual nonparallel-V/W-owned singleton after the
complete parallel shared feature is handled separately.

The actual occupied path order, with W below the V port, makes the
occupied U arc run clockwise through the lower part of U. Applying
the boundary-path endpoint moment signs to the unchanged East V
normal and West T normal gives t>0 and h>0. The West T direction
itself follows from full U3 force balance; its original mean remains
in full U3 torque balance.

For clarity, the support bound used to get a>=1-d needs no special
mask at T. Every contained unit with center z has farthest-corner
squared norm at least |z|^2+|z|+1/2, so |z|<=d+1/2.
A minimum-West support 1-a gives center West projection at least
1-a+1/2, because the directional unit width is at least one.
Therefore 1-a<=d. It follows that a>=1-d>-1/60, which is
stronger than the local guard.

Thus the local theorem applies to the entire original physical
two-circle V subdomain. Every T mask, actual UW mean, other true
force and all three arbitrary completion units remain. The same
literal entry is valid for the additional boundary-path component
scope explicitly stated in the source.

## 6. Accounting boundary

The unique-opposite and unique-adjacent V masks are not premises of
this proof. In particular the separately published opposite-circle
source is a comparison, not an operative dependency of the local
argument.

This PASS certifies the complete two-physical-circle V feature and
its stated callers. It supplies no whole D02 row or coarse-gate
closure. No Lean compilation, CI, numerical pose sample, angle mesh,
normal reselection, changed mean or deleted force was used.

