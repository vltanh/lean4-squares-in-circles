# Complete independent review: B-owned lower root, oblique return, K-owned central contact

Date: October 27, 2026.  
Reviewer: rooted_final_review.  
Target author: cert_final_review.

## 1. Verdict, exact source and independence boundary

**PASS of the entire unchanged fifteen-section local theorem.**

The frozen target is

`B_OWNED_LOWER_ROOT_OBLIQUE_RETURN_K_CENTRAL_EXCLUSION.md`

with SHA256

`1dcbe8946fbc1b2f0a010a0b49e0e2bdbb1c56e9441246022b5d2feb89c2cbde`,

26,126 bytes, under `recovery_2026_10_27/research/nine`.

I read the entire target, all eight complete present direct sources,
and reconstructed the actual geometry, complete feature union and
force equations before checking the algebra. All source hashes match.
No correction to the frozen target is requested. In particular the
entire original Section 12 continuous comparison passes as written;
this review does not substitute a later shorter argument for that
section.

The theorem has a complete present local dependency bundle. Its
displayed lower-root chart is an explicit hypothesis. Acceptance of
that theorem does not claim that the missing earlier original-family
normal-form and mask-reduction files have been recovered. Section 15
of the target states that boundary accurately.

I did not write the target. I previously authored the northwest-page
source cited only as motivation for its fully reproduced continuous
comparison, and I independently reviewed its free/shared-return helper.
Those facts are disclosed rather than presented as additional outside
independence. During this audit I found a shorter actual-contact gap
argument and sent it to the author. It is not in the frozen target and
is to be preserved in a separate credited addendum. This review covers
the unchanged full source, including the longer original arguments.

## 2. Full local contract and both genuine H leaves

The actual H chart is

    P=(-x,-A), G=1-A,
    H=[-1-x,-x] x [-A,G], 0<=A<31/120.

The radius is unchanged:

    d=1+delta, 0<delta<1/60,
    R^2=(d+1)^2+1/4,
    17/4<R^2<=1105/256, R<25/12.

The genuine vertex H leaf has actual radial application
`(-1-x,-A)` and real equation `(1+x)^2+A^2=d^2`.
The genuine aligned H leaf instead has actual radial mean `(-d,0)`,
direction -E1 and `x=delta`. Its actual side position A is retained.
The vertex equation is not assigned to the aligned row.

In H coordinates, the unchanged B axes are

    e=(beta,-alpha), f=(alpha,beta),
    alpha,beta>0, alpha^2+beta^2=1.

HB is genuinely B-owned and singleton at P. The definitions

    h_B=-beta*x+alpha*A,
    t=alpha*x+beta*A,
    D_0=1-b+t,
    |h_B|<=delta, 0<t<b<31/120, 0<D_0<1

are retained, as is the actual B square
`P+[0,1]e+[D_0-1,D_0]f`. Its genuine radial leaf is
`p_B=(1+h_B)e-bf` with real radius equation
`(1+h_B)^2+b^2=d^2`.

The actual BK singleton is owned by K at `Q=P+D_0 f`, with
actual normal `M=-c_B e+s_B f` and strictly positive c_B,s_B.
The actual HK is also K-owned singleton. C is uniquely physically
circle-touching and positively loaded with exactly HC and CK as pair
forces. H4 and B3 are genuine; K's degree, mask and additional forces
are unrestricted. Every other physical packing square remains present.

The existing compatible fixed-singleton C2 selection is a stated
certificate hypothesis. It is not performed again during the proof or
after choosing a shared-side mean.

## 3. Sections 2--3: actual root signs, B3 and central application

The orthogonal-coordinate identity is

    h_B^2+t^2=x^2+A^2.

Subtracting the two real leaf equations in the vertex H row gives

    (1+beta)x=alpha*A+(b^2-t^2)/2>0.

The aligned row already has x=delta>0. In both rows the appropriate
real equation yields `0<x<=delta`. Hence

    h=-x<0, X=1+x=1-h, 1<X<61/60.

I checked the circle-clear argument for both H and B. The actual
unit inward radial segment from the genuine leaf application belongs
to its root. At a vertex its two inward coordinates are nonnegative
and at most one; at the aligned side it is the true inward normal
segment. Its inner endpoint has norm delta. Thus every point of the
root has norm at most delta+sqrt(2)<2<R. The later B3 and H4 equations
therefore omit no circle force.

The actual radial B leaf line and HB line meet at
`q_B=sigma*p_B`, with `sigma=t/b` strictly between zero and one.
Their lines are nonparallel. The unchanged B3 moment puts the actual
BK line through q_B. Its two actual own-frame differences are

    h_B(1-sigma)-sigma,
    1-b(1-sigma)>0.

Thus the displayed positive normal ratio is exactly

    c_B/s_B=[sigma-h_B(1-sigma)]/[1-b(1-sigma)].

The denominator-minus-numerator is
`(1-sigma)(1+h_B-b)>0`. Consequently c_B<s_B and
`c_B<1/sqrt(2)<17/24`. The force direction was derived from the
original B3 line, not selected independently.

The actual owned BK chart gives every K point f-coordinate strictly
above `1-b-c_B>1/30`. Both lower H vertices have negative
f-coordinate, so neither is the HK application.

If HK were at the upper-left H vertex F, its actual H normal would
be strict northwest and have negative dot product with e. Applying
the complete backward-support span at that real minimum-normal
point of K gives `max_K e.(Z-F)<1`. But F lies alpha+beta>1
below P in e projection. Thus all K would lie below B's minimum
e support, contradicting their actual contact. The only possible
central application is the upper-right H vertex

    R_0=(h,G), N_x>0, N_y>0.

This point is genuinely in the relative interior of K's owned side.
The manuscript's tangent-sector argument excludes every third square
from R_0: K's half-plane and H's strict opposite quadrant leave only
two gaps of angle less than pi/2. In particular C cannot contain R_0.

## 4. Section 4: physical page side and the proper C2 direction

Every physical K circle corner has positive global height. If its
height were nonpositive, the actual point R_0 in K would have squared
distance greater than

    17/4-(25/12)/30>2,

contradicting the unit-square diameter. This uses no K force equation
or unique K mask.

I read all of `S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md`, and checked
that only its complete physical Sections 1--2 are applied here. K and
C are touching boundary neighbors of H, distinct from the genuine H
leaf, so their actual circle corners lie on the same strict side of
that leaf line. Each corner has angular separation greater than pi/9
from the leaf direction. The source's later global force-sum theorem
is not used, which is essential because the present B leaf is also
loaded.

For aligned H and for A=0, the transfer of positive height is immediate.
For the genuine vertex row with A>0, the actual functional is
`Phi(z)=-A*z_x+X*z_y`. A positive-height K circle point with
Phi<=0 would have `z_x>=RX/d>120/61>sqrt(2)`. Since K contains
R_0 with h<0, this contradicts its diameter. Therefore Phi is positive
on K's circle points and on C's circle points by the physical side
transfer. A nonpositive-height C circle point would then lie in the
small angular interval between the negative horizontal direction and
the true leaf direction. The bound
`arctan(A/X)<arctan(31/120)<pi/12<pi/9` contradicts the
same physical corner separation.

C's actual unique circle corner consequently has positive height.
The boundary-neighbor proper-concurrence lemma applies to its genuine
C2 because K physically touches the circle. Its concurrence is a
positive multiple of that corner and is on the proper incoming ray
from the actual HC application. A negative-height HC normal would
start on H's bottom side and have a nonpositive-height proper ray,
which is impossible. Thus every actual HC normal has nonnegative
height.

## 5. Sections 5--6: exhaustive HC cover, actual H4 endpoint and helpers

The physical triangle P,R_0,Q has all three closed sides in H,B,K
and area `alpha*D_0/2<1/2`. Every H-owned E1 singleton or
positive shared HC overlap contains a relative-interior point of its
H side, where C's interior enters that triangle. The open interior of
C cannot meet the closed physical squares H,B,K, and hence cannot
cross the triangle boundary. Connectedness would put the whole unit
C inside an area smaller than one. This rules out the entire E1
physical contact, without modifying its mean.

The -E1 alternative separates C from K by the strict backward-support
span from R_0. A strictly northeast HC uses the forbidden third-body
point R_0. Together with the height conclusion, the full remaining
HC cover is exactly the H-owned E2 top side, or a strict northwest
normal at F, either C-owned or free.

At A=0 in the top row, the actual H4 moment about P is essential.
The genuine leaf and HB have zero moment. The actual central force
at P+E2 contributes `-tau*N_x<0`; a top application
`P+E2-eta*E1` contributes `-omega*eta<=0`. Their sum cannot
vanish. This excludes G=1 before applying the strict G<1 top helper.

The actual central normal and K frame satisfy every premise of
`HIGH_CORNER_CENTRAL_TOP_PAGE_EXCLUSION.md`: h<0,
89/120<G<1, true loaded unique C2, a strict actual central offset,
arbitrary K degree and mask, the physical H-K-C triangle, the existing
fixed-singleton convention, and the complete shared HC mean. I read
that helper in full, including its extra negative K axis, both possible
K circle corners, and the whole actual side position. Its complete
theorem therefore removes the full top HC row.

For the northwest HC row, if CK is singleton its actual C application
cannot be F. Otherwise F belongs to H and K, contrary to their actual
singleton intersection {R_0}. Thus the two actual fixed C applications
are distinct. The already compatible fixed-point selector makes both
singleton page normals side-owned. HC cannot be H-owned in a strict
northwest direction, so it is C-owned. The selector's coincident radial-D
exception is excluded here by the actual different HK point, not by a
generic claim that all applications are distinct.

Any remaining free HC must therefore have physically shared CK.
The actual central K frame always has the form required by
`HIGH_CORNER_FREE_OPPOSITE_PAGE_SHARED_RETURN_EXCLUSION.md`,
independently of which of its axes BK previously used. Its whole
free cone, all shared means, h<0 and the possible G=1 endpoint lie
inside that helper's domain. The full helper excludes this case without
a K force law. I separately completed its full independent review.

The only surviving page is consequently C-owned HC at F. The later
proof covers every CK owner and physical type in this entire page.

## 6. Section 7: signed C circle, genuine aligned surplus and full budget

The actual C-owned chart is

    n_C=(-u,v), t_C=(v,u), u,v>0, u^2+v^2=1,
    C=F+[0,1]n_C+[-lambda,1-lambda]t_C,
    0<lambda<1,
    a=Xu+Gv,
    B_0=Xv-Gu.

The proper C2 point is `F+ell_C*n_C=r_C*z_C` with r_C>0.
Its transverse coordinate is -B_0. A unique physical circle corner
has nonzero own coordinates, so B_0 cannot be zero. The sign of its
actual transverse circle coordinate is fixed by this same proper ray.

The source retains the exact H radius surplus

    E_H=X^2+A^2-d^2,

which is zero in the genuine vertex row and A squared in the genuine
aligned row. If B_0<0, the identity

    a-X=v[G-Xv/(1+u)]>0

and the actual C point F+n_C give squared-radius excess

    3/4-2A+2(a-d)+E_H>1/6.

This proves B_0>0 without suppressing the aligned surplus. The actual
circle corner is therefore `F+n_C-lambda*t_C`, with coordinates
`a+1` and `-B_0-lambda`. Physical uniqueness gives
B_0+lambda>1/2, and hence a<d.

I independently expanded both exact identities

    a^2+B_0^2=d^2+1-2A+E_H,
    lambda^2+2B_0*lambda+2(a-G)
       =2d-11/4+4A-E_H.

Their full-domain consequences are exactly

    B_0>83/120, B_0<X<61/60,
    u<1/3, v>14/15, v>47/50,
    a-G>(1411/1740)u>(4/5)u,
    lambda<1/5,
    A>43/240.

The monotonicity used to prove u<1/3 is valid throughout the interval
from zero to the actual u: the derivative has the sign of B_0, whose
value decreases with u and is positive at the actual point. The
comparison at 1/3 is 51/50>61/60. Every denominator is positive.
The lambda endpoint is exact: `(1/5)^2+(83/60)(1/5)=19/60`.

## 7. Section 8: actual two-leaf angle gap

The actual B-side equation gives
`alpha*A<=delta(1+beta)<1/30`. With A>43/240 it first yields
alpha<8/43<1/5 and beta>9/10. The real B circle equation and
b>t then imply

    A^2+2alpha*A<2delta(1+beta)<1/15,
    A^2<4delta.

The maximization of `2beta*x-x^2` on `0<x<=delta` is
legitimate because beta>delta. The decreasing function
`1/(30A)-A/2` gives

    alpha<1991/20640<1/10, beta>99/100.

These arguments apply to both genuine H rows, with their correct
equations; they do not assume a fictitious aligned vertex radius.

Now the actual B3 ratio from Section 2 has
`sigma>4257/6200`, and its positive denominator is less than one.
The exact reserve

    4257/6200-1/60-2/3=61/18600>0

gives c_B/s_B>2/3 and c_B>1/2. In the actual H frame,

    M=(-c,s),
    c=beta*c_B-alpha*s_B>79/200>1/4,
    s=alpha*c_B+beta*s_B>0.

The frame is genuinely unit. The only K axis strictly northeast is
`t=(s,c)`, which must be the actual HK normal. Thus the proof
legitimately removes the potential same-axis central alternative only
after establishing the actual oblique direction.

## 8. Section 9: actual central position and whole K circle identification

The two genuine K-owned singleton side positions are strict:

    R_0=S_0+ell*m, Q=S_0+theta*t,
    0<ell,theta<1.

Their actual displacement Q-R_0=D_0 f-E2 gives

    alpha*D_0=ell*c+theta*s,
    beta*D_0-1=theta*c-ell*s.

In particular `ell<alpha*D_0/c<20/79<1/2`. Nothing chooses
a new ell or theta.

Both minimum-t K corners are less than one unit from R_0, and
their norms are below 121/60<R. A maximum-t/minimum-m circle
corner would require its own m coordinate at most -1/2, whereas
that actual coordinate is

    -c*h+s*G-ell>-ell>-20/79>-1/2.

Consequently every physical K circle point is the actual opposite
corner

    z_K=R_0+t+(1-ell)m.

This is a proved physical corner identification for arbitrary K mask
and degree. It does not apply a C2 law at K or choose a convenient
circle corner.

## 9. Section 10: complete K-alone-owned CK cover

The unchanged C2 force has transverse component
`-kappa_C(B_0+lambda)=-gamma*(w.t_C)`, so w.t_C>0.
Write

    D=vc-us, J=vs+uc>0, eta=1-lambda>4/5.

At K the actual central side and triangle rule require w.t>=0.
The complete K-owned axis cover is m,-m,t. At C its actual HC
side requires n_C.w<=0. Thus w=m is impossible because n_C.m=J>0.

For w=t the C triangle gives D<=0. Equality is a coframed axis
contact and is incompatible with the actual K-alone-owned singleton
stratum. For D<0 the actual C support is `Z=F+eta*t_C`, and
the proper line gives `ell_C=eta*(-D)/J`. The inequalities
u>c and

    J-v=c[u-vc/(1+s)]>0

give `0<(-D)/J<u/v<5/14`. The unchanged radial coordinate
identity is

    B_0=a*lambda+eta[(-D)/J](B_0+lambda).

Its upper bound is `893/1400`, below 83/120 by 113/2100.
I verified both the actual support point and this full proper-ray
identity, including all side positions.

For w=-m, the required D>0 and the actual C support again give
`Z=F+eta*t_C`. Keep the whole K-owned side position in
`Z=R_0+(1-ell)m+zeta*t`. Its m projection yields

    ell=1-c+eta*D
        =1-c(1-eta*v)-eta*u*s
        >eta(v-u)>12/25.

The exact positive comparison remainder is
`(1-c)(1-eta*v)+eta*u*(1-s)`. This contradicts
ell<20/79, with reserve 448/1975. All K-alone-owned axes are
therefore excluded, with no use of a K2 equation.

## 10. Section 11: complete C-owned and physically shared CK chart

The positive transverse force leaves only w=t_C among C's own axes.
This includes every physically shared CK. If D<0, K's minimum support
is S_0, whose n_C coordinate is `a-u-ell*J<a`; it cannot lie in C.
Thus D>=0.

For D>0 the actual CK point is `R_0+z*m`, z=1-ell. Its
unchanged C-side representation gives

    Z=F+eta*t_C+rho*n_C,
    lambda=1-v+zD,
    rho=zJ-u, 0<=rho<=1.

For D=0 the frames coincide. The full physical intersection instead
has

    u=c, v=s, lambda=1-v,
    0<=rho<=z-u, z>u.

I checked this entire interval directly from both actual supporting
sides. In particular the singleton formula rho=zJ-u is not assigned
to the actual shared mean. The common lambda identity is valid in
both physical types.

The actual circle budget then gives

    (83/60)lambda+(8/5)u<4A-43/60,
    lambda+u<(240A-43)/83.

With j=zc and v>47/50, the full actual-side identity gives

    0<j<q(A)=(12000A-2150)/3901,
    43/240<A<31/120,
    q(31/120)=950/3901<1/4.

These are necessary inequalities for every genuine shared mean and
both genuine H leaf rows. No K force or moment equation is used.

## 11. Section 12: independent audit of the entire unchanged convex comparison

The actual K corner is

    z_K=(h+s-j,1-A+c+(j/c)s).

All divisions by c are safe because c>0. I checked both complete
angle intervals in the source rather than only the final endpoint.

### 11.1 The whole interval c>=1/2

Here s<13/15 and j<Q_0=950/3901<1/4, so the absolute
horizontal coordinate is below 53/60. The positive vertical
coordinate is below

    1-A+sqrt(1+4q(A)^2).

This is convex in A, so its maximum on the necessary closed interval
is at an endpoint. At A_0=43/240 its value is 437/240<223/120.
At A_1=31/120 it is below 223/120 using the exact reserve

    (67/60)^2-(1+4Q_0^2)=532625089/54784083600>0.

Thus the actual corner has squared norm below 17/4, with exact
reserve 47/2880. This contradicts its actual circle contact.

### 11.2 The whole interval 1/4<=c<=1/2

The actual horizontal coordinate is positive because it exceeds
`-1/60+6/7-1/4=62/105`. Therefore replacing h by 1/60
strictly increases its square. The actual real-leaf inequality
A squared<4delta gives `R^2-A^2>17/4`.

For the full function

    F_*(A,c,j)=(1/60+s-j)^2
      +(1-A+c+(j/c)s)^2-A^2,

the coefficient of j squared is 1/c squared, strictly positive.
Convexity reduces the entire necessary j interval to zero and q(A).
At zero the full radius reserve is 3479/3600.

At q(A), the coefficient of A squared is

    (kappa/c)(kappa/c-2s)>0,
    kappa=12000/3901>3.

Thus the entire A interval reduces to its two endpoints. A_0 is the
already treated j=0 case. At A_1, the exact derivative is

    F_1'(c)=2(89/120)-2Q_0^2/c^3
       -2(1/60)c/s-2(89/120)Q_0/(c^2s).

I independently expanded the full derivative after clearing the
positive denominator c cubed times s. The first and last terms already
have negative sum because
`c^2s<=sqrt(3)/8<7/32<Q_0`. The other two terms are negative.
The maximum is therefore at c=1/4. Both squared coordinates are
positive, so replacing s by 31/32 is in the correct direction.
The exact full endpoint reserve is

    72980760071/3506181350400>0.

This contradicts `R^2-A^2>17/4` throughout the second whole
angle interval, including both endpoints. Hence c<1/4, incompatible
with the actual B3 lower bound c>79/200. The final rational gap is
29/200. The entire C-owned/shared CK row is excluded.

## 12. Exhaustive union and preservation of original equations

The source does not assume the central point, the page sign or the
physical return owner. It derives the central point from the actual
oblique B3 and physical K side, transfers the physical circle page
without a global load theorem, and then covers every HC direction.
The genuine H4 moment removes the aligned top-height endpoint before
the top helper is used. The free opposite page is treated with its
full normal cone and shared interval, while the singleton selector
is used only at actual distinct fixed physical points.

The final C-owned page retains its signed circle coordinate before
establishing B_0>0. Both genuine H leaf equations remain intact,
including the aligned surplus E_H. All three K-alone-owned CK axes
and the complete C-owned/shared alternative are covered. Every scalar
bound uses the actual points, means and force ratios.

No K2, H3, removed physical unit, reselected normal, fixed shared mean,
unproved circle-mask deletion or sampled orientation enters the proof.
K may retain the original K3 and any further forces allowed by the
local contract. This is a complete contradiction for the explicit
oblique-return chart.

## 13. Exact present sources, accepted helpers and independent arithmetic

Every following source was read completely and its exact bytes checked:

| Full direct input | SHA256 |
| --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 |
| S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md | 70a3488bb613b1ce1cb4ac778d6f2b2acb2e04bae226741a0665378d096e28ec |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 |
| HIGH_CORNER_CENTRAL_TOP_PAGE_EXCLUSION.md | 580c065de7812c889f91d0e06e7319a3126134b31b8bd31c2044960b7819083b |
| HIGH_CORNER_FREE_OPPOSITE_PAGE_SHARED_RETURN_EXCLUSION.md | 7df434664a33019260a1b5b41983989a536f223edca4702cfed9a91786bb4f9e |

The original sources are under `current_pr11/research/nine`; the
exact recovered connected-neighbor source and both new helpers are
under `recovery_2026_10_27/research/nine`.

The complete top-helper acceptance is separately pinned at

`REVIEW_HIGH_CORNER_CENTRAL_TOP_PAGE_CERT_INDEPENDENT_2026_10_27.md`,
SHA256 `4b39a8e97f4714a8cb37f91665edb3e3069d2a0ecde9d0b0f19c884f362daa14`.

The complete free/shared-helper acceptance is separately pinned at

`REVIEW_HIGH_CORNER_FREE_OPPOSITE_SHARED_RETURN_ROOTED_INDEPENDENT_2026_10_27.md`,
SHA256 `e0096519f88fcd14f664fef5b493d8bd689c885faf1cbc5e503bcfd8f5d71e2f`.

I checked these two acceptance-file byte pins and the complete target
joins; they do not substitute for the full direct-source reads above.

The independent arithmetic reconstruction is saved at

`recovery_2026_10_27/rooted_b_owned_oblique_audit.py`

and its exact result record at

`recovery_2026_10_27/rooted_b_owned_oblique_audit.json`.

It uses sparse rational polynomials with only the displayed unit-frame
relations. It verifies twenty-eight target coordinate or polynomial
identities, including the full real-leaf subtraction, signed C budget,
actual owner-side reconstructions, both convexity coefficients and the
entire final derivative. Forty-nine target rational values and reserves
also agree. One further contact-decomposition identity and three further
rational values record the separately proposed proof-economy argument
below. Thus the saved replay reports 29 identities and 52 values, with
eight input pins and two acceptance pins, all passing.

No author's checker, parameter sample, minimizer, interval-box packet,
Lean or CI was used. The hand inequalities are over whole continuous
intervals; these exact calculations verify algebra, not an alternative
finite-domain certificate.

## 14. Separate shorter argument found during review

This observation is not an alteration of the frozen target or a
replacement for its full review. It has been sent to the author for a
separate credited addendum and another independent acceptance.

The actual central displacement already gives

    ell*c<alpha*D_0<1/10.

Combining it with the already proved actual angle bound c>79/200,
the original j satisfies

    j=(1-ell)c>c-1/10>59/200.

But the complete C-owned/shared CK chart already gave

    j<950/3901,
    59/200-950/3901=40159/780200>0.

This removes the need for Section 12's continuous circle comparison
in a shorter adopted proof. It also makes the K circle identification
unnecessary for that owner row. The actual shared rho interval is
unchanged.

Likewise, the K-owned w=t row has D<0 and therefore u>c, whereas
the prior bounds give

    u<1/3<79/200<c,
    79/200-1/3=37/600>0.

This is a shorter contradiction for that row. The w=-m row retains
its existing complete physical side-position contradiction. These
observations preserve every original equation and require no new
computational certificate.

## 15. Original-adoption and publication boundary

The full local theorem is accepted unchanged. The recovery boundary
in its final section is also correct: the displayed lower-H-leaf
B-owned-HB chart and the physically unique loaded C premise still need
their entire original-family reduction bundle for an original graph
assembly. The missing earlier source at preserved pin

`3ad155e266b71e0c2e91ca67be9328a04e204ede77289a375fbd01c77f48653f`

is not restored by citing its hash, and the positive-concurrence,
parallel-tip and physical-mask joins are not silently assumed to have
newly verified files. They must be recovered exactly or replaced by
complete separately reviewed sources.

The actual vertical BK feature remains a separate local theorem. No
whole hub-tip gate or original ledger is changed by this acceptance.
The local new proof itself has all eight present logical inputs and
introduces zero new computational certificates.

No frozen source, original ledger, remote branch, Lean file or CI
workflow was edited during this review.
