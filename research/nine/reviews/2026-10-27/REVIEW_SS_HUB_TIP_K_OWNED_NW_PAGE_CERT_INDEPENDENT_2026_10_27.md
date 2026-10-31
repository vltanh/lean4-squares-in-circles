# Independent review of the K-owned northwest central/page exclusion

Date: October 27, 2026.  
Reviewer: cert_final_review.  
Original comparison head: `50c0cd616eb494ade100f055ad518cdbd33c7275`.

## 1. Verdict and exact recovery boundary

**The complete mathematical argument in all twelve sections passes.**
The original geometric feature, both genuine B leaves, both actual
K-owned CK axes, the entire C-owned CK side-mean interval, and the
free-HC/shared-CK exception are covered. The proof retains the true
H4/B3/C2/K3 equations and introduces no computational certificate.
No mathematical correction to the frozen target is requested.

The exact target is

`SS_HUB_TIP_H_OWNED_SINGLETON_K_OWNED_NORTHWEST_PAGE_EXCLUSION.md`

with SHA256

`b6975fe44d944a6a202fc350d6a2bd64378fe15e7e1d61f1b6f6d2793ac8e1a7`.

It has 28,525 bytes. After a workspace outage restored an older
filesystem snapshot, the author recovered the original target from
its complete original write payload. I then read the entire recovered
file and independently checked its byte length and hash. They match
the previously frozen target exactly. The recovered copy is under
`recovery_2026_10_27/research/nine/`.

There is a separate **dependency-artifact recovery limitation**. Seven
of the thirteen exact direct input files are present and were rehashed
and reread in full in this review. Six newer direct inputs and three
acceptance records are absent from the restored snapshot. Their frozen
pins and prior acceptance are preserved in the ongoing work, but this
review does not claim that those nine missing artifacts have been
restored or freshly reread. Section 12 lists them explicitly. Thus the
new proof passes under its stated accepted input contracts; a complete
publication bundle still requires restoration of the missing pinned
artifacts, or separately reviewed replacement sources. This recovery
qualification is not a new geometric hypothesis and must not be
silently omitted from an integration report.

I independently reconstructed the target's entire physical and
algebraic reasoning, rather than checking only its last scalar
inequality. Twenty-two expanded polynomial or cleared-denominator
identities and forty-two exact rational values/comparisons were also
checked by a separate sparse-polynomial/Fraction calculation. These
checks use exact coefficient expansion and the displayed unit-circle
identities. They use no sampled configurations, numerical minimizer,
symbolic-algebra package, Lean, or CI. The continuous inequalities are
proved in the manuscript and are reviewed below; the calculation is
supplemental verification, not a new certificate premise.

I did not contribute the new northwest-page proof. I previously
reviewed the cited vertical-central source and the loaded-page
application-separation source. My earlier work also supplied some
local owned-side calculations used as provenance by that prior
vertical source. The target reproduces the relevant two-leaf
calculation in full; no unproved vertical-central hypothesis is
transferred to the present central feature.

## 2. Original domain, complete actual central chart, and scope

The original positive graph is

    HK, HB, BK, HC, CK, HL_H, BL_B.

Its true degrees are H4/K3/B3/C2. Both leaves are genuine occupied
radial S leaves. K and C have positive circle loads, and the original
three extra physical squares remain. The accepted whole physical-mask
reductions supply unique physical circle corners at K and C; the
target never deduces uniqueness from the positivity of only one atom.

The radius is retained in the original form

    d=1+delta, 0<delta<1/60,
    R^2=(d+1)^2+1/4, 17/4<R^2<=1105/256.

The actual HB is an H-owned singleton in direction E1. The exact
whole-owner input gives the lower genuine H leaf and

    H=[h-1,h] x [-A,G], G=1-A,
    (1-h)^2+A^2=d^2, |h|<=delta,
    P_HB=(h,-L), 0<L<A<31/120,
    Q_BK=(h+beta,Y), Y=alpha-L.

The genuine B frame and both original leaf equations are preserved.
In particular the aligned B row retains its side application and its
own B3 parameter; its leaf is never replaced by a radial vertex.
The owner chart's cubic bound is tied to the actual leaf axis.

In the present feature K alone owns HK, and BK has its actual
northwest normal m=(-c,s). The actual K frame is m,t, where
t=(s,c), c,s>0. The already proved nonnegative global components of
the actual HK normal make t its only possible K side axis. Therefore
HK is at H's upper-right vertex R_H=(h,G), and its strict K-side
position is ell in (0,1). The actual BK side position theta is also
strictly between zero and one. Equating the original applications
gives

    beta=ell c+theta s,
    Y-G=theta c-ell s,
    ell=beta c+s(G-Y),
    theta=beta s-c(G-Y).

Both signs in these inverse formulas were reconstructed directly.
In particular the beta*c term in ell is positive. The actual B3
normal also gives r_B=beta+alpha(c/s), and hence

    A=L+(1-alpha)+beta(c/s)-ell/s.

No right/up central-height condition is used to obtain these formulas.
The theorem excludes only the complete northwest HC page at
W=(h-1,G). It leaves the distinct H-owned E2 page to its separate
complementary proof. It therefore does not, by itself, close the
whole original hub-tip S/S gate.

## 3. Section 2: identifying the physical K circle without K2

The first physical lemma is uniform on the entire actual central
chart and is independent of any page owner or C equation.

The genuine H leaf implies A>h. For h>0 the proof uses

    A^2-h^2=d^2-1+2h-2h^2>0;

for h<=0 it is immediate. Consequently

    |R_H|^2=d^2+2(h-A)<d^2.

Both minimum-t K vertices are strictly less than one unit from R_H,
so their norms are below d+1<R. They cannot be circle points.

The only remaining undesired corner is maximum-t/minimum-m. Actual
containment, by comparing the two endpoints of its m edge, requires
ell-R_H.m>=1/2 if that corner lies on the circle. This includes the
possible equal-norm endpoint comparison; it does not assume physical
uniqueness to discard the equality.

The exact half-angle bound gives beta<315/653<29/60. The relevant
reserves are 173/514500 for the cubic comparison and 37/39180 for the
last rational comparison. If c<=beta, then s>=alpha>6/7 and

    ell-R_H.m < 61/60-(6/7)(89/120)=8/21<1/2.

For beta<=c<1, ell<beta/c. The continuous function

    F(c)=beta/c+c*delta-G*sqrt(1-c^2)

is strictly convex on the open interval and continuous at both
endpoints. Both endpoint values are strictly below 1/2. Convexity
therefore controls the complete closed interval, including c=beta
and its limiting endpoint c=1. This is a valid upper bound for a
convex function on an interval; no derivative-sign assumption about
the function itself is made.

The physical K circle must therefore be the actual opposite corner

    z_K=R_H+t+(1-ell)m.

Its coordinates are exactly the target's equation (10). No radial
concurrence at K, proper K coefficient, two-force K equation, or
selected K side position is used.

## 4. Sections 3--4: full page ownership and signed C coordinate

The actual northwest HC is a singleton at W and cannot be H-owned.
If CK is also a singleton, both actual C applications are fixed
physical points. Their possible coincidence is explicitly retained
until the true C2 calculation identifies the radial-D inner vertex.
K is a physical boundary neighbor, so equality in the resulting
diameter bound would make K and C contain the same physical circle
point. This is impossible. Only after this physical exclusion does
the already compatible fixed-point selector give owners for both
actual singleton contacts. It is not applied to a variable shared
mean. Thus HC is C-owned in the two-singleton row.

For shared CK, HC may be C-owned or free. Both remain in the target;
the free alternative receives its own exhaustive geometric proof in
Section 11. This owner partition is complete.

In the C-owned row the actual frame is

    n_C=(-u,v), t_C=(v,u),
    C=W+[0,1]n_C+[-lambda,1-lambda]t_C,
    0<lambda<1.

The longitudinal a=Xu+Gv is positive. The transverse quantity
B_0=Xv-Gu is initially signed. Actual positive radial concurrence
at the true unique C circle forces B_0 to be nonzero, and determines
the sign of the actual circle's transverse coordinate.

If B_0<0, the exact identity

    a-X=v[G-Xv/(1+u)]

is positive. The actual unit inward point W+n_C belongs to C, and
its squared-radius excess is

    3/4-2A+2(a-d)>1/6.

This excludes the entire negative transverse sign before imposing a
CK owner. It does not use a fictitious opposite circle corner.

For B_0>0, the actual unique circle is W+n_C-lambda*t_C. Its
transverse own coordinate has absolute value strictly greater than
1/2; thus a<d. The target's complete estimates then follow:

    B_0>83/120, u<1/3, v>47/50,
    a-G>(1411/1740)u>(4/5)u,
    lambda<1/5, A>43/240.

I checked the monotonicity used for u<1/3 on its full domain: the
derivative of Xu+G*sqrt(1-u^2) has the sign of B_0, which is
positive throughout the interval up to the actual u. Its value at
1/3 exceeds 51/50>61/60. Every squaring has positive sides, and all
denominators have already proved positive lower bounds.

The exact circle budget is

    lambda^2+2B_0 lambda+2(a-G)=2d-11/4+4A.

This uses the actual H leaf equation, actual C corner and actual
side position. It is not a loose annulus model.

## 5. Section 5: both complete K-alone-owned CK axes

The physical triangle used here is H-K-C, whose three physical
contacts are all present. At K it gives w.t>=0 because HK is owned
by K in the actual direction t. The complete possible K axes are
m,-m,t. The extra negative m axis is retained. No nonexistent B-C
contact is used to obtain an extra sign.

The choice w=m violates the same physical triangle rule at C.
Writing D=vc-us and J=vs+uc, the true C force's transverse
component also requires w.t_C>0.

For w=t, the C triangle gives D<=0. The equality would make a
coframed side contact, so it is incompatible with a K-alone-owned
singleton. Thus D<0. The actual C support is W+(1-lambda)t_C,
and its unchanged proper line gives ell_C=(1-lambda)(-D)/J.
The comparison J>v is valid on this entire sign domain. Combining
the actual radial coordinates gives exactly

    B_0=a lambda+(1-lambda)[(-D)/J](B_0+lambda).

Its right side is below 893/1400, whereas B_0>83/120. The exact
reserve is 113/2100. No K-side application or mean is fixed to make
this inequality hold.

For w=-m, the incoming proper coefficient is
ell_C=(1-lambda)J/D<=1. The non-strict upper endpoint is valid
because the actual unique-circle C concurrence lies in C. Strict
interiority is neither stated nor required. Projecting the actual
unchanged K-side point gives

    ell=1-c+(1-lambda)D,
    zeta=(1-lambda)J-s, 0<zeta<1.

Consequently D> s, c>s and beta(c/s)>2/5. Both genuine B rows
give u_B>=beta*r_B and x_B>=-delta. The actual L therefore exceeds
7/24, contradicting L<A<31/120 with reserve 1/30. The vertex
proof of x_B>=-delta uses its real radius equation and the already
proved actual u_B<2sqrt(delta); the aligned row uses its actual
x_B=delta. The full two-row scope is retained.

## 6. Section 6: C-owned CK and every shared mean

The nonzero C transverse force leaves only the C side axes
plus/minus t_C. The minus sign contradicts the opposite support
inequality at the actual K point R_H. Thus w=t_C for both singleton
and shared CK.

For z=1-ell in (0,1), a negative D makes the unique K minimum
support point S=R_H-ell*m. Its n_C coordinate is below C's actual
minimum n_C support. Therefore D>=0.

For D>0, projection of the actual point R_H+z*m gives

    lambda=1-v+zD, rho=zJ-u.

The relaxed closed rho interval preserves the original strict
singleton application. At D=0, the actual frames coincide. The
physical shared segment has the entire original interval

    0<=rho<=z-u, z>u,
    lambda=1-v.

Both endpoints remain. The proof does not assign rho=zJ-u to this
shared row. The correct common identities are obtained from the
actual C2 force and moment equations:

    gamma/omega=(B_0+lambda)/(a+1)=B_0/(a+rho).

In particular the source's later D_C=a+rho always uses the same
unchanged actual shared mean.

## 7. Section 7: the whole continuous angle comparison

The C budget yields the uniform strict bound

    0<j=zc<q(A)=(12000A-2150)/3901,
    43/240<A<31/120,
    q(31/120)=950/3901<1/4.

The actual K circle becomes

    z_K=(h+s-j,1-A+c+(j/c)s).

All divisions by c are legitimate because this is the strict
northwest BK feature.

For c>=1/2, the horizontal absolute value is below 53/60.
The positive vertical coordinate is bounded by

    1-A+sqrt(1+4q(A)^2).

This function is convex in A. Both endpoint estimates are valid
and give an upper bound 223/120. Their squared norm is below 17/4
with exact reserve 47/2880. The radical bound was checked with
positive sides and the exact numerator 532625089.

For 1/4<=c<=1/2, the actual horizontal coordinate is strictly
positive before h is replaced by 1/60. The real H leaf equation
gives A^2<=4delta, hence R^2-A^2>17/4. The comparison F(A,c,j)
is convex in j on the entire necessary closed interval. Its j=0
endpoint is below 17/4. At j=q(A), its A^2 coefficient is

    (kappa/c)(kappa/c-2s)>0.

The second convexity comparison therefore reduces to the two actual
A endpoints. The A_0 endpoint is the already covered j=0 row.

At A_1 the exact derivative is

    2G_*-2Q_0^2/c^3-2h_*c/s-2G_*Q_0/(c^2s).

I independently expanded this derivative using s'=-c/s. All
cross terms cancel as stated. The bound
c^2s<=sqrt(3)/8<7/32<Q_0 makes its first and last terms already
have negative sum; the other two are strictly negative. Thus the
whole interval is bounded by c=1/4. The radical replacement at that
endpoint increases both positive squared coordinates. The exact
remaining reserve is

    72980760071/3506181350400>0.

Consequently c<1/4 follows over the entire continuous actual domain.
This is a proof by two convexity comparisons and a derivative sign,
not a discretized orientation cover.

## 8. Section 8: the two actual leaf equations sharpen the displacement

Both genuine B rows imply beta^3<delta(1+alpha)<1/30, so beta<1/3
and alpha^2>8/9. Define the exact auxiliary

    b_*=L+(1-alpha)+beta(c/s)=A+ell/s>A.

The target proves (1+h)^2+b_*^2<d^2 separately for both real
leaf features. I independently expanded both identities.

For the genuine vertex row, the exact positive factorization uses
its own actual radius equation and actual B3 parameter. The two
displayed terms are strictly positive; the coefficient multiplying
k in its bracket exceeds 2/3 on the entire interval.

For the aligned row, the expansion uses its real coordinates
h=alpha*delta-beta^2*r and L=beta*delta+alpha*beta*r. Its delta
coefficient is positive. The remaining scalar is bounded by a
function increasing in the true half-angle t_0. The complete first
interval 0<r<=4/15 has lower bound 9r/10. On the complete second
interval 4/15<=r<3/5, the concave quadratic has endpoint values
6/25 and 87/800. Both interval endpoints are included, and no
aligned vertex equation is imposed.

Comparing this auxiliary inequality with the real H leaf equation
gives h<0 and

    A+b_*<2sqrt(d^2-1)<11/30.

Together with the earlier A>43/240, this proves

    A<11/60, G>49/60,
    ell/s<1/120, ell<1/120, z>119/120.

The same actual C circle budget then gives lambda<1/83 and u<1/96.
Using zvc<lambda+u yields

    c<22375/928438<1/40, s>99/100.

The small central displacement is a derived consequence of both
genuine leaves. It is not imposed as a preliminary restriction or
borrowed from the different vertical-central feature.

## 9. Sections 9--10: physical direction versus the entire K3 force

The physical K circle identified before all page ownership has
horizontal coordinate greater than 569/600>9/10 and positive
height below 25/12. Its actual direction therefore satisfies

    (z_K)_x/(z_K)_y>54/125.

The actual C2 ratio gives D_C=a+rho>17347/12840>1>G, with the
original rho unchanged. The genuine leaf forces have zero moment
about the original circle center. Keeping every actual pair moment,
the H4 and B3 equations are

    L*mu_HB+tau(hc-Gs)-B_0*omega=0,
    -L*mu_HB+nu*D_Q=0.

The C2 moment therefore gives

    gamma*D_C=nu*D_Q+tau(hc-Gs).

The actual K3 force still has all three positive pair terms:

    kappa_K*z_K=tau*t+nu*m+gamma*t_C.

Combining the full moments with only its horizontal component
gives the source's exact cancellation identity. The remaining
central term tau*h*c is strictly negative because h<0, and the
C term gamma*(Gv-D_C) is strictly negative because D_C>1>G.
The full vertical component is strictly larger than nu*s.
The resulting upper bound is

    (z_K)_x/(z_K)_y
       < beta/(G*s^2)
       < 200000/480249 < 54/125.

Every divided quantity is positive before division. The final exact
reserve is 933446/60031125. This contradicts the actual physical
circle direction and excludes the complete C-owned HC row,
including the entire physical shared CK mean interval.

## 10. Section 11: the full free-HC/shared-CK exception

Only the shared CK row can retain a free HC. The target exhausts
all four signed shared translations in the actual m,t frame. The
maximum-t and minimum-m translations miss W. Across minimum t,
W's transverse coordinate lies strictly inside the C side, so W
cannot be a C vertex; that row belongs to the earlier C-owned HC
case rather than to a free normal.

Across maximum m, W can only be the lower m endpoint. Its lower
t endpoint is also forced by positive shared overlap. Thus the
entire remaining geometry is

    ell=1-c,
    C=W+[0,1]m+[0,1]t,
    w_CK=-m.

The original free HC normal is retained in its full strict common
vertex cone. Its positive components along both m and t, together
with the true C2 force, identify C's actual circle as W+m+t.
The whole-domain K physical lemma independently identifies
K's actual circle as R_H+c*m+t.

I expanded their exact squared-norm difference:

    -2h(c+s^2)+2Gs(1-c)+2c+(1-s)^2.

It is positive for all 0<c<1. For c<=1/2 the displayed lower
bound is 239/420; for c>=1/2 it is 14/15. The first term is
bounded only by |h|<1/60. The later h<0 consequence from the
C-owned HC proof is correctly not imported into this separate
free-normal branch. Both actual circle norms would have to equal
R, giving the contradiction without changing the normal or mean.

## 11. Verification record and exact remaining claim

The separate exact reconstruction checked the following substantive
identities as complete polynomials or cleared rational functions:

- The two actual-frame rotations and both inverse central formulas.
- Every side projection in the two K-owned CK axes and the C-owned
  singleton/shared chart.
- The actual C circle budget and its two actual moment determinants.
- The complete derivative used in the continuous c interval.
- Both genuine B-leaf radius identities, including the aligned
  scalar comparison and its second derivative.
- The original central elimination in D_Q and the full K3 moment
  cancellation.
- The full free-HC/shared-CK squared-circle difference.

Forty-two exact rational values and comparisons include every
displayed final reserve and each radical comparison with a rational
replacement. The calculation does not call the original author's
checker and does not use floating-point sampling.

The mathematical conclusion is exactly the target's whole northwest
HC page exclusion in the H-owned HB / K-owned HK / northwest BK
feature. The actual H-owned E2 page is its complementary unresolved
feature here. No whole hub-tip gate or ledger count is changed by
this review. No force, original degree, physical extra, shared mean,
normal-selection exception or upper-radius endpoint is discarded.

## 12. Exact target and dependency availability record

The target itself was independently rehashed at the exact frozen
pin given in Section 1. The following complete inputs were found
at their exact pinned bytes and reread in full after recovery:

| Complete input | Verified SHA256 |
| --- | --- |
| TWO_S_ROOT_TRIANGLE_OWNED_SINGLETON_ADJACENT_PORT_NORMAL_FORM.md | 2397a468e15cb7043a4774f4ce5bfc3dabb34b0d85937991f444819b4cf2ac88 |
| SS_HUB_TIP_CENTRAL_SINGLETON_DISTINCT_FRAME_NORMAL_FORM.md | 89ff6eee18061f7ef57fea5acd8da87ce42ff3c24185d478da113c181e77fae0 |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md | a33b15a4a3e7894c256ee1877edfb47f6241fd208558765267113e56e12a1b4e |

The following newer direct inputs are mathematically used at the
precise contracts stated in the target, but their previously frozen
files were absent from the restored snapshot when this review was
saved. Their listed hashes are the preserved prerequisite pins,
not a claim of a new byte verification:

| Missing exact direct artifact | Preserved SHA256 |
| --- | --- |
| SS_HUB_TIP_H_OWNED_SINGLETON_VERTICAL_C_OWNED_PAGE.md | e80e37f301f1ac7e492cf9650a5f7f43295639aa843b548dd61c8e633d5c5660 |
| LOADED_BOUNDARY_PAGE_DISTINCT_ROOT_APPLICATIONS.md | 3401781bde8a3d908e8c869f179da8618189fb680979e3ff6ca44d7179a48168 |
| UNIT_TRIANGLE_OWNED_SINGLETON_SHARED_RETURN.md | cda14432fafffe1985969229dccd7a15d1d04581b4e80e090862b9c79a1b942b |
| SS_HUB_TIP_H_OWNED_SINGLETON_VERTICAL_CENTRAL_EXCLUSION.md | 74fb39f76726e827438966dc324a03f50956f99169b1008f59f40e909a697619 |
| SS_HUB_TIP_RADIAL_PAGE_FULL_EXCLUSION.md | 2bf0e377d1c17d28c7e49742b418ea6a60a8b9fbe7dad56249e73cf0e96a8d9b |
| SS_HUB_TIP_LOADED_HUB_PHYSICAL_UNIQUENESS.md | ce1c5e44c1ac9334775e0775323830ea6eea0d63a56ebfb4f294960d43da79af |

The three immediately cited acceptance files are also absent from
that snapshot:

| Missing exact acceptance artifact | Preserved SHA256 |
| --- | --- |
| REVIEW_HIGH_ROOT_SIDE_AND_H_OWNED_VERTICAL_PAGE_TOPOLOGY_INDEPENDENT_2026_10_27.md | fc82d3e7a25588237e24fbde172da6de62de9e7045e7e709f2cefca79610e19f |
| REVIEW_SS_HUB_TIP_H_OWNED_VERTICAL_CENTRAL_CERT_INDEPENDENT_2026_10_27.md | f0077da6486eccbb64db3e9f337692cfc71097314cb5580b0f9a678d5a36101d |
| REVIEW_LOADED_BOUNDARY_PAGE_DISTINCT_APPLICATIONS_CERT_INDEPENDENT_2026_10_27.md | 8611ae03bb7abd3fb636ac4f219bba951592c138152d9dba38ad83b2c76c173c |

This explicit availability record preserves the difference between a
complete new mathematical review and a fully recovered publication
bundle. The target's original proof bytes are unchanged, no original
accepted bytes are overwritten, and no ledger or remote source is
edited by this review.
