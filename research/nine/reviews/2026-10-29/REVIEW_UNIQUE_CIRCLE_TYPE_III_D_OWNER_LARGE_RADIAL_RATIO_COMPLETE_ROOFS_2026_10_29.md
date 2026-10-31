# Full independent review: large radial-ratio exits for both Type III D owners

Date: October 29, 2026 UTC. Reviewer: roofs continuation.

**Decision: ACCEPT the complete stated high-ratio theorems at the
frozen source below.** The genuine sole-D feature is excluded for
every original p>=1 and every genuine tilt. The physical shared-D
feature is excluded for every original p>=7/5 and every full original
mean. Both radial endpoints are included with strict reserves.

This is a full independent noncontributor review of the original
force/torque reconstruction, complete scalar comparison domains,
actual C-point membership, all derivative arguments, exact endpoint
arithmetic and literal caller joins. It is not an acceptance based
only on the final numerical reserves.

## 1. Frozen source and complete operative reading

Reviewed source:

    UNIQUE_CIRCLE_TYPE_III_D_OWNER_LARGE_RADIAL_RATIO_FULL_STAR_EXCLUSION_2026_10_29.md
    SHA256 6db6cfbfa05d09b1a1cbfd93e7910b17e1fa6f85ecaef39ff51665e4a9acf3b8

I read the whole current source and reconstructed its proof. The
operative inputs were also read in full:

| Source | SHA256 | Scope checked |
| --- | --- | --- |
| UNIQUE_CIRCLE_TWO_STRICT_ROOF_PORTS_PERPENDICULAR_INTERFACE_EXCLUSION_AND_COMPLETE_SAME_AXIS_DOMAIN_2026_10_29.md | f8cce87f5bbc22ba898db4029676dd84f1fb1c448212a809ee6809cffc5056eb | Full original genuine/shared D-owner charts, V2 and A3/D3 equations, angular domain and exact D02 roles |
| UNIQUE_CIRCLE_TYPE_III_BOTH_D_OWNERS_FULL_MEAN_SMALL_RADIAL_RATIO_EXCLUSION_2026_10_29.md | a4dbb88633fff667457ecab23ac1320c588bdb2fe0ddda46b2d8217ea13812c7 | Only the separate p<=1/2 theorem needed for the stated remaining-domain join |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original positive forces, physical applications and full means, physical-mask distinction, strict singleton convention |

The p<=1/2 input has my separate complete independent ACCEPT report
REVIEW_UNIQUE_CIRCLE_TYPE_III_BOTH_D_OWNERS_SMALL_RADIAL_RATIO_COMPLETE_ROOFS_2026_10_29.md,
SHA256 29a1411868f866950fbd3fcbae4b154c214d655fb81567ff2c01fb1db7773fe5.
Neither high-ratio proof depends on that input's numerical bounds.

I did not contribute the original-ratio estimate, the fixed C
projection, the shared vertical exit or any endpoint arithmetic to
this source. The frozen manuscript was unchanged during the review.

## 2. Full original setting and common scalar chart

The source retains A,D unloaded true3 with original stars {V,D,B}
and {V,A,C}, and V loaded true2 with original star {A,D}. The
actual unique physical circle corner of V is Z=(a,b), a,b>1/2,
with unchanged applications P1=(a-1,b), P0=(a-1,b-1).

I checked the full V equations

    mu*h+nu*nD=kappa*Z,
    mu*det(P1,h)+nu*det(P0,nD)=0,

and their consequences mu*c=kappa*(a-b)>0,
nu*C=kappa*b>0, and nu*(S-C)=mu*s. The common coordinates are
therefore exactly

    k=-K/H, J=sqrt(1+k^2), H=1/J, K=-k/J,
    u=c+k*s,
    p=(mu/nu)*J-k=(1+k)*c/s-1,
    x=p+1, v=1+k, T=sqrt(x^2+v^2),
    c=x/T, s=v/T,
    Y=R/sqrt(1+p^2), Z=(p*Y,Y),
    P1=(p*Y-c,Y-s), P0=(p*Y-c+s,Y-s-c).

These are actual coordinates in the unchanged A frame h,e. The
original circle origin has not been moved. The genuine sole-D
feature has 0<k<1/sqrt(3)<3/5 and r=u<1, together with the
full slider 0<t<1-s*J. The shared feature has k=0 and

    r=c, 0<t<1-s,
    W=P1-z*h-c*e=P0+(s+z)*tD,
    0<=z<=1-t-s.

Both shared-mean endpoints remain. A physical two-corner mask with
one zero coefficient does not enter this unique-physical-corner chart.
There is no symmetry interchange of the upper and lower V ports.

## 3. Genuine sole-D: exact original force ratio and actual C point

The complete genuine data copied from the direct input are

    F_B=rho*nD-mu*h,
    Q_B=P1-h+(1-u)*e,
    mu*(1-u)=rho*(H+K),
    F_C=-(nu+rho)*nD,
    Q_C=P0-nD+z_D*tD,
    z_D=rho*(s/H)/(nu+rho).

All original mu,nu,rho are positive. Combining the full A torque
with mu/nu=(p+k)/J and H+K=(1-k)/J gives exactly

    q=rho/nu=(p+k)*(1-u)/(1-k)>0,
    tau=q/(1+q), z_D=tau*s*J.

The last equality uses the full original D moment. No support mean
has been freely selected, and no force at either unloaded hub has
been omitted.

The actual-point argument is valid for every possible support owner
of C. For a unit with minimum-support point or full side mean Q in
unit-normal direction f, each nonzero own-axis component of f moves
from its support endpoint inward by at most one; a zero component
preserves the entire own-side coordinate. Thus Q+f belongs to that
same actual unit, including every side mean and endpoint.

Applying this with f=-nD and the actual Q_C gives

    X_C=Q_C-nD=P0-2*nD+z_D*tD in C.

Since nD=(-k,1)/J and tD=(-1,-k)/J in h,e coordinates,

    X_C=(p*Y-c+s+2*k/J-z_D/J,
         Y-s-c-2/J-k*z_D/J).

I checked both coordinates. The proof does not require C loaded or
degree two; the literal caller retains its stronger original data.

## 4. Complete genuine force-ratio bound for every p>=1

At fixed original p>=1, the source compares the explicit functions
on the whole auxiliary interval 0<=ell<=k. Write x=p+1>=2 and

    T0=sqrt(x^2+1), c0=x/T0, s0=1/T0,
    delta0=1-c0.

Direct differentiation gives

    c'=-c*s/T, s'=c^2/T,
    u'=s*(1-c/T)+ell*c^2/T.

The component s increases. Also c/T=x/(x^2+(1+ell)^2)<1/x<=1/2,
so u'>s0/2 over the complete comparison interval. Integrating
from zero to actual k>0 gives

    u(k)>c0+(s0/2)*k,
    1-u(k)<delta0-(s0/2)*k.

The latter right side is positive because the actual left side is
positive. The monotonicity of u also ensures u(ell)<1 throughout
the comparison to actual k. Thus all factors used in the next
inequality have justified signs.

Rationalization gives delta0/s0=1/(T0+x). Since T0>x,

    (p+1)*delta0<s0/2<=p*s0/2.

Using the original q formula, one obtains

    q<(p+k)*(delta0-(s0/2)*k)/(1-k)<p*delta0.

For clarity, subtracting p*delta0 from the middle expression and
multiplying by positive 1-k leaves exactly

    k*((p+1)*delta0-(p+k)*s0/2)<0.

This verifies the second strict inequality for every genuine k.
Finally

    p*delta0=p/[T0*(T0+p+1)]
             <p/[2*(p+1)^2]<=1/8,
    tau=q/(1+q)<1/9.

The weak final rational bound is equivalent to (p-1)^2>=0;
the earlier comparison is strict, including at p=1. The complete
argument is uniform in every original genuine tilt. It is not a
small-k approximation or a numerical estimate at a selected mean.

## 5. Full genuine C-projection proof

I expanded the projection of the actual X_C on the fixed unit
direction (3,-4)/5. The result is exactly

    5*P_C=R*(3*p-4)/sqrt(1+p^2)
       +c+[7+(4*k-3)*tau]*s+(8+6*k)/J.

Because actual k<3/5, 4*k-3<0. Hence the upper bound tau<1/9
gives the strict lower estimate

    5*P_C>R*(3*p-4)/sqrt(1+p^2)+A(p,k),
    A=c+(20/3+4*k/9)*s+(8+6*k)/J.

The sign reversal in this step is correct. The full actual mean is
present before this bound is applied.

On the entire comparison domain p>=1, 0<=k<=3/5, direct
differentiation gives

    A_k=[-c*s+(20/3+4*k/9)*c^2]/T
         +(4/9)*s+(6-8*k)/J^3>0.

The first grouped term is positive because c/s=(p+1)/(1+k)>=5/4,
so (20/3)*c>s. The middle term is positive, and the last numerator
is at least 6/5. Therefore

    A(p,k)>=A(p,0)=8+(p+1+20/3)/sqrt((p+1)^2+1).

The scalar comparison at k=0 does not identify the actual genuine
feature with the separate physical shared row.

For the resulting function

    L_R(p)=8+(p+1+20/3)/sqrt((p+1)^2+1)
            +R*(3*p-4)/sqrt(1+p^2),

the geometric derivative is

    [1-(20/3)*(p+1)]/((p+1)^2+1)^(3/2)
        >-20/[3*(p+1)^2].

For p>=1, 1+p^2<=p*(p+1) and sqrt(1+p^2)<p+1. Multiplying
gives (1+p^2)^(3/2)<p*(p+1)^2. Thus the radial derivative
(3+4*p)/(1+p^2)^(3/2) exceeds 4/(p+1)^2. With the unchanged
actual R>=79/40, these bounds yield

    L_R'(p)>(37/30)/(p+1)^2>0.

Both continuous variables have therefore been reduced analytically
over their entire domains. At p=1 the strict lower bound is

    5*(P_C-R)>8+26/(3*sqrt(5))-R*(5+1/sqrt(2)).

The positive-side square comparisons prove
26/(3*sqrt(5))>31/8 and 1/sqrt(2)<71/100. Together with
R<1039/500 they give

    5*(P_C-R)>95/8-(1039/500)*(571/100)
              =481/50000>0.

The p=1 endpoint is included. For larger p, the strictly increasing
L_R retains the same reserve. The actual point X_C in C has
unit-direction projection greater than R, contradicting containment.

## 6. Shared-D: the original mean disappears only from the vertical coordinate

I checked the shared data separately, including the full moment:

    F_B=rho*e-mu*h,
    Q_B=P1-h+(1-c)*e,
    rho*(1-z)=mu*(1-c),
    F_C=-(nu+rho)*e,
    Q_C=P0-e+z_D*tD,
    z_D=rho*(s+z)/(nu+rho), tD=-h.

The essential original s+z numerator is retained at every mean,
including both endpoints. The actual point lemma gives

    X_C=Q_C-e=(p*Y-c+s-z_D,Y-s-c-2) in C.

Its second coordinate is genuinely independent of z_D because
tD=-h; this is an exact physical coordinate fact, not replacement
of the original mean by a convenient endpoint.

The exact excess of its (-e)-projection above R is

    H_R(p)=2+(p+2)/sqrt((p+1)^2+1)
              -R/sqrt(1+p^2)-R.

Its derivative is

    H_R'=-p/((p+1)^2+1)^(3/2)
           +R*p/(1+p^2)^(3/2)>0

for all p>0, because R>1 and the first denominator is larger.
At p=7/5, the exact values c=12/13,s=5/13 give

    H_R(7/5)=43/13-R*(1+5/sqrt(74)).

The strict inequality 5/sqrt(74)<7/12 follows by squaring positive
sides. Consequently the entire closed domain p>=7/5 satisfies

    H_R(p)>43/13-(1039/500)*(19/12)
             =1367/78000>0.

This is another contradiction from an actual point of C in a unit
direction. Every full original shared mean and every original
exterior support owner remain covered.

## 7. Independent exact arithmetic audit

The following values were recomputed with exact integer and rational
arithmetic. All agree with the frozen source:

| Comparison | Recomputed value |
| --- | --- |
| (1039/500)^2-1105/256 | 6711/4000000 |
| 6-8*(3/5) | 6/5 |
| 4*(79/40)-20/3 | 37/30 |
| 208^2-5*93^2 | 19 |
| 2*71^2-100^2 | 82 |
| 95/8-(1039/500)*(571/100) | 481/50000 |
| 49*74-25*144 | 26 |
| 43/13-(1039/500)*(19/12) | 1367/78000 |

The full derivative identities, original-force formulas, sign of the
tau coefficient and both exact endpoint substitutions were independently
expanded as described above. These finite arithmetic checks support
the continuous proof and do not stand in for a pose or angle search.

## 8. Exact original-family join and remaining scope

Both literal callers retain

    A=0,V=1,D=2,C=3,N_original=4,B=5,
    rim A--V--D--C--N_original--B--A, chord AD.

A,D remain unloaded true3. V,B,C remain loaded true2. The actual
N remains unloaded true2 in D02.L135 and loaded true2 in
D02.L1345. Every original force, torque, full mean, physical circle
corner and individual zero coefficient remains. All three additional
actual units remain. The argument imposes no transmitter equation on
the loaded N and no reduced-star equation on B or C.

Joining the separately independently accepted small-ratio theorem
leaves exactly the necessary intervals stated by this source:

    genuine sole-D: 1/2<p<1;
    physical shared-D: 1/2<p<7/5.

This is an exact join of closed exclusions: p=1/2, p=1 and p=7/5
have all been removed by strict contradictions. The source does not
claim either middle interval closed. Separate later theorems may
exclude additional domains, but are not prerequisites or credited
conclusions of the reviewed proof.

The original owned-normal Type III entry remains conditional on its
separate compatible-selector domain. No normal is reselected after
stress extraction, no unique-corner assumption is applied to a physical
two-corner mask, and no Type I/II or physical-two conclusion is imported.

## 9. Final review decision and verification boundary

The complete current source at 6db6cfbf is accepted for both full
stated radial domains. I found no missing original mean, loss of a
closed endpoint, incorrect sign, unjustified auxiliary physical path,
force deletion, support-point error or literal-degree mismatch. No
correction is requested.

This review does not close a whole D-owner row, a whole D02 load
family, the global common-selector obligation, the sharp nine-unit
theorem, equality classification or Lean. No source mutation, metadata
edit, Lean/Lake build, CI run, numerical pose search, packing
certificate, remote write or merge was performed.
