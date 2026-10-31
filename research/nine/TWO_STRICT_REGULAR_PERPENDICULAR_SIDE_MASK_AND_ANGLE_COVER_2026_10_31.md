# A uniform aperture and a complete side-channel mask cover in the regular perpendicular chart

Date: October 31, 2026 UTC. Author: regular-perpendicular continuation.

**Status: complete hand angular and physical-mask reduction, submitted
for separate review.** The exterior-axis cone has aperture strictly
less than 135 degrees throughout the entire original regular chart.
Combining this with the actual owner-side radial exclusion gives a
complete side-N alternative. Every remaining nonradial C case has two
physically unique endpoints and both original incoming angles strictly
between 45 and 90 degrees. Thus every axial, transverse and exact
45-degree boundary is covered before the strict corner chart is used.

This is not an exclusion of the entire remaining side feature.

## 1. The unchanged regular chart

Use the entire actual chart and original radius interval of
`TWO_STRICT_REGULAR_PERPENDICULAR_OWNER_EXTERIOR_RADIAL_MASK_EXCLUSION_2026_10_31.md`.
Its notation is retained:

    h=(c,-s), e=(s,c), k=(C,S), v=(-S,C),
    H=s*C+c*S, J=c*C-s*S, F=J-H,
    0<H<J, H^2+J^2=1, 0<rho<1,
    x=1+s-H*rho in (0,1),
    y=1-c+J*rho in (0,1),
    m=x/y, n=F/(1-rho),
    p=sqrt(m^2+1), q=sqrt((n+H)^2+J^2),
    b=(-m*h+e)/p,
    a=(n*J*h+(n*H+1)*e)/q,
    w=Jrot(b), z=Jrot(a),
    K=P-h+y*e, L=Q-k+(rho-1)*v.

K remains the genuine minimum-b side-interior point of B; L remains
the genuine maximum-a side-interior point of C. The actual A3/D3/V2
stars, all physical circle corners and every original application are
unchanged. The cited owner-side theorem proves that B is physically
unique and that any physical two-corner C is radial along -a.

Sections 2--3 below are radius-free scalar consequences of this chart;
they use no endpoint force equation. Sections 4--5 add the full original
loaded B2/C2 and unloaded N2 hypotheses, exactly as in D02.L135.

## 2. The support difference is strictly inside the exterior-axis cone

Put Sigma=H+J>1 and E=x-F. Then

    E=1+s-J+H*(1-rho)>0,
    Delta=K-L=-E*h+(1+Sigma)*e.                    (1)

The unnormalized exterior directions

    b0=-m*h+e,
    a0=n*J*h+(1+n*H)*e

are nonparallel. Their clockwise angular separation Theta is in
(0,pi), since their h components have opposite strict signs and both
e components are positive. Put

    D0=m*(1+n*H)+n*J>0.

Solving the actual two-coordinate identity gives

    Delta=lambda0*b0+eta0*a0,
    eta0=[-E+m*(1+Sigma)]/D0,
    lambda0=[n*J*(1+Sigma)+(1+n*H)*E]/D0.

The second coefficient is positive directly. The first numerator is

    F-x+(x/y)*(1+Sigma)
       =F+x*((1+Sigma)/y-1)>F>0.

Thus Delta is a strict positive combination of the same actual unit
directions b,a. No new supporting normal has been selected.

## 3. One positive identity bounds the whole aperture by 135 degrees

**Theorem 3.1.** The actual clockwise angle Theta from b to a satisfies

    0<Theta<3*pi/4.                               (2)

*Proof.* The normalized scalar products give

    p*q*cos(Theta)=1+n*H-m*n*J,
    p*q*sin(Theta)=m*(1+n*H)+n*J.

Consequently

    p*q*(cos(Theta)+sin(Theta))
       =1+m+n*Sigma-m*n*F=:D.                     (3)

Write t=1-rho>0. If n*F<=1, then

    D=1+n*Sigma+m*(1-n*F)>0.

If n*F>1 instead, use x<1 and y>J*rho to get
m<1/(J*rho). Because the coefficient 1-n*F is now negative,

    D>1+n*Sigma+(1-n*F)/(J*rho).

Multiplication by the positive J*rho*t and use of n*t=F give

    J*rho*t*D
       >J*rho*t+J*rho*F*Sigma+t-F^2
        =t*(1-F^2)+rho*(F*Sigma*J-F^2)+J*rho*t
        >0.                                       (4)

Every term in the last line is positive: 0<F<1, Sigma>1 and
J>F imply Sigma*J>F. Thus D>0 in both exhaustive cases, including
n*F=1 in the first case. For Theta in (0,pi), positivity of
cos(Theta)+sin(Theta) is exactly Theta<3*pi/4. QED.

No V torque, radius subinterval, endpoint mask, side coordinate or
geometric pose sampling is needed in this aperture theorem.

## 4. The full original side channel and its exhaustive mask cover

Now B and C are the actual positively loaded true2 endpoints, while N
is the actual unloaded true2 side transmitter. Retain their complete
original equations and means. Divide pair magnitudes by the same
positive AD magnitude as in the original hub chart. For the unchanged
N magnitude ell>0 and unchanged unit direction u, these equations give

    T-U=u, |u|=1,
    G_B=p*b+ell*u,
    G_C=-q*a-ell*u.                               (5)

T and U remain the actual N/B and N/C applications. Each circle
resultant is the full nonnegative sum over its entire physical mask.
The full origin torques remain in force; they are not replaced by
the vector equations alone.

The complete loaded-endpoint cone theorem applies to (1), with the
strict support difference proved in Section 2. It puts the unchanged
u in the closed positive cone of b,a and includes both parallel
endpoint alternatives and coincident means. Let

    delta_B=angle(b,u), delta_C=angle(u,a)

be its nonnegative intermediate clockwise angles. They satisfy

    delta_B+delta_C=Theta<3*pi/4.                  (6)

The already established closed-own-side-cone theorem with a genuine
axis port includes the exact 45-degree boundary. Applied to the full
B2, it says delta_B<=pi/4 would make B physically radial along b.
The owner-side exclusion has ruled out that entire physical mask.
Therefore

    delta_B>pi/4,
    0<=delta_C<pi/2.                              (7)

In particular u.a>0 in the entire remaining side chart, before any
classification of C. The original u=b possibility is impossible;
the original u=a possibility remains only in the radial C case.

There are now exactly two physical-mask alternatives:

1. **C has two physical circle corners.** Its entire actual position is

       C=[-d-1,-d]*a+[-1/2,1/2]*z,
       rho>J/(J+H).

   These are the unchanged physical consequences of the owner-side
   exclusion source. Its coefficients remain nonnegative and may
   individually vanish. Its full C2 and N2 equations in (5) remain.

2. **C has one physical circle corner.** The closed-cone theorem at its
   genuine minimum-(-a) side port gives delta_C>pi/4. Combined with
   (6)--(7), this proves the strict full angular domain

       pi/4<delta_B<pi/2,
       pi/4<delta_C<pi/2,
       pi/2<Theta<3*pi/4.                         (8)

   Thus b.a<0 and both channel projections u.b,u.a are positive.
   Neither endpoint parallelism, neither transverse tie and neither
   exact 45-degree equality survives in this physical-mask case.

The alternatives exhaust the physical circle masks because both
original endpoints are genuinely loaded and the original radius
excludes four physical circle corners. A two-corner mask with a zero
individual coefficient remains in the first alternative.

## 5. The original fixed-corner chart in the two-unique alternative

Only after the complete cover above, write the actual owned-side
coordinates as

    B=K+[0,1]*b+[-(1-beta_B),beta_B]*w,
    C=L+[-1,0]*a+[-(1-beta_C),beta_C]*z,
    0<beta_B,beta_C<1.

The strict directions in (8) uniquely expose the original supports:

    T=K+beta_B*w,
    U=L+beta_C*z,
    u=Delta+beta_B*w-beta_C*z.                     (9)

They are conclusions about the actual applications, not replacement
means. The full endpoint force signs in (5) identify the actual
physical circle corners

    Z_B=K+b-(1-beta_B)*w,
    Z_C=L-a-(1-beta_C)*z,
    |Z_B|=|Z_C|=R.                                (10)

The complete same-side true2 theorem also gives the strict absolute
own-coordinate orders

    Z_B.b > -Z_B.w > 1/2,
    -Z_C.a > -Z_C.z > 1/2.                        (11)

For clarity, at B it is used in the actual frame (b,-w), and at C
in (-a,-z). Reversing an oriented coordinate frame reverses all
determinant signs together and changes no physical equation.

Taking the unchanged full torques about these actual unique circle
corners yields

    p*(1-beta_B)=ell*(sin(delta_B)-cos(delta_B)),
    q*(1-beta_C)=ell*(sin(delta_C)-cos(delta_C)).   (12)

Both positive right sides are consistent with, and retain, the
strict angular domain (8). The full vector equations (5), the two
circle equations (10), and all original A/D/V equations are still
required; (12) is not asserted to replace that complete system.

This entire strict chart was reached by physical-mask classification.
No radial corner, individual zero coefficient, tied support or
parallel original endpoint was discarded in order to write (9).

## 6. Scope and direct inputs

The aperture theorem is a uniform algebraic consequence of the
original regular hub chart and holds at arbitrary exterior degrees.
The complete side-mask cover uses both actual loaded true2 endpoint
stars and the actual unloaded true2 N star. Thus its literal original
caller is D02.L135; loaded N in D02.L1345 is not silently treated as
an unloaded transmitter.

The result excludes the entire B-radial mask, every C-radial parameter
in the stated closed lower-rho range, and all of the angular boundary
features outside (8) when C is physically unique. It leaves the actual
C-radial residual and the two-unique strict side chart open. All three
completing squares and every unused original equation remain.

Direct complete inputs:

* `TWO_STRICT_PERPENDICULAR_AD_REGULAR_ANGLE_TORQUE_REDUCTION_2026_10_30.md`;
* `TWO_STRICT_REGULAR_PERPENDICULAR_OWNER_EXTERIOR_RADIAL_MASK_EXCLUSION_2026_10_31.md`;
* `LOADED_ENDPOINTS_FORCE_TRANSMITTER_CONE_AND_PHYSICAL_CORNER_CAP_2026_10_29.md`,
  only its complete finite/parallel/coincident loaded-endpoint cone theorem;
* `LOADED_FULL_STAR_CLOSED_SIDE_CONE_WITH_GENUINE_AXIS_PORT_FORCES_RADIAL_ALIGNMENT_2026_10_29.md`,
  its closed-cone theorem and complete same-side true2 consequence.

All new comparisons are the exact positive identities (3)--(4) or
literal applications of those full-star theorems. No numerical pose
search, computer-generated exclusion, normal reselection, replacement
mean, shortened star, physical-mask relabeling, Lean/Lake invocation or
CI was used.
