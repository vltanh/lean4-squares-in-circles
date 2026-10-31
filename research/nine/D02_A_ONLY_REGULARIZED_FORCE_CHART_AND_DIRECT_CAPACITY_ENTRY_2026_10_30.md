# A-only force regularization and normalization-free physical entry

Date: October 30, 2026. Author: pocket_capacity continuation.

**Status: proved algebraic reformulation of the existing complete A-only
both-unique necessary system.** This source supplies a regular chart for a
strict-angle boundary and removes repeated normalizations from the exact
circle equations and actual vertex formulas. It neither asserts exhaustive
root isolation nor closes the whole original D02 row.

All nine actual squares, the original positive graph, actual force and torque
equations, physical masks, original application means and selected normals are
retained. Dividing all original force magnitudes and circle coefficients by
one common positive magnitude is only an algebraic normalization of the same
certificate; it changes no selected direction, application, mean or zero set.

## 1. Exact inherited identities and the regular ratio

Use the actual variables of
`TYPE_II_A_ONLY_WHOLE_TRANSVERSE_GAP_AND_EXACT_BOTH_UNIQUE_SIDE_MATRIX_2026_10_29.md`,
Section 1. Thus

    s=sin(alpha), c0=cos(alpha), S=sin(beta), C=cos(beta),
    delta=s-c0>0,
    H=c0*S+s*C, k=s*S-c0*C, p=H-k>0,
    0<u,t,omega<1,
    omega=(1-u)*H/S,
    t=(S-s+s*u)/S.

Set eta=1-omega. All S,p,t,eta are strictly positive on the actual branch.
The full original positive magnitudes satisfy

    rho*u=mu*delta,
    nu*t=rho*p,
    (mu/nu)*eta=S-C,
    mu>0,nu>0,rho>0.                                      (1)

Normalize by the same original nu and define

    r=rho/nu=t/p,
    m=mu/nu=(S-C)/eta,
    w=u/delta.

Then the following exact identity holds throughout the strict original domain:

    w = p*(S-C)/(t*eta),       m=r*w.                       (2)

**Proof.** Divide the first equality in (1) by nu*delta, obtaining
m=(rho/nu)*(u/delta)=r*w. The other two equalities give r=t/p and
m=(S-C)/eta. Since r,t,p,eta are positive, solve for w to obtain (2).
No equation at a completing square or at the unloaded transmitter is altered.

Equivalently, the original hub cubic is

    u*(S-s+s*u)*(S-H+H*u)
      =p*delta*S^2*(S-C).                                 (3)

Substitute S*t for the second factor and S*eta for the third; cancellation
of the positive S^2 gives u*t*eta=p*delta*(S-C), again yielding (2).
Thus the ratio formula follows directly from the original full moments and
also agrees with the monotone cubic used by the interval contractor.

## 2. Regular vectors and full magnitudes

In the same original orthonormal (h,e) frame, introduce

    B0=(m*c0+r, m*s),       C0=(r+k,H),
    b=-B0/|B0|,
    c=(-C0_x,C0_y)/|C0|,
    w_B=(b_y,-b_x),        w_C=(-c_y,c_x),
    F=(m*c0-k, m*s+H),
    P_B=|B0|,             P_C=|C0|.                       (4)

Here m,r>0 and H>0, so B0,C0 are nonzero. F is nonzero because its
second coordinate is positive. The meanings of P_B,P_C are the original
return-force magnitudes divided by nu; the original common BN/NC magnitude
is divided by nu at the same time. Consequently every previous full force
and torque equation remains valid in these normalized quantities.

These formulas are exactly the old vectors. For example

    B0=r*(w*c0+1,w*s)
       =(r/delta)*(u*c0+delta,u*s).

The positive factor cancels from its unit direction. Formula (2) permits
evaluating w, m and r without dividing an interval by delta. One may
evaluate m directly as (S-C)/eta and avoid w entirely.

The old scaled choice mu_scaled=u*t, nu_scaled=delta*p yields the
same ratio m. Its vector normals and all circle equations are related to
(4) by multiplication by that common positive nu_scaled. Hence both charts
cover the same original strict domain; use whichever has better interval
denominator bounds. Neither permits changing the original physical owner.

## 3. Why the alpha=pi/4 boundary can be covered uniformly

At alpha=pi/4, the scaled variables in the preceding paragraph all vanish
when u tends to zero, even though the original normalized force ratios may
have finite positive limits. This is an artificial coordinate singularity.
The regular chart (2)--(4) has no such singularity whenever t and eta
have positive lower bounds.

Two simple sufficient bounds are

    S>s, S>H,
    t >= (S-s)/S >0,
    eta >= (S-H)/S >0.                                    (5)

They follow from u>=0, s>0 and H>0 in the exact formulas. Thus a rational
interval rectangle whose certified sine bounds give S_lower>s_upper and
S_lower>H_upper has explicit positive lower bounds for both denominators.

On the limiting edge alpha=pi/4 and beta>3*pi/8,

    S>s=1/sqrt(2),
    H=(S+C)/sqrt(2),
    S-H>0  iff  tan(beta)>sqrt(2)+1.

The latter is exactly beta>3*pi/8. The inequalities are strict, so every
closed subinterval bounded away from that endpoint has a uniformly regular
neighborhood. The actual branch is still alpha>pi/4; including its limit
in an interval cover does not assert a new physical case or a nonzero force
at a formerly vanishing coefficient.

For a concrete coarse rational half-angle box, take

    sqrt(2)-1 <= tan(alpha/2) <= 47/100,
    tan(beta/2) >= 7/10,
    alpha+beta <= 2*pi/3.

Then

    S >= 140/149,
    s <= 9400/12209 < 140/149,
    H <= 191/(149*sqrt(2)) < 140/149.

For the H bound, alpha+beta is in the decreasing branch of sine and
is at least pi/4+2*atan(7/10); its sine there is
(140+51)/(149*sqrt(2)). The strict final comparison is certified by
2*140^2-191^2=2719>0. Thus (5) is uniform on this whole coarse box.
The upper sum bound also gives p>=(sqrt(3)-1)/2>0. These are examples
of exact denominator control, not an assertion that the whole original
domain is contained in that one box.

## 4. Cancel the roof normalization from both circle equations

Let g=F/|F| and retain the existing actual offsets

    E_B=D_B-b-x_B*w_B,
    E_C=D_C+c+x_C*w_C,
    Z_B=Z-E_B, Z_C=Z-E_C, Z=R*g.

Both named circle corners have norm R. Their exact equations are

    |E_B|^2=2*Z dot E_B,
    |E_C|^2=2*Z dot E_C.                                  (6)

Whenever F dot E_B>0, (6) gives the actual original circle vector directly:

    lambda=|E_B|^2/(2*(F dot E_B))>0,
    Z=lambda*F,            R^2=|Z|^2.                     (7)

Indeed Z is a positive scalar multiple of F by the full V force equation.
Insert this fact in the first equation of (6). The second then becomes
the normalization-free polynomial/radical identity

    |E_B|^2*(F dot E_C)-|E_C|^2*(F dot E_B)=0.             (8)

The previous positive g dot E_B implies F dot E_B>0, since |F|>0.
Formula (7) avoids separately enclosing R and g and multiplying the resulting
dependent intervals. Every actual core vertex is obtained from this unchanged
Z by adding the original frame/side offsets.

For the original B moment-radius formula, write

    cd=d dot b, sd=d dot w_B, kB=d dot(w_B-b),
    Db=D_B dot b, Dw=D_B dot w_B,
    N=Dw*(kB+x_B*cd)-x_B*sd*Db+x_B*(1-x_B)*cd,
    DF=(kB+x_B*cd)*(F dot w_B)-x_B*sd*(F dot b).

Multiplying the old denominator by the positive |F| shows that its full
moment equation is equivalently

    |E_B|^2*DF-2*(F dot E_B)*N=0.                         (9)

The old strict denominator signs are preserved. Equations (7)--(9) remove
only a repeated positive normalization; they discard no singular determinant,
side mean, endpoint, force or actual circle equation.

## 5. Two further exact interval reductions and the physical exit

With the old sigma>0, Delta, A_B,A_C and r_B,r_C, evaluate the genuine
side offsets in the cancellation-preserving forms

    x_B=1+((d-Delta) dot c)/sigma,
    x_C=1+((d-Delta) dot b)/sigma.                         (10)

These are exactly r_B-A_B and r_C-A_C. They avoid subtracting two
separately enlarged copies of the same projection. Likewise if
B0=(X,Y), C0=(U,V), then

    sigma=(X*V+Y*U)/(|B0|*|C0|),
    tau=(X*U-Y*V)/(|B0|*|C0|).

The strict necessary unit-direction filter from the table-first draft remains

    A_B^2+A_C^2-2*tau*A_B*A_C < 1,                       (11)

because A_B,A_C>0, x_B,x_C>0, tau<0 and the same increasing quadratic
at (A_B+x_B,A_C+x_C) equals one. This condition does not depend on the
remaining side-direction parameter and may prune a whole angle box before
subdividing that parameter.

Finally, actual vertex coordinate enclosures obtained from (7) can be supplied
directly to `verify_actual_vertex_boxes` in `scripts/n9_five_core_capacity.py`.
Section 8 of `FIVE_CORE_ROBUST_CENTER_COVER_CAPACITY_EIGHT_2026_10_30.md`
proves that interface. A successful call excludes the full nine-unit packing
on the whole enclosed algebraic box, including arbitrary N and all three
completing squares. An unsuccessful call is only an unproved box.

Combining these algebraic identities with that physical exit provides a route
to a finite complete branch cover without assuming a unique numerical root.
The complete cover, its remaining strict-boundary treatment and its ordinary
Lean proof remain independent obligations. No original ledger flag is changed
by this reformulation.
