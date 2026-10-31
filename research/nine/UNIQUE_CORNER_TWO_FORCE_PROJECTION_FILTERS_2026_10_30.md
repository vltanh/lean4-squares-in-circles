# Unique-circle corners give two exact force-projection filters at each endpoint

Date: 2026-10-30. **Complete necessary inequalities; no entire original row
is declared excluded.** These filters retain the actual circle origin and can
be used before reconstructing all corner coordinates in an interval proof.

## 1. General physical-corner theorem

Let e,w be an orthonormal side frame of an actual unit square. Suppose Z is
its unique physical circle corner in the disk centered at zero, so

    |Z|=R,  Z-e and Z-w are actual vertices strictly inside that disk.

Subtract their squared containment inequalities from |Z|^2=R^2. One gets

    Z.e>1/2, Z.w>1/2.                             (1)

Suppose the square's complete circle force is F=lambda*Z, lambda>0. For
any R^2<=Q, (1) gives

    4*Q*(F.e)^2>|F|^2,
    4*Q*(F.w)^2>|F|^2.                           (2)

This uses the actual full force and actual physical corner. It is false to
apply it to an arbitrary selected circle atom when another physical circle
corner is present; the unique-corner premise is retained.

## 2. Full two-force/torque substitution

Suppose the original force and torque equations give

    F=P*e+gamma*d,
    |d|=1, P>0, gamma>0,
    cd=d.e>0, sd=d.w>0,
    k=sd-cd>0,
    x=(gamma/P)*k>0.

Then, without changing any original force magnitude,

    F=(P/k)*(k*e+x*d).

Since P/k>0, both inequalities (2) are equivalent to the following strict
necessary comparisons:

    D=k^2+2*k*x*cd+x^2,
    4*Q*(x*sd)^2>D,                              (3)
    4*Q*(k+x*cd)^2>D.                            (4)

Here cd^2+sd^2=1, and the exact orthogonal decomposition is

    D=(k+x*cd)^2+(x*sd)^2.

The equations contain no P, gamma, force-matrix determinant or small-force
denominator. Closed non-strict versions of (3),(4) are safe necessary filters
on interval enclosures of the original strict domain.

## 3. Rational filters without squaring a wide interval

For Q=1105/256 put K=65/16. The exact comparison

    K^2-(4*Q-1)=61/256>0

and positivity of all original k,x,cd,sd turn (3),(4) into

    x*(K*sd-cd)>k,                               (5)
    K*(k+x*cd)>x*sd.                             (6)

Indeed (3) gives k+x*cd<sqrt(4Q-1)*x*sd<K*x*sd. Equation (4) gives
x*sd<sqrt(4Q-1)*(k+x*cd)<K*(k+x*cd). Thus (5),(6) hold over the entire
domain, including arbitrarily small original positive force magnitudes.

In particular K*sd-cd>0 and x>k/(K*sd-cd). Since sd<1 and cd>0, one has the
coarser whole-domain bound x>k/K=16*k/65. These are necessary offset bounds,
not newly chosen support coordinates.

## 4. Literal simultaneous application to the two D02 endpoints

Use the original A-only Type II side feature of D02.L135 with both B and C
physically unique-circle, retaining all nine squares and the full stars

    A:{V,D,B}, D:{A,V,C}, V:{A,D},
    B:{A,N}, C:{D,N}, N:{B,C}.

The exact source
[TYPE_II_A_ONLY_WHOLE_TRANSVERSE_GAP_AND_EXACT_BOTH_UNIQUE_SIDE_MATRIX_2026_10_29.md](TYPE_II_A_ONLY_WHOLE_TRANSVERSE_GAP_AND_EXACT_BOTH_UNIQUE_SIDE_MATRIX_2026_10_29.md)
supplies all the following unchanged data:

    G_B=P_B*b+gamma*d,
    G_C=-P_C*cvec-gamma*d,
    xB=(gamma/P_B)*kB, kB=d.(wB-b)>0,
    xC=(gamma/P_C)*kC, kC=d.(wC-cvec)>0.

B has actual corner ZB with its adjacent vertices ZB-b and ZB-wB. Thus apply
Sections 1–3 with e=b,w=wB and the original d.

C has actual corner ZC with adjacent vertices ZC+cvec and ZC+wC. Use the
actual frame e=-cvec,w=-wC and direction -d. The projected coordinates are
again cd=d.cvec and sd=d.wC; P=P_C, x=xC, k=kC. This proves the same two
quadratic and two rational filters at C, with no change in its physical mask.

The complete four quadratic necessary inequalities are therefore

    4Q*(xB*(d.wB))^2 >= kB^2+2*kB*xB*(d.b)+xB^2,
    4Q*(kB+xB*(d.b))^2 >= kB^2+2*kB*xB*(d.b)+xB^2,
    4Q*(xC*(d.wC))^2 >= kC^2+2*kC*xC*(d.cvec)+xC^2,
    4Q*(kC+xC*(d.cvec))^2 >= kC^2+2*kC*xC*(d.cvec)+xC^2.

Their strict rational counterparts (5),(6) apply independently at both B and C.
They are cheaper early tests than the two full circle equations and the radial
origin equation. They supplement those equations; none is discarded.

The general theorem also applies in any other graph when the stated actual
frame, physical unique circle corner, complete force vector and full torque
substitution are proved. It does not suppress higher-degree forces or turn a
physical two-corner square into a unique-corner square.

## 5. Scalar forms with every normalization cancelled

The three-variable chart uses positive ratios `0<m<v<1` and `0<w<1` with

    a0=1/sqrt(1+v^2), cY=1/sqrt(1+m^2), W=sqrt(1+w^2),
    b=(-a0,-a0*v), wB=(-a0*v,a0),
    cvec=(-cY*m,cY), wC=(-cY,-cY*m), d=(-1,w)/W.

Define the unnormalized strict sector expressions

    KB=(v-1)+(1+v)*w,
    KC=(1-m)-(1+m)*w.

Their original meanings are `kB=a0*KB/W` and `kC=cY*KC/W`. Direct dot
products give

    d.b   =a0*(1-v*w)/W,  d.wB=a0*(v+w)/W,
    d.cvec=cY*(m+w)/W,    d.wC=cY*(1-m*w)/W.

Thus the two orthogonal components of `kB*b+xB*d` in the B side frame are
the common positive multiple `a0/W` of

    HB1=KB+xB*(1-v*w),
    HB2=xB*(v+w).

The components of `-kC*cvec-xC*d` in the C side frame `(-cvec,-wC)` are
the common positive multiple `cY/W` of

    HC1=KC+xC*(m+w),
    HC2=xC*(1-m*w).

All four scalar components are strictly positive on the original feature.
Canceling the squared positive factors from (3),(4), and using
`4Q-1=1041/64`, proves the exact strict scalar filters

    1041*HB1^2 > 64*HB2^2,
    1041*HB2^2 > 64*HB1^2,
    1041*HC1^2 > 64*HC2^2,
    1041*HC2^2 > 64*HC1^2.                        (7)

These are polynomial necessary inequalities in `(v,m,w,xB,xC)`. They
contain no square root, force normalization or division. Closed versions
with `>=` are safe filters for enclosures of the strict original feature.
The rational unsquared alternatives are equally division free:

    65*HB2 > 16*HB1, 65*HB1 > 16*HB2,
    65*HC2 > 16*HC1, 65*HC1 > 16*HC2.             (8)

Equations (7) are the stronger exact comparisons; (8) can be cheaper when
a wide interval causes dependency loss in squared expressions. Both are
proved uniformly, including near a vanishing original positive force.

The current interval cover and the whole both-unique feature remain open.
These uniform constraints introduce no original gate and change no checkbox.
