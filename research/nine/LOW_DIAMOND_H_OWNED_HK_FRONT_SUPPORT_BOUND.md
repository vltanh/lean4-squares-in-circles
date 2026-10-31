# A strict front-support bound in the original H-owned HK row

Date: October 25, 2026.

**Status: complete root hand derivation; separate independent derivation
and final saved-source review passed on October 25, 2026. See
REVIEW_LOW_H_OWNED_HK_FRONT_SUPPORT_BOUND_2026_10_25.md.** This is a scalar
geometric input, not a whole unique-B return exclusion or a new gate.

Keep the original negative-A upper-left diamond chart, true H5/K3/A2/B2,
the intact petal, all nine physical squares, both physical B masks, every
original force and every shared mean. A,K have unique physical circle
corners. Use the strict H-owned n-normal HK row throughout

    q0=6241/1600 <= q=R^2 <= 1105/256.

Use the accepted complete fan and sign-split source:

- LOW_DIAMOND_H_OWNED_HK_RETURN_FAN.md;
- LOW_DIAMOND_H_OWNED_HK_RADIAL_AND_NONNEGATIVE_PROJECTION_EXCLUSION.md.

The original H-frame front-side coordinate is

    N=P dot n=V dot n, cn=c_H dot n=N-1/2.

**Theorem.** The original configuration necessarily has

    N>3/8.

In particular the remaining unique-B negative-cn row has
-1/8<cn<0. No original position or selected normal is changed.

## 1. The two actual circle corners and their opposite transverse signs

Retain all notation of the accepted original row:

    n=(u,v), j=(-v,u) in A's frame,
    0<u<=v, u^2+v^2=1,
    n=(E,d), j=(-d,E) in K's (f,g) frame,
    E>v, d>0, E^2+d^2=1,
    r0=s/E=u+vd/E,
    V=P+r0 j,
    zA=P+(1,1),
    zK=V+f+g.

Here zA and zK are the actual physical circle corners. Put

    S=u+v, A0=E+d.

Both S and A0 belong to [1,sqrt(2)]. Their exact n coordinates are

    zA dot n=N+S, zK dot n=N+A0.                    (1)

Also zA dot j=bu-av<0 from the original a>b and 0<u<=v. The actual
positive j projection of zK is the unchanged identity and bound

    zK dot j=E+v-(av-bu)-tau d
              >u(v-2/5)>0.                        (2)

It follows from a<2, b>3/5, E>v, d<u and tau<1-v, as fully proved
in Section 3.1 of the sign-split source. That calculation itself does
not require cn<=0. Alternatively, under the contradiction assumption
N<=3/8 below, that section's cn<=0 premise holds automatically.

The exact gap between these two opposite j coordinates is

    L_j=(zK-zA) dot j
        =r0+E-d+v-u
        =E+v-(d/E)(E-v)<E+v.                       (3)

No auxiliary circle corner or contact mean replaces either endpoint.

## 2. One elementary lower line for the complete norm interval

For every t in [1,sqrt(2)],

    sqrt(q0-(3/8+t)^2)>14/5-(7/5)t>0.               (4)

To prove this on the whole interval, the exact squared difference is

    q0-(3/8+t)^2-[14/5-(7/5)t]^2
       =-102/25+(709/100)t-(74/25)t^2.              (5)

This is a concave quadratic, so its minimum on the interval occurs
at an endpoint. At t=1 its value is 1/20. At t=sqrt(2) its value is

    (709sqrt(2)-1000)/100>0,

because both compared numbers are positive and

    2*709^2-1000^2=5362>0.

The affine right side of (4) is positive since t<=sqrt(2)<2.
Thus (5) proves that the square-root radicand is positive and proves
(4), with no angle table, polynomial coefficient packet or numerical
extremum.

## 3. The actual two-circle equations contradict N<=3/8

Suppose N<=3/8. The original row has N>0. Equations (1)--(2) and the
two unchanged radius equations give the exact transverse gap

    L_j=sqrt(q-(N+S)^2)+sqrt(q-(N+A0)^2).           (6)

Since q>=q0, N<=3/8 and S,A0>0, equation (4) applies to each term:

    L_j>28/5-(7/5)(S+A0).                          (7)

But the two orthonormal pairs (u,v) and (d,E) satisfy Cauchy's exact
bounds

    7u+12v<=sqrt(193),
    7d+12E<=sqrt(193),
    2sqrt(193)<28.

Consequently

    7(S+A0)+5(E+v)
       =7(u+d)+12(v+E)
       <=2sqrt(193)<28.

Rearranging and using (7) yields L_j>E+v, contrary to (3).
Therefore N>3/8 on the entire original row.

The scalar comparison retains both actual physical circle corners,
the original common support line and every allowed parameter. The
only hypothetical restriction N<=3/8 is used for contradiction; no
pose is moved to a comparison boundary.

This theorem supplies -1/8<cn<0 for the remaining unique-B row after
the accepted nonnegative-cn exit. It does not prove its actual A/K/B
block-pressure inequality or a three-extra completion obstruction.
No gate, new ID, Lean compilation or CI is introduced.

