# A near vertical contact bounds the whole horizontal gap of a loaded perpendicular two-side star

Date: October 29, 2026 UTC. Author: root continuation.

**Status: complete proposed uniform hand theorem, frozen for separate
full independent review.** The actual horizontal separation of the two
original perpendicular T-owned contacts is strictly less than 13/20.
The theorem uses the whole loaded T2 star and its one physical circle
corner. It retains the complete original side-mean intervals, including
their endpoints. It imposes no force or degree condition on either
neighbor, and needs no upper bound on the containing radius.

The literal original owned-leaf house caller is given at the end. This
bound alone is a necessary condition, not a whole original-family exit.

## 1. Complete actual geometric and force hypotheses

Keep an actual closed unit square T in a circle about the unchanged
O=0, with

    R^2>=17/4.

Its true positive degree is two, and its complete original circle mask
has exactly one physical circle corner with positive total coefficient.
Both original pair normals are T-owned perpendicular side axes. Write
their incoming forces and actual own axes as

    lambda*U, gamma*W, lambda,gamma>0,
    U=(-C,S), W=(S,C),
    0<S<C, C^2+S^2=1.

Thus U points to the upper left and W to the upper right. The complete
actual square and original means have the form

    T=H+[0,1]U+[0,1]W,
    P=H+delta*W,
    F=H+eta*U,
    0<=delta,eta<=1.

P and F are the original minimum-U and minimum-W applications. They
may be endpoints of their actual shared segments. No singleton premise,
new owner selection or full-degree simplification is used in this
theorem. The original full T force and origin moment equations remain.

Suppose the same actual P has coordinates

    P=(h,V), 0<=h<1/60, 0<V<=1.

Define the actual nonnegative horizontal gap

    c_*=(P-F)_x=eta*C+delta*S.

**Theorem.** Every such complete actual star satisfies

    c_*<13/20.                                        (1)

In particular, if the caller already has c_*^2+s_*^2=1 with s_*>0,
then s_*>3/4, because 1-(13/20)^2=231/400>9/16.

All coordinates describe the actual fixed units about their original
circle center. The scalar comparisons below are inequalities between
explicit real functions; they are not deformations or sampled poses of
the packing, and do not change a selected normal or original mean.

## 2. The full T2 gives an exact function for the original gap

The full original force equation makes the unique circle vector a
positive multiple of lambda*U+gamma*W. Its own components are both
positive. A unique farthest corner has positive own coordinates exactly
at its two maximum faces, so the actual circle corner is

    Z=H+U+W=P+U+(1-delta)*W.

Set

    A=P.U=V*S-h*C,
    B=P.W=V*C+h*S>0,
    X=A+1,
    Y=Z.W=B+1-delta>0,
    p=lambda/gamma.

The circle force and radius give

    Z.U=X, p=X/Y,
    Y=sqrt(R^2-X^2).                                  (2)

The entire original T2 origin moment is

    lambda*det(P,U)+gamma*det(F,W)=0.

Since det(U,W)=-1, its scalar form is

    lambda*B=gamma*(A+eta),
    eta=p*B-A.                                         (3)

Also delta=1+B-Y. Substituting in the unchanged horizontal gap gives

    c_*=C*(p*B-A)+S*(1+B-Y)
       =h+S+C*p*B-S*Y,                               (4)

using -C*A+S*B=h. This is an identity for the actual original means,
not a new choice of application point. No finite-concurrence assumption
is required to derive it.

## 3. Three complete scalar monotonicities

Write r=R^2 and let

    Phi(h,V,r;S)=h+S+C*B*X/Y-S*Y,
    C=sqrt(1-S^2),
    X=1+V*S-h*C, B=V*C+h*S, Y=sqrt(r-X^2).

Throughout the comparisons below,

    0<=h<1/60, 0<V<=1, 0<S<1/sqrt(2), r>=17/4.

Thus X>59/60, B>0 and

    Y^2>=17/4-(1+1/sqrt(2))^2>0.

The entire intervals from the actual V to 1, from 0 to the actual h,
and from 17/4 to the actual r stay within this explicit positive
denominator domain. No physical realization is asserted at an
intermediate scalar value.

For fixed h,r,S, differentiation of (4) gives exactly

    dPhi/dV=p+C*B*S*r/Y^3>0.                          (5)

For fixed V,r,S, the two direct h terms from p and Y cancel, leaving

    dPhi/dh=1-C^2*B*r/Y^3<=1.                         (6)

For fixed h,V,S, the radius derivative is

    dPhi/dr=-C*B*X/(2*Y^3)-S/(2*Y)<0.                (7)

These signs give the entire bound

    c_*=Phi(h,V,r;S)
        <=Phi(h,1,r;S)
        <=h+Phi(0,1,r;S)
        <=h+Phi(0,1,17/4;S).                         (8)

Each weak endpoint has been retained. The final strict result will come
from h<1/60 and the full scalar estimate in the next section.

## 4. The entire remaining one-variable function is bounded at its endpoints

Put r0=17/4, x=S, X0=1+x and Y0=sqrt(r0-X0^2). At h=0,V=1,
formula (4) simplifies exactly to

    f(x)=Phi(0,1,r0;x)
        =x+[(1+x)^2-r0*x]/sqrt(r0-(1+x)^2),
    0<=x<=1/sqrt(2).                                 (9)

We include both comparison endpoints, even though the actual orientation
is strict. Direct differentiation gives

    f'(x)=1+[3*r0*X0-r0^2-X0^3]/Y0^3,
    f''(x)=3*r0*[X0^2-r0*x]/Y0^5.                   (10)

The numerator controlling the second derivative is

    N(x)=1-(9/4)*x+x^2.

It is strictly decreasing on the whole interval, is positive at zero,
and at the other endpoint equals

    N(1/sqrt(2))=(12-9*sqrt(2))/8<0.

Hence it has exactly one zero there. The derivative f' first increases
and then decreases. At the right endpoint it is strictly positive, as
we now check with exact constants.

At x=1/sqrt(2),

    Y0^2=11/4-sqrt(2),
    3*r0*X0-r0^2-X0^3=(74*sqrt(2)-125)/16.

The latter numerator is negative. Both sides of the comparison
16*Y0^3>125-74*sqrt(2) are positive, and their squared difference is

    256*Y0^6-(125-74*sqrt(2))^2
       =12180*sqrt(2)-17029
       >12180*(7/5)-17029=23>0.                     (11)

Thus f' at the right endpoint is positive. Since f' decreases only
after its unique maximum and is still positive at that endpoint, any
zero of f' can only occur in its earlier increasing part, where it
changes from negative to positive. There is no interior local maximum
of f. Its maximum on this whole closed interval is at one of the two
endpoints. This is a continuous derivative argument, not an angle mesh.

At zero,

    f(0)=2/sqrt(13)<19/30.

The last positive squared comparison is 13>(60/19)^2. At the other
endpoint, Y0<7/6 and N<0, so

    f(1/sqrt(2))
       <sqrt(2)/2-(9*sqrt(2)-12)/(8*(7/6))
        =(36-13*sqrt(2))/28
        <75/119<19/30.                              (12)

Here sqrt(2)>24/17 gives the second strict inequality. The bound
Y0<7/6 follows from

    Y0^2<11/4-24/17=91/68<49/36.

The final exact reserve is

    19/30-75/119=11/3570>0.

Both endpoint bounds and the complete derivative argument prove

    f(x)<19/30 for every 0<=x<=1/sqrt(2).              (13)

Combining (8),(13) with the actual h<1/60 yields

    c_*<1/60+19/30=13/20.

This proves the full theorem, with all original side means and either
comparison orientation endpoint treated explicitly.

## 5. Literal original house caller and exact dependency boundary

The complete accepted original inner-nonparallel reduction gives the
owned genuine-leaf chart

    h=epsilon in (0,1/60), V=1-q in (5/8,1),
    R^2=(2+epsilon)^2+1/4>17/4,
    T=H+[0,1]U+[0,1]W,
    P=H+delta*W=(h,V), F=H+eta*U,
    0<eta,delta<1,
    N=AT=lambda*U, G=DT=gamma*W,
    T has one physical circle corner and true degree two.

In its shallow range 0<S0<C, put S=S0. Its actual D-to-A coordinate
identity is

    c=eta*C+delta*S0, c^2+s^2=1, c,s>0.

Every hypothesis above is therefore literal, and the entire original
shallow system satisfies

    c<13/20, s>3/4.

The A4, D3, C2, real genuine leaf, positive chord, all nine physical
units and both original open T means remain. The original force groups
are not contracted or shortened. This is a necessary full-domain bound;
the final shallow-house contradiction is a separate obligation.

| Complete source | SHA256 | Literal scope |
| --- | --- | --- |
| HOUSE_TC_BOTH_LEAF_INNER_NONPARALLEL_UNIQUE_T_PERPENDICULAR_OWNER_REDUCTION_2026_10_29.md | d79bb4a7a43016e50e23c9878bbcfef27a48487373ee06136a9143d1c4544ce0 | Entire original owned-leaf caller, actual unique T2, both genuine T side owners and all original means |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original full T force and origin moment equations and physical applications |

Root fully read the complete two inputs and the complete separate
noncontributor review of the first source at
b96c8f566fac489077a467395cd78b8bc9fe8d2cefd3744a40c831d21b7d45a7.
Root contributed two earlier simplifications to that input. The new
gap formula, full scalar monotonicities and endpoint proof above are
root's contribution and need a separate independent noncontributor
review. House checked the intended original caller while constructing
its separate final shallow exit; that integration is not represented
as an independent review of this theorem.

No original fine, parent, coarse or equality flag changes here. No
original physical pose, force, selected normal, mean or coefficient is
changed. No numerical sampling, finite packing certificate, Lean/Lake
compilation, CI/workflow dispatch, remote mutation or merge was used.
