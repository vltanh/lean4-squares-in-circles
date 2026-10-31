# Independent full review: the loaded perpendicular-side horizontal-gap bound

Date: October 29, 2026 UTC. Reviewer: block_forests continuation.

**Verdict: PASS unchanged.** I read every line of the 273-line frozen
source and independently reconstructed the complete T2 reduction, all
three scalar comparisons, the full one-variable derivative argument,
both endpoint estimates, and the literal original house caller.
No correction or scope restriction is needed.

I am a noncontributor to this new theorem. I supplied none of its gap
formula, interpolation method, derivative argument, endpoint constants,
or proof steps before reading the frozen manuscript. Root is its author;
house's intended-caller check is correctly identified as integration.

## 1. Exact frozen source and operative pins

The target is

    LOADED_PERPENDICULAR_OWNED_SIDE_CONTACTS_NEAR_VERTICAL_POINT_HORIZONTAL_GAP_BOUND_2026_10_29.md
    273 lines, 9383 bytes
    SHA256 1b172bcef958085c7260015dea7979505767f14da492b3b2e572e5df920da453.

Both printed direct input pins match their unchanged actual files:

| Source | SHA256 | Operative use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Complete actual force, origin torque, and pair-mean convention for the true loaded T2 |
| HOUSE_TC_BOTH_LEAF_INNER_NONPARALLEL_UNIQUE_T_PERPENDICULAR_OWNER_REDUCTION_2026_10_29.md | d79bb4a7a43016e50e23c9878bbcfef27a48487373ee06136a9143d1c4544ce0 | Literal original owned-leaf caller only, including the entire physical-mask and owner cover |

I previously read the complete 399-line physical stress source and had
just independently reconstructed the full 432-line house reduction and
its operative inputs. The latter review remains unchanged at

    REVIEW_HOUSE_TC_INNER_NONPARALLEL_PERPENDICULAR_T_BLOCK_FORESTS_2026_10_29.md
    SHA256 b96c8f566fac489077a467395cd78b8bc9fe8d2cefd3744a40c831d21b7d45a7.

The new main theorem uses no other physical or selected-normal result.
In particular no fixed-singleton selection is an assumption in its
general statement, and no upper bound on R is used in its proof.

## 2. Complete actual hypotheses and retained endpoints

The theorem starts with a true loaded degree-two unit T and exactly one
physical circle corner, not merely one nonzero coefficient in a larger
physical mask. Its two original incoming pair forces have positive
magnitudes lambda and gamma along actual perpendicular T-owned axes

    U=(-C,S), W=(S,C), 0<S<C, C^2+S^2=1.

The unchanged real square and contact means are

    T=H+[0,1]U+[0,1]W,
    P=H+delta*W=(h,V), F=H+eta*U,
    0<=eta,delta<=1,
    0<=h<1/60, 0<V<=1, R^2>=17/4.

These hypotheses retain every original side-mean endpoint. Neither
neighbor's load, positive degree, physical mask, or other forces enter.
The general result makes no singleton premise and does not select new
contact owners or applications.

The actual horizontal separation is exactly

    (P-F)_x=eta*C+delta*S>=0.

The asserted bound on this actual quantity is c_*<13/20. The proof
does not substitute an interval length or a surrogate normal parameter
for that original contact difference.

## 3. The full force and torque equations give the exact gap function

The unique circle vector is a positive multiple of lambda*U+gamma*W,
so both of its own components are positive. Containment then puts that
circle corner on both maximum own faces. For example a positive own
coordinate on a minimum face could not be farthest: the corresponding
maximum-face corner has a strictly larger squared norm. Consequently

    Z=H+U+W=P+U+(1-delta)*W.

Set A=P.U=V*S-h*C and B=P.W=V*C+h*S. The original assumptions give
B>0. Let X=A+1 and Y=Z.W=B+1-delta. The actual force equation and
the actual circle equality give

    X=Z.U>0, Y>0, lambda/gamma=X/Y,
    Y=sqrt(R^2-X^2).

For the moment identity, det(U,W)=-1 and P=A*U+B*W. Hence
det(P,U)=B and det(F,W)=-(A+eta). The unchanged full T2 torque is

    lambda*B=gamma*(A+eta),
    eta=(X/Y)*B-A.

The geometric expression for Z also gives delta=1+B-Y. Inserting
these exact identities into eta*C+delta*S yields

    c_*=h+S+C*B*X/Y-S*Y,

because -C*A+S*B=h. This reconstruction neither assumes finite
concurrence nor moves either real mean. The cases eta=0, eta=1,
delta=0, and delta=1 remain in the equations whenever an actual star
can satisfy them.

## 4. The complete scalar comparison domains have positive denominators

For r=R^2 define the target's explicit function Phi with

    X=1+V*S-h*C, B=V*C+h*S, Y=sqrt(r-X^2).

Across every comparison interval, 0<=h<1/60, 0<V<=1,
0<S<1/sqrt(2), and r>=17/4. Thus X>59/60 and B>0. Also

    Y^2>=17/4-(1+1/sqrt(2))^2=11/4-sqrt(2)>0.

The change from V to 1, the integration from 0 to the actual h,
and the radius comparison from 17/4 to r all stay within this same
strictly positive denominator domain. The proof does not require any
intermediate scalar values to describe a physically realizable square.

Direct differentiation independently gives

    Phi_V=X/Y+C*B*S*r/Y^3>0,
    Phi_h=1-C^2*B*r/Y^3<=1,
    Phi_r=-C*B*X/(2*Y^3)-S/(2*Y)<0.

For the h derivative, the direct C*S*(X/Y) and -S*C*(X/Y) terms
cancel exactly. Integrating Phi_h<=1 is valid in the stated direction
because h>=0; the theorem does not claim that bound for negative h.
The three comparisons therefore give, with all equality walls retained,

    c_*<=h+Phi(0,1,17/4;S).

No mean constraint is needed in the enlarged scalar comparison domain;
the actual mean identities were used only at the original entry.

## 5. Full reconstruction of the one-variable maximum argument

At h=0,V=1,r0=17/4, put x=S and X0=1+x. Direct algebra gives

    f(x)=x+[X0^2-r0*x]/sqrt(r0-X0^2),
    0<=x<=1/sqrt(2).

Both endpoints are included for comparison. The denominator is bounded
away from zero on this entire interval. Writing Y0=sqrt(r0-X0^2),
I independently differentiated the expression to obtain

    f'(x)=1+[3*r0*X0-r0^2-X0^3]/Y0^3,
    f''(x)=3*r0*[X0^2-r0*x]/Y0^5.

The second numerator is N(x)=1-(9/4)*x+x^2. Its derivative is
2*x-9/4<0 throughout the interval. N is positive at zero and negative
at 1/sqrt(2), where its value is (12-9*sqrt(2))/8. It therefore
has exactly one zero. Thus f' increases first and decreases after
that unique transition; it has a single maximum.

The right-endpoint derivative is strictly positive. There

    Y0^2=11/4-sqrt(2),
    3*r0*X0-r0^2-X0^3=(74*sqrt(2)-125)/16<0.

Both sides of 16*Y0^3>125-74*sqrt(2) are positive. Expanding their
squared difference gives exactly

    12180*sqrt(2)-17029>12180*(7/5)-17029=23>0.

This proves the required derivative sign. On the later decreasing
part, f' is at least its positive value at the right endpoint. On
the earlier increasing part it can cross zero at most once, and only
from negative to positive. Hence f has no interior local maximum.
Its maximum on the whole closed interval is attained at an endpoint.
This implication does not mistakenly infer convexity of f everywhere;
the change of sign of f'' is explicitly retained.

## 6. Both endpoint estimates are strict and have exact reserves

At zero, f(0)=2/sqrt(13)<19/30. The positive squared reserve is

    13-(60/19)^2=1093/361>0.

At the right endpoint the numerator N is negative. From sqrt(2)>24/17,

    Y0^2<91/68<49/36,

with last reserve 7/306; therefore Y0<7/6. Dividing the negative
numerator by this larger denominator gives a strict upper bound,
with the correct inequality direction:

    f(1/sqrt(2))<(36-13*sqrt(2))/28
      <75/119<19/30.

The radical squared reserve for sqrt(2)>24/17 is 2/289, and the
final rational reserve is 11/3570. Thus the endpoint maximum argument
proves f(x)<19/30 on the entire closed interval, rather than only
at the actual strict-angle points.

Combining this with the full comparison and h<1/60 gives

    c_*<1/60+19/30=13/20.

The conditional consequence for a caller with c_*^2+s_*^2=1 and
s_*>0 is also correct: 1-(13/20)^2-(3/4)^2=3/200>0 gives s_*>3/4.

## 7. Exact original house transfer and scope boundary

In the accepted owned-leaf nonparallel inner residual, the same actual
T has true positive degree two, one physical circle corner, both
perpendicular T-owned contacts, and original open eta,delta. Its actual
P=(epsilon,1-q) satisfies h in (0,1/60) and V in (5/8,1), and its
unchanged radius satisfies R^2=(2+epsilon)^2+1/4>17/4.

In the shallow range 0<S0<C, the substitution S=S0 is literal. The
original D identity c=eta*C+delta*S0 is exactly this theorem's
horizontal gap, not a newly introduced proxy. The original c,s>0
and c^2+s^2=1 then give c<13/20 and s>3/4.

All A4,D3,C2 forces, the genuine leaf, the chord and all nine physical
units remain. The input's entire mask and owner cover was established
before this gap bound is called. The new theorem alone is a necessary
condition, as stated; it does not claim the final shallow contradiction
or close a whole original TC.S row.

The displayed derivatives and expansions were reconstructed algebraically,
and the decisive radical and rational reserves were checked with exact
fractions. No numerical pose, sampled angle mesh, or computational
packing certificate is used. The target and both operative inputs were
left unchanged. This review edits no ledger, roadmap, handoff, Lean
source, CI state, or remote object.
