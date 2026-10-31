# Three genuine shares cannot occur in the all-unique alternating C6

Date: October 25, 2026.

**Status: complete hand proof with an exact whole-angle certificate;
independent root full-source, original-scope, analytic and complete
arithmetic review passed on October 25, 2026. See
REVIEW_SIX_CYCLE_THREE_SHARED_MATCHING_2026_10_25.md. No roadmap gate,
accepted count, physical force or application mean changes here.**

**Current scalar proof:** `SIX_CYCLE_THREE_SHARED_MATCHING_TABLE_FREE.md`
replaces the entire 45-coefficient angular certificate with an elementary
half-angle/Taylor-variance argument over the whole closed angle triangle
and every positive force triple. Independent source/scope review passed:
`REVIEW_C6_THREE_SHARE_TABLE_FREE_2026_10_25.md`. Sections 1--2 below
remain the physical derivation. Sections 3 onward retain the older
certificate proof as a historical alternative only. The current
three-share scalar lemma needs no Bernstein coefficient packet.
The separate double-shared-channel prerequisite is still retained.

Retain the original alternating six-cycle with three positively loaded
units S_i and three unloaded side-normal transmitters W_i. Each S_i has
one physical circle corner z_i. Keep the true degree-two equations of
all six bodies, all original positive pair magnitudes, every physical
contact and original mean, the complete transverse position interval of
each transmitter, and all three additional packing units. Work throughout

    79/40 <= R <= sqrt(1105)/16.

Use the already accepted whole-domain conclusions of
SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md and
SIX_CYCLE_DOUBLE_SHARED_CHANNEL_EXCLUSION.md. The former gives the
original proper counterclockwise force triangle, with turns

    pi/2 < theta_i <= 3pi/4, sum_i theta_i=2pi,

and at most one genuinely shared interface at each loaded body. The latter
gives at most one genuinely shared interface at each transmitter. Both
retain actual shared mean endpoints.

**Theorem.** The entire family with three genuine shared interfaces is
impossible. In fact its true force and support identities imply R<79/40,
without imposing any condition on the original transmitter positions or
the three additional units.

Together with the already complete all-singleton exclusion, the accepted
strict-turn normal form and the double-shared-channel exclusion, this
leaves exactly one or two genuine shared interfaces in any remaining
all-unique C6. This is a whole contact-type reduction, not a proof of the
remaining three-extra completion capacity or a new gate.

## 1. The complete three-share matching and its reflection

There are three loaded and three transmitter vertices in the actual
alternating contact cycle. With at most one shared interface incident at
each vertex, three shared edges form a perfect matching. The six-cycle
has exactly two such matchings: every S_i shares its incoming interface,
or every S_i shares its outgoing interface. This is a graph consequence
of the original six physical interfaces; it does not identify coincident
means or replace a positive-length shared contact by a singleton.

It suffices to consider the incoming matching. To cover the other one,
reflect the complete physical packing across a line through the origin
and reverse the cyclic labeling. Both changes together preserve the
counterclockwise force-polygon convention and turn the outgoing matching
into the incoming matching. More explicitly, if T is the orthogonal
reflection, set

    S'_i=T S_(-i),
    f'_i=-T f_(-i-1), mu'_i=mu_(-i-1).

Then F'_i=f'_(i-1)-f'_i=T F_(-i), the new turn is theta_(-i), and the
actual incoming/outgoing applications are interchanged by the reflection.
Every original magnitude, mean, circle corner, transmitter position and
completion unit is carried along. Nothing is selected after extraction.

In the incoming matching write the unchanged forces as

    f_i=mu_i*n_i, mu_i>0, |n_i|=1,
    F_i=f_(i-1)-f_i=k_i*z_i, k_i>0.

The actual side-channel displacement is still

    p_(i+1)^- - p_i^+ = n_i.                         (1)

## 2. An exact force-value formula retaining every shared mean

The complete normal form in
SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md gives, for an incoming shared
interface at S_i,

    u_i=J n_(i-1), v_i=n_(i-1),
    n_i=sin(theta_i)*u_i+cos(theta_i)*v_i,
    z_i=p_base+v_i,
    p_i^-=p_base+t_i*u_i, p_i^+=p_base+u_i,
    0<=t_i<1.                                      (2)

Here t_i is the actual original shared mean. The strict upper bound is
the already proved distinctness of the two applications, not a new mean
choice. The endpoint t_i=0 remains. The physical far-corner choice in
(2) is also forced: F_i has negative u_i component and positive v_i
component, so the unique circle corner is the minimum-u, maximum-v
corner. The theta_i=3pi/4 endpoint is fully included.

Consequently the two original support terms are exactly

    f_(i-1) dot (z_i-p_i^-)=mu_(i-1),
    f_i dot (z_i-p_i^+)=mu_i[cos(theta_i)-sin(theta_i)].

The actual t_i cancels because n_(i-1) is perpendicular to the shared
side. This is an identity at the original mean, not replacement by an
endpoint. Summation by parts using (1), or equivalently Section 2 of the
accepted support-functional source, therefore gives

    R*sum_i |F_i|
      =sum_i mu_i[2+sin(theta_i)-cos(theta_i)].       (3)

The term R|F_i| uses the actual positive unique-circle load at S_i.
No two-corner mask or unequal radial load is put into this formula.

The rest of the proof is the following independent weighted triangle
inequality, on a closed enlargement of the entire actual turn domain.

**Scalar lemma.** If mu_i>0 and

    pi/2 <= theta_i <= 3pi/4, sum_i theta_i=2pi,

then, with K=79/40,

    sum_i mu_i[2+sin(theta_i)-cos(theta_i)]
      < K*sum_i sqrt(mu_(i-1)^2+mu_i^2
                         -2mu_(i-1)*mu_i*cos(theta_i)).       (4)

In particular the lemma includes every weak angle boundary, even those
already excluded from the original physical family.

## 3. Historical alternative: a force-chord lower bound

The inequality is homogeneous in the mu_i. For its calculation normalize
sum_i mu_i=1. This is only a normalization of a scalar inequality; the
physical certificate itself remains unchanged.

Set

    s_i=sin(theta_i/2),
    D_i=sqrt(mu_(i-1)^2+mu_i^2-2mu_(i-1)*mu_i*cos(theta_i)),
    c_*=3/40, sigma=1/sqrt(2).

For positive a,b and s in [0,1], concavity of the square root between
s^2 and 1 gives the elementary full-interval bound

    sqrt((a+b)^2*s^2+(a-b)^2*(1-s^2))
      >=s(a+b)+(1-s)*(a-b)^2/(a+b).                (5)

Indeed divide by a+b and put z=(a-b)^2/(a+b)^2 in [0,1]. The inequality
is sqrt(s^2+(1-s^2)z)>=s+(1-s)z, the chord inequality for a concave
function. Every denominator is positive.

On the full angle interval,

    1-s_i>c_*,
    s_i>=sigma-(3/10)cos(theta_i).                  (6)

For the first bound, s_i<=sin(3pi/8)<37/40. Squaring positive quantities
reduces the last strict comparison to 569>400sqrt(2); its exact squared
reserve is 569^2-2*400^2=3761>0.

For the second bound put x=-cos(theta_i) in [0,sigma]. Both sides are
positive, and

    (1+x)/2-[sigma+(3/10)x]^2
       =x[1/2-(3/5)sigma-(9/100)x]
       >=x[1/2-(69/100)sigma]>=0.

The last bracket is strictly positive because 50sqrt(2)>69, with exact
squared reserve 2*50^2-69^2=239>0. Equality at x=0 is harmless and is
retained.

Apply (5)--(6) to every force chord. Since mu_(i-1)+mu_i<=1,

    sum_i D_i
      >=sum_i mu_i(s_i+s_(i+1))
           +c_* sum_i (mu_i-mu_(i-1))^2
      =sum_i mu_i(s_i+s_(i+1))
           +3c_* sum_i (mu_i-1/3)^2.              (7)

The last identity is the exact three-variable identity under sum mu=1.
No upper or lower ratio of the original positive magnitudes is assumed.

Define

    q_i=K*sqrt(2)-2-sin(theta_i)
             +(163/400)cos(theta_i)
             -(237/400)cos(theta_(i+1)),
    qbar=(q_0+q_1+q_2)/3,
    xi_i=mu_i-1/3.

Here 163/400=1-(3/10)K and 237/400=(3/10)K. Using the second bound
in (6), equation (7) gives

    K*sum D_i-sum mu_i[2+sin(theta_i)-cos(theta_i)]
      >=qbar+sum_i xi_i(q_i-qbar)+3Kc_* sum_i xi_i^2
      =3Kc_* sum_i [xi_i+(q_i-qbar)/(6Kc_*)]^2
           +qbar-sum_i(q_i-qbar)^2/(12Kc_*).        (8)

All weights have now been eliminated by a complete-square inequality.
Since 12Kc_*=711/400, strict positivity of the following two-angle
quantity is sufficient:

    B=(711/400)*sum_i q_i-3*sum_i q_i^2+(sum_i q_i)^2>0.       (9)

Indeed the last two terms of (8) equal B/(36Kc_*), with positive
denominator. Sections 4--5 prove (9) on the entire closed turn triangle.

## 4. A single rectangle covers the whole angular domain

Put alpha=pi-theta_0 and beta=pi-theta_1. Then

    alpha,beta>=pi/4, alpha+beta<=3pi/4,
    theta_2=alpha+beta.

These inequalities also imply alpha,beta<=pi/2. The entire closed
triangle is covered by the following single unit rectangle:

    k=sqrt(2)-1, x,y in [0,1],
    t=k*x, H=1+k^2*x, j=k*(1-x)*y,
    alpha=pi/4+2atan(t),
    beta=pi/4+2atan(j/H).                           (10)

For completeness, after choosing alpha the allowed half increment of
beta is between zero and pi/8-atan(t). Its upper tangent is

    tan(pi/8-atan(t))=(k-t)/(1+k*t)=k*(1-x)/H.

Thus y in [0,1] covers every allowed beta, including both boundaries.
At x=1 the allowed beta is pi/4 and all y give that same endpoint.
No angular subdivision, sampled pose or deleted boundary is involved.

The following explicit polynomials all lie in Q(sqrt(2))[x,y]:

    Da=1+t^2, Db=H^2+j^2,
    ca=(1-2t-t^2)/sqrt(2),
    sa=(1+2t-t^2)/sqrt(2),
    cb=(H^2-j^2-2Hj)/sqrt(2),
    sb=(H^2-j^2+2Hj)/sqrt(2),
    S=sa*cb+ca*sb, C=ca*cb-sa*sb, L=Da*Db.

They satisfy the exact polynomial identities

    ca^2+sa^2=Da^2,
    cb^2+sb^2=Db^2,
    S^2+C^2=L^2.

The complete sine and cosine numerators for the three theta_i, in order,
are

    S_i=(sa*Db, sb*Da, S),
    C_i=(-ca*Db, -cb*Da, C).

Their common denominator is L. Since Da>0, H>0 and Db>0 throughout
the whole rectangle, L is strictly positive, including every boundary.

Define the three polynomial numerators

    Q_i=(K*sqrt(2)-2)*L-S_i
               +(163/400)C_i-(237/400)C_(i+1),
    T=Q_0+Q_1+Q_2,
    G=(711/400)*L*T-3*(Q_0^2+Q_1^2+Q_2^2)+T^2.     (11)

Then Q_i=L*q_i, and the full cleared identity is exactly

    G=L^2*B.                                      (12)

There is no division by an angular endpoint or a possibly zero trigonometric
factor. The positive factor L^2 is the only normalization in (12).

## 5. Complete exact sign certificate, including the inverse identity

The polynomial G in (11) has degrees (8,4) in x,y. Write its ordinary
coefficients as g_rs and set, for 0<=i<=8 and 0<=j<=4,

    b_ij=sum_(r<=i,s<=j) g_rs
            *binom(i,r)/binom(8,r)*binom(j,s)/binom(4,s).     (13)

The exact coefficient computation gives every one of the 45 values

    b_ij>1/100.                                   (14)

For a compact complete sign record, the exact integers floor(1000*b_ij),
one row for each i=0,...,8 and columns j=0,...,4, are

```text
 [55,17,133,273,76]
 [149,73,117,185,50]
 [201,112,116,144,70]
 [212,135,127,143,122]
 [187,147,149,173,194]
 [141,148,177,220,271]
 [95,145,200,261,328]
 [81,140,200,259,319]
 [144,144,144,144,144]
```

The full exact ordinary and Bernstein coefficients, each recorded as a
rational pair r+s*sqrt(2), are retained in
SIX_CYCLE_THREE_SHARED_MATCHING_CERTIFICATE.json. They are independently
reconstructible from (10)--(13), without relying on the floor table.

The complete inverse identity is

    G(x,y)=sum_(i=0..8,j=0..4) b_ij*binom(8,i)*binom(4,j)
               *x^i*(1-x)^(8-i)*y^j*(1-y)^(4-j).             (15)

In ordinary coefficient form, every g_rs is reconstructed by

    g_rs=sum_(i<=r,j<=s) b_ij*binom(8,i)*binom(8-i,r-i)
                    *binom(4,j)*binom(4-j,s-j)*(-1)^(r+s-i-j).

SIX_CYCLE_THREE_SHARED_MATCHING_CHECK.py rebuilds all defining
polynomials, all 45 coefficients, every coefficient of (15), all exact
floor values, and the three full trigonometric identities above. It also
checks the alternative exact variance identity

    3*sum_i Q_i^2-T^2=sum_i (Q_i-Q_(i+1))^2

and both integer reserves in (6). Its standard-library Q(sqrt(2))
comparison uses rational squares with the signs of the rational and
sqrt(2) parts retained; no decimal sign or external algebra package is a
premise. Regeneration and readback match the saved certificate exactly.

The tensor Bernstein basis in (15) is nonnegative and sums to one on the
entire closed unit rectangle. Hence (14) gives G>1/100 there. The positive
normalization (12) proves (9) on the whole original turn triangle.
Equation (8) now proves the strict weighted inequality (4) for every
positive force triple.

## 6. Return to the unchanged physical C6

The force chords in (4) are exactly |F_i| for the original
F_i=f_(i-1)-f_i. Combining (3) and (4) gives

    R*sum_i |F_i| < (79/40)*sum_i |F_i|.

Each F_i is a positive actual circle load, so the denominator is positive.
Thus R<79/40, contrary to the original radius window. Reflection in
Section 1 covers the other perfect matching. This excludes all three
genuine shares, including every surviving angle endpoint and every
original shared mean endpoint.

No transmitter was moved, centered or assigned a singleton port chord.
The proof is independent of its transverse position, so its full original
slider remains covered. No completion square is removed or constrained
to a preferred free-space region. The contradiction already occurs in
the true six-body equations.

The accepted all-singleton theorem handles zero shares; the accepted
normal form gives at most three, and the present theorem excludes three.
Every remaining all-unique/shared alternating C6 therefore has precisely
one or two genuine shares, with at most one at each loaded body and each
transmitter. Their three-extra completion-capacity problem remains open.

No new gate, numerical-sign inference, angle mesh, force reassignment,
physical mask collapse, Lean compilation or CI is used.

