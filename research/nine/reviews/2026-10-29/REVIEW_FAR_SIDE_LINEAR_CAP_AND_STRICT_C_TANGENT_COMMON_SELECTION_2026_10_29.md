# Independent full review of the far-side linear cap and strict tangent reduction

Date: October 29, 2026 UTC.
Reviewer: common-selection continuation.
Authors of the reviewed construction: far-vertex continuation and root
continuation.

**Verdict: PASS at the exact revised frozen source below.** The complete
original far-side domain has e<1/2 and z>8/15+4e/7. Along the entire
justified scalar connecting interval, the unchanged C tangent formula
has derivative strictly less than -1/7. Consequently the whole original
tangent is strictly below the explicitly printed one-variable endpoint
function. The remaining inequality that would put that function at most
1/2 is not proved, and this review grants no whole far-side closure.

One boundary correction was requested and made during review: the
Section4 comparison interval includes e=0, so H<S=1/J<1 was replaced
by H<S=1/J<=1. The strict conclusion H<1 still follows. No scalar
constant, proof identity, physical premise or derivative estimate changed.

## 1. Exact source, complete reading and independence

Reviewed source:

    TYPE_II_FAR_SIDE_LINEAR_CAP_AND_STRICT_C_TANGENT_MONOTONIC_REDUCTION_2026_10_29.md
    11,347 bytes
    SHA256 90950427e5f69369fd9bd6a6295552355b2abf33954aa989cacb094ac98a7ffe

The earlier pre-review source had SHA256

    0be4e68268285625c0cda749e10eb4c50393854db9636b30f268ce269a1b149a.

The final pin is the source after the single closed-endpoint wording
repair described above. This report applies to the final pin.

I read the entire new manuscript and both complete direct sources,
not only their advertised exports or summaries:

| Complete direct source | Bytes | SHA256 |
| --- | ---: | --- |
| TYPE_II_FAR_RETURN_SIDE_CHANNEL_EXCLUDES_BOTH_PARALLEL_LOADED_ENDPOINTS_2026_10_29.md | 14,251 | e573ec4e567bb3e255ddbc9348b24dd4780651beebd1f3ea713e949930929b68 |
| UNIVERSAL_UNIT_SQUARE_CAP_AND_COMPLETE_TYPE_II_FAR_RETURN_DIAGONAL_EXCLUSION_2026_10_29.md | 18,949 | f4f2f293e038ea9f42dc8572cb8f216c9b9718a8fb14c4ac215232efcaf34e3c |

I supplied no linear-cap constant, concavity argument, slope derivative,
positive-q polynomial, connecting-interval proof or final endpoint
formula in this source. My earlier generic loaded-endpoint work is
separate; it does not make me an author of these scalar constructions.
The corrected e=0 inequality was identified as a review boundary issue.
The substantive two-author scalar proof remains the authors' work.

The existing full reviews and original input boundaries of the two
direct sources remain separate. Reading their whole statements here
checks the literal imported hypotheses and formulas; it does not
claim a new recursive review of every earlier repository result or
close their common-selection prerequisites.

## 2. Literal original entry and the exact force-ratio substitution

The reviewed source keeps the complete far-A-vertex D-owned Type II
row, with A,D unloaded true3, V,B,C loaded true2, and N the unchanged
unloaded true2 side transmitter. Every original hub force, torque,
selected normal, physical corner, zero individual coefficient and
full side mean remains. Loaded N in L1345 is not assigned this
unloaded side equation.

The complete direct far source supplies

    e=ell, J=sqrt(1+e^2), A=1+e, B=1-e,
    S=1/J, d=B/J, L=A/J,
    H^2+k^2=1, H,k>0, H<S,
    q=A*k/H-1>0,
    v=k+e*H<1,
    k<1/sqrt(1+q^2).

The actual V radial direction gives

    z=(L-H*J^2)/d=(A-H*J^3)/B,
    Z=R*(1,z)/sqrt(1+z^2).

Its d0 component is positive. The original C cap supplies
Z.n>L-1/60>0, so z>0 is literal. The source's scalar u=z-e
satisfies exactly

    u=J^2*(1-J*H)/B>0.

Substituting S=1/J into the full original ratio

    p=S^3*B*(q+e)/(S-H)

gives p=(q+e)/u. Thus, with T=q+e,

    delta_D=p*v/(1+p)=T*v/(T+u).

The original geometric C application is Q_C=P-n-delta_D*d0,
while P=Z-(d,L). Its unchanged d0 coordinate is therefore

    Q_C.d0=R/sqrt(1+z^2)-B/J-delta_D.

These identities use the original full D-torque mean. No mean or
force ratio is introduced as an independent variable.

## 3. The whole original e interval shrinks to (0,1/2)

I checked the strict v<1 squaring carefully. Since k= sqrt(1-H^2)
and 1-eH is positive,

    k+eH<1  implies  H*J^2>2e.

Consequently z<1, using L-d=2e/J<2e. The sharper comparison is

    z<z_v(e)=(A-2eJ)/B.

Its derivative is exactly

    z_v'=2*(1-J-e^2*B/J)/B^2<0.

If e>=1/2 in the original e<1/sqrt(3) interval, this gives

    z<3-sqrt(5)<4/5,
    L>=3/sqrt(5)>4/3.

With the retained upper radius R<25/12,

    Z.n<(25/12)*4/sqrt(41)<125/96.

The square comparison sqrt(41)>32/5 is strict. Therefore
P.n<-1/32, contrary to the original P.n>-1/60. This excludes
the whole e>=1/2 branch, including e=1/2, rather than a sample
of possible angles.

## 4. Complete closed-interval linear-cap proof

For w=8/15+4e/7 and

    Phi=L-1/60-(25/12)*w/sqrt(1+w^2),

the exact derivatives give

    L''=-(1+3e-2e^2)/(1+e^2)^(5/2)<=-1,
    Phi''=L''+(100/49)*w/(1+w^2)^(5/2).

The first bound holds on the entire closed interval [0,1/2]:
the numerator is at least1+2e, while
(1+e^2)^(5/2)<=(1+e^2)^3<=1+2e. The last comparison follows
from 3e+3e^3+e^5<=61/32<2, with e=0 checked directly.

The global maximum of w/(1+w^2)^(5/2) for w>=0 occurs at w=1/2
and equals16/(25sqrt(5)). Hence

    Phi''<=-1+64/(49sqrt(5))<-1+32/49<0.

Both endpoint reserves were independently recomputed exactly:

    Phi(0)=1/340>0,

and, using 3/sqrt(5)>67/50 and sqrt(18421)>271/2,

    Phi(1/2)>397/300-1075/813=29/27100>0.

The squared reserves for those two radical comparisons are,
respectively, 11/2500 and243/4. Strict concavity puts every
intermediate value above the positive endpoint chord. This is
a whole-interval proof with no angular table.

The original cap R*z/sqrt(1+z^2)>L-1/60 and R<25/12 then imply
z>w by strict monotonicity of z/sqrt(1+z^2). Therefore

    u=z-e>w-e>=67/210>3/10.

Every strictness direction is retained. No physical cap at a
hypothetical replacement configuration is assumed.

## 5. The comparison branch is genuinely positive

At q=0 the corresponding positive value is

    H0=A/sqrt(1+A^2),
    u0=J^2*(1-JH0)/B.

The source proves u0<3/10 on the whole closed interval [0,1/2].
Both sides in the required squaring are positive:
J^2-(3/10)B>0, and A*J^3/sqrt(1+A^2)>0.
The exact squared difference expands to

    1/50+(9/50)e-(31/100)e^2+(7/5)e^3
      +(131/100)e^4+(17/5)e^5+3e^6+2e^7+e^8.

I independently recomputed this identity using rational coefficient
arithmetic. The only negative coefficient combines with the linear
term as

    (9/50)e-(31/100)e^2
       =e*(18-31e)/100>=e/40.

Every other coefficient is nonnegative on the interval, with a
strictly positive constant. Thus u0<3/10 also holds at e=0.

Since u(w)=w-e>=67/210>3/10 and u decreases strictly in H,
the comparison H(w) is strictly below H0. Its direct expression

    H(w)=(49+101e+60e^2)/(105*J^3)>0

also establishes the positive branch. The revised correct chain is

    H(w)<S=1/J<=1.

Thus H(w)<1 and k(w)>0, including e=0, and q(w)>0. The
nonnegative square root and every division used later are valid.

## 6. Every premise holds on the actual-to-line comparison interval

For each fixed original e,R, only a scalar function is compared on

    w(e)<=z<=z_actual.

As z decreases toward w, H increases, k decreases and q decreases.
The minimum q is q(w)>0. Since a(q)=1/sqrt(1+q^2) increases
while k decreases, the actual strict k<a inequality is preserved.

The actual v<1 implies H>2e/J^2>e/J, hence H>ek by positive
squaring. Increasing H and decreasing k preserves that sign.
With H=cos(eta), k=sin(eta),

    z_eta=J^3*k/B>0,
    v_eta=H-ek>0.

Therefore v_z>0, so moving toward the line decreases v and keeps
0<v<1. The remaining interval bounds z<1, z>=w>1/2 and
u>3/10 also remain. This verifies the full domain of every
subsequent derivative estimate.

The comparison is not a family of physical packings. The proof
does not claim physical circle containment, actual means or the
original C cap at the nonphysical line endpoint. It compares
the exact original formula using its explicit scalar extension.

## 7. Exact strict derivative reserve

At fixed e the exact derivative is

    T_z=(1-e^2)/(J^3*k*H^2).

The complete bound k(1-k^2)<=2/(3sqrt(3))<2/5, together with
1-e^2>3/4 and J^3<45/32, gives T_z>4/3.

Differentiating the unchanged mean formula gives

    (delta_D)_z
      =v*(u*T_z-T)/(T+u)^2+T*v_z/(T+u).

If u*T_z-T>=0, its derivative is positive. Otherwise 0<v<1
and the strict T_z bound give

    (delta_D)_z>((4/3)u-T)/(T+u)^2
                   >=-3/(28u)>-5/14.

The middle inequality is valid for every positive T,u. Multiplication
by84u(T+u)^2 reduces it exactly to (3T-11u)^2>=0; no original
force ratio or mean is assigned to the scalar minimum T=(11/3)u.

The function z/(1+z^2)^(3/2) on [1/2,1] has its minimum at an
endpoint, with lower endpoint value4/(5sqrt(5)) exceeding
1/(2sqrt(2)); the squared comparison is128>125. Thus the entire
interval has

    R*z/(1+z^2)^(3/2)>1/2

because R>sqrt(2). Combining the two strict estimates yields

    (Q_C.d0)_z<-1/2+5/14=-1/7.

The sign, the radius factor and both strict boundary reserves were
checked. The bound applies over the complete connecting interval,
not merely at the actual endpoint.

## 8. The final comparison and its exact open boundary

Integrating the strict monotonic comparison from the line to the
actual z gives

    Q_C.d0
      <R/sqrt(1+w^2)-B/J-delta_D(e,w)
      <(25/12)/sqrt(1+w^2)-B/J-delta_D(e,w).

The upper comparison radius25/12 is arithmetic only. No original
body, contact or physical circle is moved.

With P0=49+101e+60e^2 and
K=sqrt(11025*J^6-P0^2), direct substitution gives exactly

    delta_D(e,w)
      =(A*K-B*P0)*(K+e*P0)
        /[J^3*(105*A*K+(60e-49)*P0)].

In particular

    T=(A*K-B*P0)/P0,
    u=(56-45e)/105,

and the displayed denominator is the positive T+u denominator
after multiplication by105P0 and the other positive factors.
Section5's comparison branch proves K>0 and q>0. No sign
assumption has been lost in clearing a denominator.

The remaining printed target is the explicit one-variable
inequality

    (25/12)/sqrt(1+w(e)^2)-B/J-delta_D(e,w(e))<=1/2

for the actual allowed original e values in(0,1/2).
**This inequality is not proved in the reviewed manuscript.**
Neither the author status nor this review treats it as established.
Therefore the source supplies no conclusion Q_C.d0<=1/2,
no whole physical-mask exclusion and no entire far-side row exit.

## 9. Verification record and adoption boundary

Exact rational arithmetic was used only to independently check
the degree-eight polynomial identity and the printed rational
endpoint reserves. Its output was:

    Exact degree-eight identity and all requested rational endpoint reserves: PASS

The proof of positivity is the whole-interval written argument,
not a computational sampling certificate. The complete source
hashes and byte lengths in Section1 were verified from the
unchanged files. All calculus and all original-data joins were
reconstructed directly in this report.

The accepted result is exactly the complete necessary scalar
reduction at the revised source pin. Every physical mask, zero
coefficient, actual unit, original force, original mean and
conditional common-selection premise remains. Loaded N, both
whole Type II side rows, the global sharp radius and equality
classification retain their separate obligations.

No numerical pose search, angle mesh, new packing certificate,
changed normal, replacement physical mean, omitted force,
shortened star, Lean/Lake build, CI/workflow dispatch, shared
metadata edit, commit, push or remote mutation was performed.

