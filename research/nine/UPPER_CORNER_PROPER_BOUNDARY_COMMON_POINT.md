# A proper boundary return at a small upper corner contains one fixed point

Date: October 27, 2026.  
Author: cert_final_review.

**Status: complete fresh analytic candidate, pending a separate full
independent review.** This is a new proof of the entire stated local
common-point theorem, not a claimed byte restoration of the older
missing b8617879 source. All actual side positions are retained,
including the closed endpoints, and the proper radial offset is
allowed to be zero. There is no second-contact owner hypothesis,
circle-mask reduction at a neighboring unit, or computational packet.

## 1. Full local theorem

Let a physical unit square C lie in the disk centered at zero with
radius R, where

    17/4<=R^2, R<25/12.

Fix the actual point and the actual inward normal/tangent frame

    W=(h,G), -1/60<h<=0, 89/120<G<=1,
    n=(u,v), f=(v,-u),
    u,v>0, u^2+v^2=1,
    C=W+[0,1]n+[-lambda,1-lambda]f,
    0<=lambda<=1.                              (1)

Assume C has an actual containing-circle corner z_C and an actual
proper positive radial line through the indicated side point:

    W+ell*n=r*z_C,
    ell>=0, r>0.                              (2)

For example, a genuinely loaded physically unique C2 with a physical
boundary neighbor has exactly this proper radial property at its
actual incoming owned side, by the complete original proper-port
lemma. The local theorem itself needs only (1)--(2), containment and
the actual circle corner. It does not assume ell>0 or ell<1.

**Theorem 1.1.** The fixed point

    F=(h+1/2,5/4)

belongs to the open interior of the entire actual C.

The endpoints h=0, G=1, lambda=0, lambda=1 and ell=0 remain in
the domain. No value is assigned to a second contact or its mean.

## 2. The actual circle corner and the retained proper inequality

Put

    a=W.n=hu+Gv,
    B=-W.f=Gu-hv>0.

The two minimum-n vertices of C are at distance at most one from
W, for the entire closed lambda interval. Their norms are less than
121/60, since

    |W|^2<1+1/3600<(61/60)^2.

They cannot be containing-circle corners because

    17/4-(121/60)^2=659/3600>0.

Thus the actual z_C is on C's maximum-n side. Projecting (2) on
f gives z_C.f=-B/r<0. Such a negative-coordinate circle corner
must be the minimum-f endpoint: if it were the maximum endpoint,
subtracting f would give another physical C vertex with larger
squared norm. Therefore

    z_C=W+n-lambda*f,
    z_C.n=a+1>0,
    z_C.f=-B-lambda<0.                         (3)

The sign a+1>0 follows also directly from a>h>-1/60. Comparing
the same two components in (2) gives

    r=B/(B+lambda)>0,
    ell=(B-a*lambda)/(B+lambda)>=0,
    B-a*lambda>=0.                            (4)

The last inequality is non-strict. It is the entire proper-port
information used in the proof, including the real ell=0 endpoint.

## 3. The normal coordinate of F is strictly internal

Let

    L=5/4-G, 1/4<=L<61/120,
    K_F=(F-W).n=u/2+Lv,
    T_F=(F-W).f=v/2-Lu.

Both positive terms make K_F>0. The full unit-frame bound gives

    K_F^2<=1/4+L^2
       <7321/14400<1.

Thus 0<K_F<1. The complete remaining problem is exactly

    0<lambda+T_F<1.                           (5)

These are the two genuine transverse face inequalities of the same
actual C. No enclosing rectangle is substituted for C.

## 4. Failure of the lower transverse face puts the circle inside radius two

Suppose lambda+T_F<=0. Then

    lambda<=Lu-v/2,
    0<B+lambda
       <=(G+L)u-(h+1/2)v
        =(5/4)u-(h+1/2)v<(5/4)u.

The last sign is strict because h+1/2>0 and v>0. Also
0<a+1<=1+v, since h<=0 and G<=1. The actual circle identity
in (3) consequently gives

    R^2=(a+1)^2+(B+lambda)^2
       <(1+v)^2+(5u/4)^2
        =41/16+2v-(9/16)v^2<=4.              (6)

The final quadratic increases on 0<=v<=1, because its derivative
is 2-9v/8>0 there, and its endpoint value is four. Equation (6)
contradicts R^2>=17/4. Thus the first strict inequality in (5)
holds on the entire local domain.

## 5. Two uniform consequences of failure of the upper transverse face

Suppose instead lambda+T_F>=1. Define the exact threshold

    lambda_0=1-T_F=1-v/2+Lu>1/2,
    epsilon=-h/G in [0,2/89).

Then lambda>=lambda_0. We prove the following full continuous
implications of that same supposed failure:

    u>5/9;
    if G<=4/5, then u>3/5.                    (7)

The scalar calculations establishing them are given in full below.
They introduce no physical case labels and change no actual angle.

For either contrary range u<=5/9 or u<=3/5, one has v>=4/5 and

    v-(2/89)u>=70/89>0.

Consequently a=G(v-epsilon*u)>0. From the actual non-strict proper
inequality (4),

    lambda_0<=lambda<=B/a
          =(u+epsilon*v)/(v-epsilon*u).

Thus the expression

    F_epsilon,L(u,v)
      =(v-epsilon*u)(1-v/2+Lu)-u-epsilon*v    (8)

must be nonpositive. It strictly decreases with epsilon because
its epsilon derivative is -u*lambda_0-v<0. On the present ranges
it increases with L, since (v-epsilon*u)u>0.

Set e=2/89. For a chosen lower bound L_0<=L and v_0<=v,
use v^2=1-u^2 to obtain the whole quadratic lower comparison

    F_epsilon,L(u,v)>=F_e,L_0(u,v)>=f(u),

    f(u)=(1-e)v_0-1/2
       +[(L_0+e/2)v_0-(1+e)]u
       +(1/2-e*L_0)u^2.                     (9)

The coefficient of v before replacing it by v_0 is
1-e+(L_0+e/2)u>0, so that replacement has the stated direction.
All denominator and derivative signs are uniform on the ranges.

Here are the two exact comparisons, with every endpoint retained:

| Contrary range | L_0 | v_0 | f(r), at its upper u endpoint r | f'(r) |
| --- | --- | --- | --- | --- |
| 0<u<=r=5/9, any G<=1 | 1/4 | 33/40 | 12389/1153440 | -371/1440 |
| 0<u<=r=3/5, G<=4/5 | 9/20 | 4/5 | 59/890 | -146/2225 |

In the first row, v>=sqrt(56)/9>33/40, with exact squared
reserve 1391/129600. In the second row v>=4/5 follows exactly
from u<=3/5. The stated lower L bounds are respectively G<=1
and G<=4/5.

For both rows, 1/2-e*L_0>0. Hence f' increases with u and is
at most the displayed negative f'(r) throughout 0<=u<=r.
Therefore f(u)>=f(r)>0 on the entire closed interval. This
contradicts the nonpositive expression required by (8). Both
implications (7) follow, without discarding a lambda or ell
endpoint.

## 6. A complete endpoint principle for the actual circle height

For a fixed g define the continuous function on [0,1]

    Y_g(u)=g+(5/4-g)u^2+u
              +(1-u/2)sqrt(1-u^2).

Under the same upper-face failure, the actual circle height in
(3) satisfies

    (z_C)_y=G+v+lambda*u
        >=G+v+lambda_0*u
         =Y_G(u).                            (10)

For each fixed 0<u<1, Y_g(u) increases with g, with derivative
1-u^2>0. To control the entire u intervals in (7), differentiate:

    Y_g'(u)=2(5/4-g)u+1-v/2-u(1-u/2)/v,

    Y_g'''(u)=3(1/2-u)/(1-u^2)^(5/2)<0
                  for 1/2<u<1.              (11)

Thus Y_g' is strictly concave on every interval considered below.
If Y_g'(r)>0 at its left endpoint r>1/2, its nonnegative set
is an interval beginning at that endpoint. It can change sign from
positive to negative at most once. Therefore Y_g first increases
and may then decrease; it has no interior minimum on [r,1].
Continuity at u=1 gives the complete bound

    Y_g(u)>=min(Y_g(r),Y_g(1))
                     for r<=u<=1.           (12)

This is an endpoint consequence of a derivative sign on the full
continuous interval. It is not an inference from sampled values.

## 7. Both full height intervals contradict the containing radius

If G>=4/5, equation (7) gives u>5/9. Use g=4/5 and r=5/9.
The derivative at r is strictly positive. Indeed v>=4/5 and
v<=1 there give

    Y_(4/5)'(5/9)>=1-325/648=323/648>0.

The exact endpoint comparison, using v>33/40, is

    Y_(4/5)(5/9)
      >4/5+(9/20)(25/81)+5/9+(13/18)(33/40)
       =301/144=25/12+1/144.

At the other endpoint Y_(4/5)(1)=9/4>25/12. Equations
(10)--(12) therefore give (z_C)_y>25/12>R.

If G<=4/5, equation (7) gives u>3/5. Use g=89/120 and r=3/5.
The full lower height G>89/120 ensures Y_G(u)>Y_g(u). At
r=3/5 one has v=4/5 exactly and

    Y_(89/120)'(3/5)=137/200>0,

    Y_(89/120)(3/5)
       =(89/120)(16/25)+(5/4)(9/25)+7/5-6/25
        =3127/1500=25/12+1/750.

Again Y_(89/120)(1)=9/4>25/12. The same full interval argument
gives (z_C)_y>25/12>R. The equality G=4/5 is covered by both
computations and is not removed.

Both alternatives contradict the actual circle corner's membership
in the radius-R disk. Upper-face failure is therefore impossible.
Together with Sections 3--4, all four strict C face inequalities
hold at F. This proves F belongs to int(C).

## 8. Exact genuine C2 caller and whole endpoint preservation

In the original hub-tip usage, W is the actual upper near vertex
of a root H, and HC is a singleton owned only by C, with its
strictly northeast normal n. The actual C-owned side position
gives the chart (1); the theorem above deliberately allows the
larger closed lambda interval.

The original C is uniquely and positively loaded and has exactly
the two original positive pair forces HC and CK. Its actual
neighbor K is a physical boundary unit. The complete original
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, therefore
gives a positive radial concurrence q_C and

    q_C=W+ell*n, ell>=0.

Because C is physically unique, its resultant is a positive
multiple of its actual circle corner z_C. This is precisely (2).
No strictness of ell is added, no interiority at H or K is used,
and no C-owned or K-owned CK alternative is selected in advance.
The actual second-contact mean and all other forces are untouched.

The theorem proves the same fixed point belongs to every such C
at once. A separate physical theorem can prove that a second
actual boundary unit K contains this point, yielding a complete
overlap contradiction without further CK owner cases. That second
inclusion is not assumed or claimed by this source alone.

## 9. Complete direct inputs and verification boundary

The local geometric theorem in Sections 1--7 has its whole proof
here from its explicit proper-line premise. For the exact C2 caller
in Section 8, the complete present original inputs are:

| Source | SHA256 | Exact use |
| --- | --- | --- |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Lemma 2.1 at the true loaded C2 with actual physical boundary neighbor K, including ell>=0 and positive radial multiplier |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | The actual owned side/application convention, unchanged circle force and full actual shared means |

Both complete sources are present and were read in full. The proof
uses no remembered conclusion from a missing newer manuscript.
Exact rational and polynomial calculations verify the displayed
identities and reserves; the continuous sign and physical domain
arguments are supplied in the manuscript itself.

This is a fresh replacement local theorem. It does not claim the
old b8617879 source hash, restore a missing original-family
normal form, prove a physical-mask reduction, or change a graph
gate. It invokes no Lean, CI, numerical pose sample, ledger edit
or remote mutation. No computational exclusion certificate is
introduced.
