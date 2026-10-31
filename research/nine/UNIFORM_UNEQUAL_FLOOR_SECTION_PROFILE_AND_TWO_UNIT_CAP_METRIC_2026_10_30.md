# Unequal-floor section profiles, the sharp two-unit cap metric, and the complete vertical-return seven-cycle branch

Date: October 30, 2026 UTC.

**Status: complete proposed hand family theorem, awaiting full independent
review. Original proof gates and unrestricted nine-square status are
unchanged by this manuscript alone.**

The main theorem controls every unit orientation above every floor in
one continuous interval. It gives an exact sharp bound on the distance
between two actual squares with different floors. No common separating
normal is assumed. The cycle application consequently handles both
vertical direct return normals with arbitrary initial short-channel
normal, endpoint heights, return-square orientations and original means.

The positive-tilt section proof was developed in the separate frozen
source by annular_capacity, cited below. Its complete argument is
reconstructed here together with the negative-tilt family, the metric
join and the actual full-force cycle caller.

## 1. Statements

Put

    Q=1105/256, R=sqrt(Q), z=5/4,
    g(Y)=sqrt(Q-Y^2), 0<=Y<=R,
    C(f)=g(f+1), 3/8<=f<=1/2.                          (1)

Let S be any actual closed unit square contained in the centered disk
D_Q and in the halfplane y>=f, for a specified floor in this interval.
Its section at y=z is a nondegenerate interval [ell,r].

**Theorem 1 (complete section profile).** For every such S,

    ell<=C(f)-1, r>=1-C(f).                            (2)

Both inequalities are strict if S is not axis aligned. Equality in
the left inequality forces the actual center to be
(C(f)-1/2,f+1/2); equality on the right forces its reflection
(-(C(f)-1/2),f+1/2). These aligned squares do attain equality.

**Theorem 2 (sharp unequal-floor two-unit metric).** Suppose two actual
unit squares S_1,S_2 are contained in D_Q and respectively above
specified floors f_1,f_2 in [3/8,1/2]. Then

    dist(S_1,S_2)<=C(f_1)+C(f_2)-2.                    (3)

If either square is rotated relative to these axes, (3) is strict.
The upper bound is attained by the two aligned units whose centers are

    (-(C(f_1)-1/2),f_1+1/2),
    ( C(f_2)-1/2 ,f_2+1/2),                            (4)

or by exchanging the left and right assignments. Thus (3) is an exact
metric profile for the entire continuous floor domain.

**Corollary 3 (the sharp average-floor terminal).** If, in addition,

    f_1+f_2>=7/8, dist(S_1,S_2)>=1,                    (5)

then

    f_1=f_2=7/16,
    centers=(-1,15/16),(1,15/16),                      (6)

up to exchanging the two actual units, and both are axis aligned.
In particular, if the two units lie in a smaller centered disk D_q
with q<=Q, then q=Q. No intermediate unit is required in this
terminal, and the gap in (5) may be supported in an arbitrary direction.

## 2. One-square coordinates and the actual section

Quarter turns of a unit's side description permit either frame

    u=(a,b), v=(-b,a),
    or u=(a,-b), v=(b,a),
    a>=b>=0, a^2+b^2=1.

Write its center as (x,y), and put

    h=(a+b)/2, t=(a-b)/2, w=a+b,
    delta=z-y, k=z-f, C=C(f), K=(f+1)/C.               (7)

The horizontal and vertical halfwidths are both h. The floor and disk
give y>=f+h and y+h<=R. Consequently its top is at least
f+w>=11/8>z, and its bottom is at most R-w<=R-1<9/8<z.
The line at z therefore passes strictly between its horizontal
supports, and its section is nondegenerate. Its relative interior is
in the open square interior. No point chosen on that line is presumed
to be an original contact or an application mean.

The constants satisfy

    3/4<=k<=7/8,
    23/16<=C<=sqrt(621)/16<25/16,
    K>3/4.                                             (8)

For the last inequality, K increases with f, and at f=3/8 its
square is484/621>9/16. We use actual corner constraints below;
each radical at an actual lower vertex-height bound is therefore in
its permitted domain.

## 3. Positive tilt: both possible left edges

Suppose b>0 and use u=(a,b),v=(-b,a). Solving the original side
inequalities gives

    ell=max(ell_1,ell_2),
    ell_1=x-(1/2+b*delta)/a,
    ell_2=x+(a*delta-1/2)/b.                            (9)

The actual top vertex is P=(x+t,y+h), with P_y>=f+w. The following
whole-domain proof is the frozen positive-tilt lemma
`UNIFORM_FLOOR_POSITIVE_TILT_LEFT_SECTION_BOUND_2026_10_30.md`,
SHA2565029d8729481ff2a461fa1e3fd0aef05c1c89b1a555f9443f76fd5b8f3ffdbf0.
Its details are retained to specify every interval and endpoint.

### 3.1 The first edge

The actual top vertex gives

    a*ell_1=a*P_x+b*P_y-1-b*z.

The function a*g(Y)+b*Y decreases for Y>R*b, and its entire
permitted interval is there, since

    f+w-R*b=f+a-(R-1)b>=f+(2-R)b>1/4.

Concavity of g at f+1 now gives

    a*ell_1<=a*C-a*K*(w-1)+b*(w-k)-1.                 (10)

For every a>=b>0 on the unit circle,

    b*(w-3/4)<1-a+(3/4)*a*(w-1).                      (11)

Indeed four times the right side minus the left side of (11) is

    b/(1+a)*(3+2a-a^2-7ab)>0,

because 2a-a^2>=3/4 and ab<=1/2 leave a bracket at least1/4.
Using k>=3/4 and K>3/4, (11) in (10) proves ell_1<C-1.

### 3.2 The active second edge

If ell_2>=ell_1, then delta>=t. The actual floor gives

    a=h+t<=z-f=k<=7/8.                                (12)

Also b*ell_2=b*P_x-a*P_y+a*z. Monotonicity of
b*g(Y)-a*Y for positive Y gives

    ell_2<=g(f+w)-(a/b)(w-k).

Thus it suffices that

    F(f,a)=g(f+1)-g(f+w)+(a/b)(w-k)>1.                 (13)

At fixed a the derivative in f is

    -(f+1)/g(f+1)+(f+w)/g(f+w)+a/b>0.

Lowering f to3/8 preserves the radical domain. The comparison extends
to its closed upper endpoint by continuity. Put

    D(w)=g(11/8)-g(3/8+w),
    F_0(a)=D(a+b)+(a/b)(a+b-7/8).

Here D'(w)<2 throughout: 3/8+w<9/5 and
4Q-5(9/5)^2=341/320>0. Direct differentiation gives

    b^3 F_0'(a)
      =a+b-7/8+(b-a)(b^2 D'(w)+ab)
      >=a^3+3b^3-7/8>15/256.                          (14)

For the last strict bound, a^3+3b^3 decreases on
[1/sqrt(2),7/8], and at the right endpoint equals
(343+45sqrt(15))/512>239/256.

The smallest value is therefore at a=b=1/sqrt(2). At that point

    F_0>31/20-17/16+7/5-7/8=81/80>1.                 (15)

The exact inputs are g(11/8)=sqrt(621)/16>31/20,
g(3/8+sqrt(2))<17/16, and sqrt(2)>7/5. For the second,
sqrt(2)>7/5>67/48 implies (3/8+sqrt(2))^2>51/16.
This proves ell_2<C-1 whenever that edge is active. When it is
inactive, (10)--(11) already bound the actual left endpoint.

## 4. Negative tilt: the first edge and the full continuous floor interval

Suppose b>0 and use u=(a,-b),v=(b,a). The original side inequalities
give

    ell=max(m_1,m_2),
    m_1=x+(b*delta-1/2)/a,
    m_2=x+(-a*delta-1/2)/b.                            (16)

The actual rightmost vertex is P=(x+h,y+t), whose height is at
least f+a. The identity

    a*m_1=a*P_x-b*P_y+b*z-1

and monotonicity of a*g(Y)-b*Y give

    a*(m_1-(C-1))
       <=a*(g(f+a)-g(f+1))+b*(k-a)-1+a
       =-V(f,a),                                      (17)

where

    V(f,a)=1-a+b*(a-k)-a*(g(f+a)-g(f+1)).              (18)

We prove V(f,a)>0 on the entire stated floor and tilt domain.

### 4.1 Reduce the floor to3/8 without weakening the actual corner estimate

Since

    -g''(Y)=Q/g(Y)^3,

we have Q/g(Y)^3<3/2 for 0<=Y<=3/2. Indeed its largest value
on that interval is17680/12167<3/2. Therefore

    partial_f V
      =b-a*integral_(f+a)^(f+1) Q/g(Y)^3 dY
      >b-(3/2)*a*(1-a)>b/4>0.                        (19)

The last inequality follows from
a(1-a)=ab^2/(1+a)<b/2. All integration endpoints are at
most3/2, so (19) applies to the full original interval. Hence it
suffices to prove V(3/8,a)>0.

### 4.2 Retain a strict quadratic circle-tangent remainder

Put C_0=g(11/8)=sqrt(621)/16 and K_0=22/sqrt(621).
On the interval [3/8+a,11/8] we have

    Y>=3/8+1/sqrt(2)>17/16,
    g(Y)^2<51/16,
    -g''(Y)>3/4.                                     (20)

For the last comparison, squaring positive quantities leaves the
exact reserve

    Q^2-(9/16)*(51/16)^3=13583/32768>0.

Integrating the second-derivative estimate between11/8 and3/8+a
gives

    g(3/8+a)
       <=C_0+K_0*(1-a)-(3/8)*(1-a)^2.                 (21)

This quadratic remainder is essential to cover the complete interval
near the diagonal orientation at the lowest permitted floor. A linear
tangent bound alone is not substituted for (21).

Let

    tau=b/(1+a),
    0<tau<=sqrt(2)-1<5/12,
    a=(1-tau^2)/(1+tau^2), b=2tau/(1+tau^2).

We have K_0<221/250: the squared reserve is
80261/38812500. Substituting (21) in (18), dividing by b, and
using this upper bound on K_0 gives

    V(3/8,a)/b
      > a-7/8+tau*(1-(221/250)*a)
                    +(3a/(8b))*(1-a)^2
      =N(tau)/(8*(1+tau^2)^2),                         (22)

where the exact polynomial is

    N(tau)=1+(116/125)tau-14tau^2+22tau^3
                  -15tau^4+(1134/125)tau^5.            (23)

### 4.3 One exact positive polynomial identity over the whole interval

Put xi=12tau/5, so0<=xi<=1. The polynomial in (23) has the
following exact identity:

    N(tau)=sum_(j=0)^5 B_j*binom(5,j)*xi^j*(1-xi)^(5-j),

with coefficients, in order j=0,...,5,

    1,
    404/375,
    16409/18000,
    142987/216000,
    343139/864000,
    24119/115200.                                     (24)

This is a polynomial identity after tau=5xi/12, obtained by
ordinary coefficient expansion. Every displayed coefficient is
positive and at least24119/115200. The basis terms in (24) are
nonnegative and sum to1 by the binomial theorem. Thus

    N(tau)>=24119/115200>0                              (25)

on the entire continuous interval, including both endpoints. No
sampled value, orientation partition, root isolation or numerical
approximation is used in (24)--(25).

Equations (19),(22),(25) prove V(f,a)>0. By (17), the first
negative-tilt edge satisfies m_1<C-1 at every original floor and
every negative tilt.

## 5. Negative tilt: the second edge

Use the actual top vertex P=(x-t,y+h). The identity

    b*m_2=b*P_x+a*P_y-a*z-1

gives b*m_2<=R-a*z-1. It is enough to prove

    a*z+b*(C-1)>R-1.                                  (26)

For fixed C the function a*z+(C-1)*sqrt(1-a^2) is concave
on [1/sqrt(2),1], so its minimum is attained at an endpoint.
Since C-1>=7/16,

    a*z+b*(C-1)
       >=min(5/4,(z+C-1)/sqrt(2))
       >=min(5/4,27/(16sqrt(2)))
       >9/8>R-1.                                      (27)

Here sqrt(2)<3/2 and R<17/8 suffice for the strict comparisons.
Thus m_2<C-1 everywhere. Combined with Section4, this proves the
strict left-profile bound for the entire negative-tilt family.

## 6. Aligned squares, reflection and exact one-square equality

If b=0, the unit is axis aligned and y>=f+1/2>0. Its actual
farthest corner gives

    (|x|+1/2)^2+(y+1/2)^2<=Q.

Therefore

    ell=x-1/2<=|x|-1/2
               <=g(y+1/2)-1<=g(f+1)-1=C-1.            (28)

Equality in (28) requires x>=0, y=f+1/2, and
|x|+1/2=C. It forces precisely the center given in Theorem1.
Conversely that actual aligned square is in D_Q and attains equality.

Reflection in the y axis preserves the disk and floor, exchanges the
two tilt forms, and exchanges the left and right section endpoints.
It gives r>=1-C, with strictness for every tilted square and the
stated reflected equality center. This completes the whole orientation
and floor domain of Theorem1.

## 7. The sharp metric join for two different floors

Let I_1,I_2 be the two actual intervals on the common line y=5/4.
If they overlap, the two actual squares share a point and have
distance0, strictly below the positive right side of (3).

Otherwise order them with I_1 on the left. Their interval gap is
ell_2-r_1. Because their endpoints are actual points of the original
squares,

    dist(S_1,S_2)<=ell_2-r_1
                  <=C(f_2)-1-(1-C(f_1))
                  =C(f_1)+C(f_2)-2.                  (29)

If either unit is tilted, one of the last two profile inequalities
is strict. Exchanging the interval order proves the same assertion
with the other assignment. This proves Theorem2 without any common
support-direction assumption.

For the aligned units in (4), their vertical intervals overlap since
|f_1-f_2|<=1/8<1. Their horizontal gap is exactly
C(f_1)+C(f_2)-2>0, and their Euclidean set distance equals that
gap. All four corners are in D_Q, with the two outer-upper corners
on its circle. Thus the entire profile (3) is attained as claimed.

Under (5), strict concavity and decrease of g give

    1<=dist(S_1,S_2)
       <=g(f_1+1)+g(f_2+1)-2
       <=2*g(1+(f_1+f_2)/2)-2
       <=2*g(23/16)-2=1.                              (30)

Every inequality is therefore equality. Strict concavity implies
f_1=f_2; strict decrease gives f_1+f_2=7/8. Theorem1's strict
tilt clause and aligned equality description then give exactly (6).
The outer corners have squared normQ, so an actual containing disk
D_q with q<=Q must have q=Q. This proves Corollary3 in full,
including equality, arbitrary gap directions and unequal initial floors.

## 8. Full physical seven-cycle caller with both vertical return normals

Consider the original positive cycle

    A -- U -- V -- B -- C -- W -- D -- A

in the radius window79/40<=sqrt(q)<=sqrt(Q). The three internal
bodies U,V,W are unloaded of full true positive degree two. The four
other bodies physically touch the circle. The cycle has its compatible
physical embedding and circle spokes. All actual units of the original
packing remain present, including those outside this cycle.

The completed long-endpoint alignment theorem permits us to consider
the remaining aligned-long-endpoint family in the original long-normal
frame. Write

    c_A=(-X_A,y_A), c_B=(X_B,y_B),
    |y_A|+|y_B|<=1/8,
    X_A+X_B=3.                                        (31)

The equality in (31) is the unchanged support telescoping through the
two side-normal long transmitters. The complete return-side theorem
allows one common reflection so that the entire original C,D lie above
the long diameter.

Assume the actual positive direct normals from A to D and from B to C
are both the upward axis e_y. This includes shared-side means and
endpoint means at either allowed actual support endpoint. It is a
normal hypothesis, not a prior assumption that C or D is aligned.
Suppose A and B have full true positive degree two, as in the entire
simple-cycle component caller. Their other original force is horizontal.

Full y-force balance therefore makes each endpoint's total circle
resultant have negative y component. An aligned boundary square with
positive center height has only its upper outer circle corner, with
positive y component; it cannot satisfy this equation. Hence

    y_A<=0, y_B<=0.                                    (32)

At zero center height both physical circle corners and both original
weights are retained. No individual downward-corner choice is made.

The original vertical supporting equalities give whole-square floors

    D subset {y>=f_A}, C subset {y>=f_B},
    f_A=y_A+1/2, f_B=y_B+1/2.                          (33)

Equations (31),(32) imply

    f_A,f_B in [3/8,1/2], f_A+f_B>=7/8.                (34)

The original short transmitter's force balance and actual support
equalities give dist(C,D)>=1. This implication needs only the actual
unit width lower bound; it does not presuppose a horizontal short
normal or the location of W relative to either cap floor. The original
angular equation, if used, retains its actual one- or sqrt(2)-width
classification as usual.

Corollary3 applies directly to C,D and the two floors in (33). It
forces

    q=Q, f_A=f_B=7/16,
    y_A=y_B=-1/16,
    c_D=(-1,15/16), c_C=(1,15/16),                     (35)

with C,D aligned, after fixing their actual left/right order. That
order is also forced by their actual contacts with A,B: the opposite
assignment could not contact the corresponding long endpoint.

The physical circle equations of the aligned A,B, their actual signs
and the center span in (31) now give

    c_A=(-3/2,-1/16), c_B=(3/2,-1/16).                 (36)

Indeed their outer-lower corners have height-9/16 and squared normQ,
so both outer horizontal coordinate magnitudes are2. The reflected
version is the usual four-anchor equality geometry.

If the full short channel has exactly one true unloaded transmitter,
its actual closest-support gap is exactly1 in this equality geometry.
Its direction is horizontal: for the two aligned return squares in
(35), the unique minimum-norm vector of their convex difference set
is (1,0), up to the original direction sign. Thus its internal width
is1 and W is side-normal in this same frame. Its actual transverse
center coordinate and force-line mean are not changed or fixed by
this conclusion.

**Whole-branch conclusion.** Below Q the entire aligned-long-endpoint
opposite seven-cycle family with both actual vertical direct return
normals is impossible. At Q the four actual boundary anchors are
exactly (35)--(36). This covers all initial endpoint heights, return
tilts, short normals, physical circle masks and original shared-side
means in that family, while retaining every original completing unit.

The remaining aligned-long-endpoint family has at least one actual
direct return normal strictly oblique at the corresponding upper-inner
endpoint vertex. Section8 does not replace that genuine physical
alternative by a vertical separator, and does not claim its closure.

## 9. Frozen inputs, continuous verification and research record

| Source | SHA256 | Used content |
| --- | --- | --- |
| `UNIFORM_FLOOR_POSITIVE_TILT_LEFT_SECTION_BOUND_2026_10_30.md` | `5029d8729481ff2a461fa1e3fd0aef05c1c89b1a555f9443f76fd5b8f3ffdbf0` | Complete positive-tilt family, reconstructed in Section3 |
| `TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md` | `78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6` | Actual long-endpoint coupled heights in the caller |
| `LONG_CHANNEL_OUTER_STRIP_EXCLUSION_AND_STRAIGHT_LINE_BARRIER_2026_10_30.md` | `dd1d91f8e49f4a5f507a70b53a75a30b299757f9f04a0976da3e674674ae7b05` | Original long support telescoping and side-normal internal widths |
| `LONG_RUN_RETURN_MARKS_WHOLE_SIDE_CLEARANCE_AND_SHORT_NORMAL_CONE_2026_10_30.md` | `c10361ea546b8e5681b4ac38c09b1b2e9b14fa0a2621c541f689857c73acbd1e` | One common return-side choice for the actual compatible cycle |
| `SEPARATED_BOUNDARY_RETURN_NEIGHBORS_FORCE_ALIGNED_LONG_ENDPOINTS_2026_10_30.md` | `9c7f47ce87b5a7d548ec76c33f5912adae870211770ea578f15621a78104ca06` | Complete preceding long-endpoint alignment reduction |

The one-square theorems and metric join use only actual corner
containment, continuous monotonicity, a quadratic circle-tangent
estimate, one exact positive polynomial identity and interval geometry.
The physical application separately retains all full true-degree,
force, torque, support, circle-mask and unchanged-mean hypotheses.

An earlier exploratory numerical section diagnostic occurred during
research without creating a file; it was outside the delegated search
scope. No numerical observation is a premise, verification substitute
or source of proof credit here. Every asserted orientation and floor
case is proved continuously in Sections2--7, with exact identities.
No further such search was used. No Lean compilation, CI execution,
original gate mutation or remote publication is asserted by this file.
