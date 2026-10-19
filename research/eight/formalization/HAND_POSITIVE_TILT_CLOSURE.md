# Complete table-free positive-tilt capture, including the original frame errors

**Status: G8 is closed on paper under its original hypotheses.** Assume the candidate frame, signed tangent cuts, all seven intended original-axis owner sets, q<=Q1, and S<=1/1000. Then

    1001/20000 < z < 2/25,
    t=2 arctan(z), and 1/10 < t < 4/25.

The preceding contraction to S<1/1000 is NOT proved here. It remains an earlier table-free gate. The present result replaces the mathematical content of all 41 retained positive-tilt bundles and their 861 quartics. Existing Lean/table files remain unchanged in this hand-proof-only pass.

The nominal stress and its entire scalar polynomial proof are in `HAND_POSITIVE_TILT_NOMINAL_GAP.md` (commit 14a68717335c689f72a6f5d8e3f32597bfe72375). This companion proves why it remains valid for every original error/owner combination, without a 21-alternative certificate list.

## 1. Original hypotheses and the single error budget

Use roles H,G,A,B,T,D,E, and zero-based owner sets

    ({0,2},{0},{0,2},{2,3},{0,2},{2,3},{1}).

Choose any originally feasible allowed axis on every edge. Put I={H,A,B,T,D}, d_i=theta_(i+1)-theta_i, eta=sum_(i in I) d_i and S=sum_(i in I)|d_i|. The G-to-A phase is exactly pi/2-t, the E-to-H phase is pi/2+t-eta, and the other five phases are their nominal multiples of pi/2 plus d_i. In particular |eta|<=S. This is exact cyclic compatibility, not an independent variation of the seven angles.

The hand mixed-owner chain bounds supply the actual primary bounds

    7/12<=a_G,a_T<=349/250,

and show that the intended G axis with t>=0 implies 0<=s=sin(t)<=3/10. The frame chart has c=cos(t)>0. Thus c^2+s^2=1 and c>=19/20 on this arc. Every center also has the original corner disk, a_i<=283/200 and 0<=b_i<=9/10.

The already established negative-half-chart argument in `OWNER_GEOMETRY.md`, Sections 1--4, excludes z<=0 under the same hypotheses. It remains to exclude both positive tails. No positive-tail certificate is used to obtain these facts.

## 2. A necessary nominal inequality retaining the first-order cusps

Use the polynomial weights alpha,beta,delta,epsilon and masses m_A,m_B,m_D,m_H,m_E from the nominal companion. Write lambda=(1,1,alpha,beta,beta,delta,epsilon).

Every center has Euclidean radial length below 3/2: its open inscribed disk of radius 1/2 lies in the containing disk of radius below 2. Consequently each sinusoidal pair projection has second derivative of absolute value at most 3/2.

On an aligned edge the actual feasible projection and the elementary width cusp give

    1 <= P_i^nom + P_i' d_i - |d_i|/2
                          + d_i^2 + |d_i|^3/12.       (1)

Indeed the projection's upper Taylor remainder is at most 3d_i^2/4, while the width is at least 1+|d_i|/2-d_i^2/4-|d_i|^3/12. The derivatives at the nominal angles are exactly

    H: a_G or a_H;       A: a_B or a_A;
    B: b_B or a_T;       T: a_D or a_T;
    D: b_D or a_E.                                   (2)

These are the two actual permitted axes on each aligned edge, not a choice of a preferred axis.

For E define

    K=c(a_E-1/2)+s(b_E+1/2).

The derivative of its nominal separating margin with respect to t is K. Its phase error is -eta. The width is bounded below by the signed smooth branch (1+cos(t-eta)+sin(t-eta))/2 even if t-eta crosses zero. That branch has Taylor remainder bounded by eta^2/2; the projection has upper remainder 3eta^2/4. Hence actual E feasibility implies

    W <= P_E^nom - K eta + (5/4)eta^2.              (3)

G has no error. Weight and sum (1) and (3). The single total remainder L satisfies

    L <= (6/5)(1+1/12000)S^2 + (5/4)(6/5)S^2
       < 3S^2.                                      (4)

Here sum d_i^2<=S^2, sum |d_i|^3<=S^3 and |eta|<=S are used only once. Thus the full necessary inequality is

    D <= sum_i F_i dot x_i
       +sum_(j in I)[(lambda_j P_j'-epsilon K)d_j
                                  -(lambda_j/2)|d_j|]+3S^2,  (5)

where x_i=(a_i,b_i), and D,F_i are the exact nominal demand and forces of the companion.

## 3. Reference torques: whole-arc bounds, not error alternatives

For each of the five anchored vertices define its reference coordinate purely algebraically:

    x_i^0=F_i/(2m_i)-(1/2,1/2).

A reference point is NOT assumed to be an actual center or to lie in the admissible center domain. No proximity conclusion is used. The free primary coordinates a_G and a_T retain their actual values in (2).

Put K0=c(a_E^0-1/2)+s(b_E^0+1/2). The E force gives an exact cancellation:

    K0=(5/3)delta(1+4s/5)-c,
    v:=epsilon K0=epsilon[(5/3)delta(1+4s/5)-c].     (6)

Let m_j^lin denote lambda_j/2 minus the absolute value of the reference version of lambda_j P_j'-epsilon K. The reference first-order error is therefore at most -min_j(m_j^lin) S.

We prove the two uniform bounds

    min_j(m_j^lin) >= s-9/100     (0<s<=1/10),        (7)
    min_j(m_j^lin) >= 0          (79/500<=s<=3/10).  (8)

The details below expose every allowed derivative in (2).

### 3.1. Useful scalar bounds on v and the weights

On 0<=s<=3/10 the explicit weight formulas give

    24/41<=alpha<=3/4, 97/100<=beta<=1,
    47/50<=delta<=6/5, 9/10<=epsilon<=6/5.

The circle identity gives 1-s^2/2 >= c >= 1-(4/7)s^2. Substitution into (6), followed by collecting its five powers of s, yields

    543/500-(493/1000)s-(123/250)s^2+(29/50)s^3
          <= v <= 109/100-(49/100)s-(23/100)s^2.     (9)

Here is one way to check the bounds directly. Replacing c by 1-s^2/2 in the lower expression gives coefficients, beginning at power zero, bounded below by 1.086, -0.493, -0.492, 0.650, -0.213, -0.046. The last three terms are at least (0.650-0.213(0.3)-0.046(0.3)^2)s^3 >=0.58s^3. For the upper expression obtained with c>=1-4s^2/7, the quadratic coefficient is at most -0.408, the cubic at most 0.580, and both higher coefficients are negative. These give a quadratic coefficient at most -0.234, which is below -0.23. All decimals in this paragraph denote exact terminating rationals; these are expansions of the displayed degree-five expression, not numerical evaluations at sample states.

The lower cubic in (9) is decreasing on the whole arc. Its value at 3/10 exceeds 9/10 and its value at 1/10 exceeds one. The upper expression at 79/500 is below 51/50. Consequently

    v>=9/10 throughout;
    v>=1 on the left arc s<=1/10;
    v<=51/50 on the right arc s>=79/500.             (10)

### 3.2. The two potentially small anchor torques

Define

    X_AB=alpha beta/(2m_B)-v,
    X_A =alpha c/(2m_A)-v.

The lower bound on c and the upper polynomial for v BEFORE the rounding in (9) show X_AB>=s-9/100 and X_A>=s-9/100 throughout [0,3/10]. For reproducibility these are the following small polynomial estimates. Let

    V_U=epsilon[(5/3)delta(1+4s/5)-1]+(4/7)epsilon s^2.

Then direct expansion gives

    alpha beta(41/24)(1-9s/50)-V_U-s+9/100
       >=36/10000+s(99/1000-(28/1000)s-(662/1000)s^2),

    alpha(41/24)(1+13s/60)(1-4s^2/7)-V_U-s+9/100
       >=36/10000+s(545/1000-(68/1000)s-(6/5)s^2).

In each line the omitted fourth- and fifth-degree coefficients are positive. The two displayed brackets are positive at their worst bound s=3/10: at least 0.03102 and 0.4166. Thus both estimates hold over the entire arc, not just at endpoints.

The upper margins alpha-X_A and alpha-X_AB exceed 1/20. For example v>=9/10, alpha<=3/4 and

    c/(2m_A)<=8733/4800,
    beta/(2m_B)<=41/24

give these claims immediately. Since beta>=alpha, beta-X_AB also exceeds 1/20. These statements handle both A derivatives and the B derivative b_B.

### 3.3. The other anchor torques

Put X_BD=beta delta/(2m_D)-v and X_H=epsilon/(2m_H)-v. The rough bounds already proved imply

    X_BD >= (97/100)(47/50)(31/24)-109/100
          =10529/120000>1/20,
    X_H >= (9/10)(31/24)-109/100=29/400>1/20.

Their upper margins beta-X_BD, delta-X_BD and 1-X_H also exceed 1/20. For example

    delta/(2m_D)<=8587/5000,
    beta/(2m_D)<=8587/6000,
    epsilon/(2m_H)<=35557/20000,

and v>=9/10 suffice. These cover H's anchored derivative, T's a_D derivative, and D's b_D derivative.

For D's remaining derivative a_E, (6) cancels its entire reference coordinate contribution:

    delta a_E^0-v=epsilon c-delta/2.

Its margin is therefore min(epsilon c,delta-epsilon c). Both are nonnegative because

    delta-epsilon c >= delta-epsilon
       =s(3/10-49s/80)>=0.

On the left arc this is at least s/5, which is at least s-9/100 for s<=1/10. Also epsilon c>=171/200. Thus D's second owner satisfies (7) and (8).

### 3.4. Every actual free-slider coordinate

For either u=a_G or u=a_T in [7/12,349/250], the two endpoint margins for weight l (l=1 or beta) are

    v-l(112/125),        l(13/12)-v.

On the right, (10) and beta>=97/100 make both nonnegative. On the left the first exceeds 13/125 because v>=1 and l<=1. For the second, (9) shows that subtracting s-9/100 leaves at least 1/12-(3/5)s, which is positive for s<=1/10. This covers the free derivative on H, B and T and completes (7)--(8). No slider coordinate was replaced by an assumed nearby reference value.

## 4. Absorb all center-dependent derivatives in one operation

The exact circle completion retains

    sum_i F_i dot x_i-D
       =-g(q,s)-sum_i m_i |x_i-x_i^0|^2
                    -sum_i m_i[q-|x_i+(1/2,1/2)|^2]
       <=-g(q,s)-sum_i m_i |x_i-x_i^0|^2.            (11)

The nonreference part of the derivative term in (5) is linear in the five center displacements. Write it sum_i L_i(d) dot (x_i-x_i^0). Completing these squares a second time gives

    sum_i[L_i(d) dot (x_i-x_i^0)-m_i|x_i-x_i^0|^2]
          <=sum_i |L_i(d)|^2/(4m_i).                (12)

The right side is a squared norm of a linear function of the five errors. The triangle inequality in that weighted direct sum gives

    sum_i |L_i(d)|^2/(4m_i) <= S^2 max_j C_j,        (13)

where C_j is the value for a single unit error on edge j with its actual owner. This is a general norm inequality, not a generated list of 21 tests.

The common E contribution for every such edge is -epsilon(c,s). If D uses its target-primary owner, its additional E contribution is delta(1,0), and the resulting squared norm is

    delta^2+epsilon^2-2delta epsilon c <= epsilon^2,

since delta<=6/5<2(9/10)(19/20)<=2epsilon c. In every other case there is at most one additional anchored coordinate, with coefficient one, alpha, beta or delta. The corresponding coefficient squared divided by four times its anchor mass is at most 11/10, directly from the weight/mass bounds above. Therefore

    max_j C_j <= epsilon^2/(4m_E)+11/10
       <=6/(5s)+103/50.

Combining (4), (5), (7)--(8) and (11)--(13), every actual feasible configuration satisfies

    g(q,s)+m(s)S <= [6/(5s)+6] S^2,                (14)

where m(s)=s-9/100 on the left arc and m(s)=0 on the right. The same lambda and masses are used for every error sign and actual allowed owner. No error budget has been spent a second time.

## 5. Exclude the full left tail, including the removable E-mass endpoint

### 5.1. The short initial arc 0<=s<=1/250

At s=0 the varying E mass is zero, so use the aligned four-circle stress instead. Its weights are (1,1,24/41,1,1,36/31,36/31), with masses 12/41,12/41,12/31,12/31 on A,B,D,H. Bound its E leftover by

    (36/31)[(283/200)s+(9/10)(1-c)].

Its exact demand-minus-bound gap is

    B0-(97/1550)s-(407/155)(1-c).

The actual nominal loss is at most (3001/1000)(36/31)S, by the original improved aligned loss and the E loss 2S. Using 1-c<=4s^2/7, B0>39/10000 and S<=1/1000 gives the uniform positive reserve

    39/10000-(97/1550)(1/250)
       -(407/155)(4/7)(1/250)^2
       -(3001/1000)(36/31)(1/1000)
       =9537/67812500>1/10000.                      (15)

This handles zero and the complete initial arc without division by s.

### 5.2. The arc 1/250<=s<=9/100

The nominal companion gives g>=p. On s<=1/10 its polynomial satisfies

    p(s)>=B0-(79/1250)s+(6/25)s^2,

because the remaining bracket is at least (11/1000)s^2. If (14) were true with S<=1/1000, multiplication by s and B0>39/10000 would force H(s)<=0, where

    H(s)=(6/25)s^3-(311/5000)s^2
                       +(951/250000)s-3/2500000.

But H is positive over the ENTIRE stated interval. Put a=1/250, b=9/100 and let ell be the line joining (a,H(a)) and (b,H(b)). Polynomial division gives

    H(s)-ell(s)=(s-a)(s-b)[(6/25)(s+a+b)-311/5000].

The last bracket is at most (6/25)(a+2b)-311/5000=-451/25000<0, while (s-a)(s-b)<=0. Thus H>=ell. Its endpoint values are

    H(a)=20369/1562500000>0,
    H(b)=123/10000000>0.

This is one cubic chord argument; it introduces no numerical subinterval cover.

### 5.3. The remaining arc 9/100<=s<=1/10

Here m(s)>=0. The nominal companion gives g>9/100000, while (14) would give

    g <=[6/(5(9/100))+6]/1000000
       =58/3000000<1/50000.

This is impossible. The split at 9/100 records the sign change of the proved first-order margin, not a fitted interval partition. Sections 5.1--5.3 exclude every s in [0,1/10], including the common boundaries.

## 6. Exclude the full right tail

For 79/500<=s<=3/10, (8) makes the first-order contribution nonnegative. The nominal companion gives g>1/25000. However, (14) would imply

    g <=[6/(5(79/500))+6]/1000000
       =1074/79000000<14/1000000.

The remaining reserve exceeds 26/1000000. This excludes the entire right tail by the same varying stress, with no intermediate tilt intervals.

## 7. Half-angle conclusion and coverage

By the negative-half-chart hand theorem, z>0. If z<=1001/20000, then s=2z/(1+z^2)<1/10, contrary to Section 5. If z>=2/25, then s>=100/629>79/500; the intended G axis already gives s<=3/10, so Section 6 applies. Hence

    1001/20000<z<2/25.

The inequalities arctan(z)>=z-z^3/3 and arctan(z)<z for z>0 give 1/10<t<4/25. The lower endpoint comparison is an exact rational substitution at z=1001/20000.

Every originally feasible allowed axis is covered in (2), including simultaneous feasible ties. Every center remains at its original position. The proof requires neither radial contact equalities nor uniqueness of a radial chart. All angular errors come from one cyclic frame and share S. Thus this is the original G8 capture statement, not a zero-error or locally centered substitute.

## Dependency and trust status

G8's hand-proof replacement is complete, conditional only on its original earlier capture inputs. The last mismatch contraction, the earlier cuts/contractions, frame concentration and wrong-word table-free gates remain separate. This proof does not claim that those gates have closed or that any Lean import has been removed.

The finite content is one explicit varying stress, elementary circle/Taylor inequalities, degree-five reference-torque expansions, the companion's single scalar polynomial, and one cubic chord identity. There are no generated owner alternatives, Bernstein interval rows, recursive certificates, or external success flags in the mathematical proof. Local symbolic/rational calculations checked the algebra; no Lean source was changed, no Lean compilation was attempted, and no CI was run.