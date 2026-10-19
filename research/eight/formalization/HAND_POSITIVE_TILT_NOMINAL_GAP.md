# A single analytic five-circle stress on both positive tilt tails

**Status: the complete nominal continuous inequality is proved below.** The perturbation argument for the original nonzero frame errors is a separate companion, not assumed in this note. This is a hand-proof-only checkpoint; no Lean or historical certificate file is changed.

Let s=sin(t), c=cos(t), 0<=s<=3/10, c>=0 and c^2+s^2=1. The mixed-owner chain argument already supplies s<3/10 for any feasible intended G owner, under the original S<=1/1000 hypotheses. Put Q=Q1=1957767069/500000000. Each actual center has (a_i+1/2)^2+(b_i+1/2)^2<=q<=Q. No radial equality or proximity of a center is required.

## 1. The varying stress and its geometric normalization

Write the seven nominal edge projections in the intended-owner order H,G,A,B,T,D,E:

    b_H+b_G, c a_A-s b_A-b_G, b_A+b_B,
    a_B-b_T, b_T+b_D, a_D+b_E, a_H+s a_E-c b_E.

Their demands are 1,W,1,1,1,1,W, where W=(1+c+s)/2. Choose edge weights

    (1,1,alpha,beta,beta,delta,epsilon),

where

    alpha   = 24/41 + (49/100)s - s^2/20,
    beta    = 1 - s/20 - s^2/6,
    delta   = 36/31 - (7/10)s - s^2/16,
    epsilon = 36/31 - s + (11/20)s^2.

Choose five circle masses, in order A,B,D,H,E:

    m_A = (12/41)/(1+13s/60),
    m_B = (12/41)/(1-9s/50),
    m_D = (12/31)/(1+9s/25),
    m_H = (12/31)/(1+49s/100),
    m_E = (3s/10)/(1+4s/5).

For s>0 they are all positive. All seven edge weights are positive and at most 6/5. At s=0 the E force and mass vanish together, and E is simply omitted.

The coefficients are one explicit polynomial/rational family, not a list selected by an interval index. Its zero-tilt normalization is the exact aligned four-circle equilibrium: the A/B farthest corners are (41/24,1), the D/H corners are (3/2,31/24), all of squared norm 2257/576. Dividing the previously used stress by its H/G weight gives alpha=24/41, beta=1, delta=epsilon=36/31 and masses 12/41,12/41,12/31,12/31. The nonconstant terms supply a low-degree continuation of these circle supports. Their validity is proved directly over the whole arc below; no fitted-value accuracy or optimality premise is used.

The G and T transverse forces cancel. The five remaining force vectors are

    F_A=(c,alpha-s), F_B=(beta,alpha), F_D=(delta,beta),
    F_H=(epsilon,1), F_E=(epsilon s,delta-epsilon c).

The weighted demand is D=1+alpha+2beta+delta+(1+epsilon)W.

For a corner disk use the exact completed-square upper bound

    F_x a+F_y b <= m q+(F_x^2+F_y^2)/(4m)-(F_x+F_y)/2.

Consequently define the demand-minus-circle-bound gap

    g(q,s)=D+sum_i(F_ix+F_iy)/2
             -sum_i |F_i|^2/(4m_i)-q sum_i m_i.

Every nominally feasible configuration must have g(q,s)<=0. The exact retained squared displacements will be used in the perturbation companion.

## 2. One polynomial lower bound on the entire arc

Let

    B0=(1728/1271)(2257/576-Q)=38726637/9929687500,

    p(s)=B0-(79/1250)s+(51/200)s^2-s^3/100
                 -(27/100)s^4-(3/10)s^5.

We prove, for every 0<=s<=3/10,

    g(q,s) >= g(Q,s) >= p(s).                         (1)

The first inequality follows from q<=Q and positive masses. Here is a fully specified polynomial proof of the second, with no angle or state partition.

### 2.1. A chord estimate with its remainder displayed

Set x=s^2 and P(x)=1-x/2-x^2/8-x^3/14. On 0<=x<=9/100, P(x)>0 and

    1-x-P(x)^2 = x^3(56-273x-56x^2-16x^3)/3136 >=0.

The last bracket is positive even after replacing every x by 9/100 in its negative terms. Thus P(x)<=sqrt(1-x)=c. In particular, with chi=1-c,

    0<=chi<=s^2/2+s^4/8+s^6/14=:chi_U.               (2)

### 2.2. Polynomial upper bound for the total mass

Put T4(x)=1-x+x^2-x^3+x^4. The identity

    T4(x)-1/(1+x)=x^5/(1+x)>=0

holds for x>=0. Also, for 0<=x<=27/500,

    1/(1-x)=1+x+x^2+x^3+x^4/(1-x)
             <=1+x+x^2+x^3+(500/473)x^4.

Define the polynomial

    U(s)=(12/41)[T4(13s/60)+1+9s/50+(9s/50)^2
                           +(9s/50)^3+(500/473)(9s/50)^4]
          +(12/31)[T4(9s/25)+T4(49s/100)]
          +(3s/10)T4(4s/5).

Then sum_i m_i<=U(s).

### 2.3. The explicit scalar expression and its whole-interval sign

Using c^2+s^2=1 before estimating anything gives exactly

    g(Q,s)=3+2alpha+3beta+2delta+epsilon+epsilon s-Q sum_i m_i
       -(1+alpha^2-2alpha s)/(4m_A)
       -(beta^2+alpha^2)/(4m_B)
       -(delta^2+beta^2)/(4m_D)
       -(epsilon^2+1)/(4m_H)
       -(delta-epsilon)^2/(4m_E)
       -chi[1+delta epsilon/(2m_E)].                  (3)

The coefficient multiplying chi is positive. Replace sum m by U and chi by chi_U in (3), obtaining the explicit polynomial G(s). All reciprocals of m_A,m_B,m_D,m_H are affine. The apparently singular terms at E are polynomial as well: delta-epsilon=s(3/10-49s/80), and chi_U is divisible by s^2, whereas 1/m_E=(10/(3s))(1+4s/5). Thus G has degree ten and its value at zero is B0.

For clarity, the entire sign check can be expressed without printing ten enormous rational coefficients. Direct expansion of the displayed expression for G gives the following coefficientwise lower bound:

    G(s)-p(s) >= s(26-9s)/1000000 + (27/10000)s^3
                 +(s^4/1000)(56-132s-86s^2-77s^4).  (4)

Specifically the coefficients at powers 1,2,3,4,5,6,8 are bounded below by 26/1000000, -9/1000000, 27/10000, 56/1000, -132/1000, -86/1000, -77/1000, respectively; the coefficients at powers 7,9,10 are nonnegative. These are comparisons of the one explicitly defined polynomial (3), with (2) and U substituted, not data indexed by geometric boxes. They are ordinary exact rational arithmetic. For example the first two coefficients are 231172458277/8865225000000000 and -314430917549/36938437500000000. The three positive high coefficients are 272761/2777600, 2339/67200, and 11/3360.

Both brackets on the right of (4) are positive throughout the whole interval. Indeed 26-9s>=233/10, and

    56-132s-86s^2-77s^4
       >=56-132(3/10)-86(3/10)^2-77(3/10)^4
       =80363/10000>0.

This proves G>=p, and hence (1). There is no Bernstein coefficient cover or interval subdivision.

## 3. The two complete nominal tails

The constant satisfies

    B0-39/10000=3423/39718750000>0.

On 0<=s<=1/10, p'(s)<=-79/1250+(51/100)(1/10)<0. Therefore

    g(q,s)>=p(s)>=p(1/10)>9/100000.                  (5)

For the right tail, p'' is decreasing on [0,3/10], and

    p''(3/10)=24/625>0,
    p'(3/20)=13153/1600000>0.

Thus p increases on [3/20,3/10]. Substitution, using B0>39/10000, gives

    p(79/500)-1/25000>928996453/312500000000000>0.

Consequently

    g(q,s)>1/25000  whenever 79/500<=s<=3/10.        (6)

To relate these to the required half-angle tails, s=2z/(1+z^2) is increasing on [0,3/8]. The entire left tail 0<=z<=1001/20000 has s<1/10, while the entire right tail z>=2/25 has s>=100/629>79/500. Equations (5) and (6) therefore exclude both complete nominal tails by the same varying circle stress.

## 4. Remaining obligation at this checkpoint

An actual packing may have nonzero aligned frame errors. It is NOT enough to assert that a nominal gap of order 1/10000 tolerates a crude error of order S: the latter would be larger. The companion must keep the first-order support cusps, use the same total mismatch S once, and absorb center-dependent derivatives into the retained five circle squares. Only after that step is proved will the original positive-tilt capture gate be closed.

The formulas above were explored and their expansions checked using local symbolic/rational calculations. Those calculations are diagnostics, not premises: the proof consists of the displayed circle identity, geometric-series identities, polynomial expression, coefficient inequalities and whole-interval sign bounds. No Lean compilation or CI was run.