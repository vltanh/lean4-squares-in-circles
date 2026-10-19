# Gate 3B.2/HIGH: a complete near-3+5 Jensen-defect exclusion

2026-10-13. This is a **new continuous exclusion extending into HIGH**. It uses the previously completed exact 3+5 fixed-frame certificate. M5 as a whole and unrestricted optimality remain open.

## 1. Defect and strong concavity

For either closed folded M5 word I or II put h=pi/4, c=(sqrt(2)-1)/2, W0=28+15c. Let

    0=x_0<=x_1<=...<=x_7<=h,
    lambda_k=(x_k-x_(k-1))/h (1<=k<=7),
    lambda_8=(h-x_7)/h,
    Lambda_odd=lambda_1+lambda_3+lambda_5+lambda_7.

The lambda_k are nonnegative and sum to one. The eight simplex vertices v^(k) give exact two-frame reference configurations: every EVEN k has a 3+5 split and every ODD k has a 4+4 split.

Define the actual complete-pair width sum and two defects

    w_ij=(1+|cos(theta_i-theta_j)|+|sin(theta_i-theta_j)|)/2,
    W=sum_(i<j) w_ij,
    E=W-W0,
    J=E-c*Lambda_odd = W-sum_k lambda_k W(v^(k)).

The coupled strong concavity of the true pair support widths, proved in GATE3B_M5_COUPLED_WIDTH_CONCAVITY.md and GATE3B_M5_GLOBAL_SUPPORT_SURPLUS.md, gives

    J >= (1/4)sum_(i<j)(x_j-x_i)(h-x_j+x_i)
      >= (7h^2/8)(1-sum_k lambda_k^2) >=0.               (1)

Unlike E, J removes the legitimate increased cost of an odd (4+4) vertex.

## 2. A quantitative dichotomy

If J<=3/1000 choose k with maximal lambda_k. Because sum lambda_j^2<=max lambda_j, (1) implies

    1-lambda_k <=8J/(7h^2)<16/2625<1/100,
    max_i|x_i-v_i^(k)|<=h(1-lambda_k)
                       <=8J/(7h)<4/875<1/200.            (2)

Here h>3/4. The maximum lambda is unique. Thus every actual M5 packing with J<=3/1000 has all eight actual frames, after a common rotation and labeling, within epsilon=1/200 radian of ONE exact reference configuration of type 3+5 (even k) or 4+4 (odd k), modulo quarter turns. All angular boundary ties remain covered.

## 3. Complete exclusion of the even-cut child, including HIGH

Assume the packing fits a disk of squared radius q<=Q=9789/2500, that J<=3/1000, and that its maximizing lambda has even index. At every actual center inscribe a reference-oriented square of side b=200/201. By (2), its misalignment is at most 1/200, and

    b(|cos(delta)|+|sin(delta)|) <= b(1+1/200)=1.

Hence these eight reference squares lie within their actual host squares. All 28 nonoverlap constraints and disk containment survive. Rescaling by 1/b gives an ACTUAL exact 3+5 two-frame unit-square packing with

    q_ref<=Q/b^2=395485389/100000000=3.95485389.

GATE3B_M5_LOW_EXACT_CERTIFICATE.md gives a complete rational exclusion of ALL 3+5 exact-frame packings at radius Rbar=198869/100000. The difference

    Rbar^2 - q_ref_bound =340261/10000000000>0

contradicts its theorem. Therefore:

> **No M5 packing under q<=Q has J<=3/1000 and an EVEN maximizing lambda.**

This is strictly stronger than the previous LOW exclusion, because it does not assume E<=3/1000.

## 4. A genuine angular HIGH example in the newly excluded child

Take folded word I, x=(1-t)v^(2)+t*v^(1) with t=1/500. Its unique largest lambda is even (lambda_2=499/500). Put delta=th=pi/2000. Counting the actual pair widths gives

    E=2(sin(delta)+cos(delta)-1)
        -(3sqrt(2)/2)(1-cos(delta)),
    J=E-c/500.

Using 3.14<pi<22/7, sin(delta)>=delta-delta^3/6, cos(delta)>=1-delta^2/2, sqrt(2)<3/2 and c>1/5 gives the **strict** bounds

    3/1000<E<22/7000,
    0<=J<22/7000-1/2500<3/1000.

This example lies on a closed folded-chamber boundary. Perturb its simplex weights slightly into the relative interior, retaining the even maximum. The strict inequalities persist, and the bounded occupancy walk then gives generic true M5 frame data in HIGH. This does not claim existence of a disk packing; it proves the new HIGH subdomain is nonempty as an angular domain.

## 5. Exact unresolved HIGH decomposition

Every M5-HIGH configuration (E>3/1000) belongs to exactly one of:

* HIGH-J-EVEN: J<=3/1000, maximizing lambda even: **EXCLUDED** by Section 3.
* HIGH-J-ODD: J<=3/1000, maximizing lambda odd: **OPEN**. The same inscribed-square argument reduces it to an actual **4+4 exact two-frame** unit-square packing under q_ref<=3.95485389. A complete 4+4 exclusion at this ceiling would close this entire child, without any original separator-owner assumptions.
* HIGH-J-DIFFUSE: J>3/1000: **OPEN**, retaining all original angles, real disk vertices, and 28 complete true-square SAT disjunctions.

The equality boundary J=3/1000 is covered by the near-cut cases, where maximizing lambda is unique. This is an exhaustive new **parent-to-children** proof, not a radius theorem for the two open children.

No 4+4 impossibility, full M5 exclusion, later M6--M8 exclusion, unrestricted optimality, or equality theorem is asserted. No Lean or CI is involved.
