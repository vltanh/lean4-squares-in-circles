# Both E-owned outer returns are impossible at adjacent unloaded pentagon ends

Date: October 28, 2026 UTC. Authors: root and pentagon_owned continuation.

**Status: complete proposed radius-free original-interface exclusion,
frozen for separate full independent and root review.** The two
actual E-axis alternatives are both excluded: equal axes by an
actual port separation greater than one, and perpendicular axes
by one full original endpoint torque and the positive height of
its actual inner-return point. Every closed E-face parameter is
retained, including both endpoints.

No circle estimate, E2 properness, boundary-neighbor condition,
physical circle mask or force equation at B,C,E is needed. The
separately complete singleton reduction supplies this exact owner
class in the surviving original two-unloaded-end pentagon.

## 1. Exact whole original adjacent chart

Keep all nine actual units, the original positive graph

    HA, HB, HC, HD, AB, BC, CD, DE, EA,

and complete genuine unloaded H4,A3,D3. Retain every original
normal, application, full shared mean, positive force, torque,
physical mask, circle corner, zero coefficient and true degree.

Use the entire adopted adjacent-end chart

    INNER_PENTAGON_ADJACENT_EXTERNAL_ENDS_FOUR_CORNER_AND_OUTER_RETURN_CHART.md
    SHA-256 4d789a72e56cba5b4416f5231cf97fc3145488cfdaec0482ba9fabd808036db3.

It gives the actual own chart H=[0,1]^2 with strict H applications

    HA at (1,0), HB at (1,1), HC at (0,1), HD at (0,0).

The unchanged endpoint poses and original force/torque tables are

    n_A=(u,-v), j_A=(v,u),
    n_D=(-p,-q), k_D=(-q,p),
    u,v,p,q>0, u^2+v^2=p^2+q^2=1,
    A=(1,0)+[0,1]n_A+[-rho,1-rho]j_A,
    D=[0,1]n_D+[-kappa,1-kappa]k_D,
    0<rho,kappa<1,                                    (1)

and

    F_AH=-Gamma_A*n_A,
    F_AB=-alpha_A*n_A+beta_A*j_A,
    F_AE=(Gamma_A+alpha_A)n_A-beta_A*j_A,
    P_AB=(1,0)+tau_A*n_A+(1-rho)j_A,
    T_A=P_AE=(1,0)+n_A-rho*j_A,
    beta_A*(1-tau_A)=alpha_A+rho*Gamma_A,               (2)

    F_DH=-Gamma_D*n_D,
    F_DC=-alpha_D*n_D+beta_D*k_D,
    F_DE=(Gamma_D+alpha_D)n_D-beta_D*k_D,
    P_DC=tau_D*n_D+(1-kappa)k_D,
    T_D=P_DE=n_D-kappa*k_D,
    beta_D*(1-tau_D)=alpha_D+kappa*Gamma_D.             (3)

Here Gamma_A,Gamma_D,beta_A,beta_D>0, alpha_A,alpha_D>=0,
0<=tau_A,tau_D<1, and alpha_J>0 implies tau_J=0 at the corresponding
end. All original perpendicular inner means and their remaining
closed endpoints are kept. The original AE and DE normals are
strict at their actual endpoint vertices T_A,T_D and both have
strictly negative world y components.

Assume both of these original normals into E are own axes of that
same actual unit E. The theorem below permits every actual support
point of E on those closed faces; it does not require its parameters
to be in side interiors.

**Theorem.** This entire original E-owned outer-return domain is
impossible.

## 2. Both middle supports give a strict combined inner height

Apply the entire geometric theorem and literal caller

    OBLIQUE_SUPPORT_WITH_LOWER_AND_RIGHT_POINTS_FORCES_SIDE_OWNERSHIP.md
    SHA-256 43cf46d235fa6175403150a763cc435be7c2421847f249f72ab1787f28b40739.

Its complete hypotheses are the unchanged chart (1)--(3), strict
upper H corner normals, and actual BC. It covers every original
B,C support feature and forces genuine B ownership of HB and C
ownership of HC. In particular its whole-unit bounds are

    min_B x+min_B y>1,
    min_C y>max_C x.                                  (4)

The actual BC contact gives min_B x<=max_C x. Therefore

    min_B y+min_C y
       >1-min_B x+max_C x>=1.                         (5)

The same original P_AB belongs to B and P_DC belongs to C.
Substitution from (2)--(3) into (5) gives the strict actual-point
inequality

    (1-rho)*u+(1-kappa)*p-tau_A*v-tau_D*q>1.          (6)

All four subtracted terms and parameters here are original. The
nonnegative tau terms may be dropped only in this numerical
consequence, not from an original force or moment equation:

    (1-rho)*u+(1-kappa)*p>1.                           (7)

Because 0<u,p<1 and 0<rho,kappa<1, this entails both

    u+p>1, rho+kappa<1.                               (8)

No loaded equation or boundary status of B or C was used.

## 3. Actual outer ports are strictly more than one apart horizontally

The unchanged outer points in (2)--(3) have exact coordinates

    T_A=(1+u-rho*v,-v-rho*u),
    T_D=(-p+kappa*q,-q-kappa*p).

Thus their actual horizontal difference is

    dx=(T_A)_x-(T_D)_x
       =1+u+p-rho*v-kappa*q
        >1+u+p-rho-kappa
         >u+p>1.                                     (9)

The first strict comparison uses v,q<1 and rho,kappa>0. The
second and third are exactly (8). In particular the two actual
applications are distinct. There is no virtual grouped contact
or replacement mean in (9).

## 4. Entire equal-axis E row, with both closed face endpoints

If the two original E inward normals are equal, both T_A and T_D
belong to the same minimum-support face of the same unit E.
That full closed face is a side of length one. Hence

    |T_A-T_D|<=1.

But (9) gives |T_A-T_D|>=dx>1, a contradiction. This excludes the
entire equal-axis row, including identical or endpoint-valued
applications before the strict separation is used. It also
excludes every radial parallel exception without invoking a
two-force theorem or deleting any physical circle coefficient.

Opposite E axes are impossible because both original outer normals
have strictly negative world y components. The only remaining
E-axis relation is perpendicularity.

## 5. Full perpendicular E frame and both closed application orders

Two perpendicular own unit axes with strictly negative world y
components must be of the exact form

    e=(a,-b), f=(-b,-a),
    a,b>0, a^2+b^2=1.                                 (10)

The same actual E has a highest vertex V and full pose

    E=V+[0,1]e+[0,1]f.

There are exactly two assignments of these distinct axes to the
original AE and DE normals.

If n_AE=e and n_DE=f, their entire closed support faces give

    T_A=V+s*f, T_D=V+t*e,
    0<=s,t<=1.

Consequently dx=-s*b-t*a<=0, contradicting (9). This covers both
closed endpoints and possible coincident applications in that
reversed assignment.

The remaining whole assignment is therefore

    n_AE=f, n_DE=e,
    T_A=V+s*e, T_D=V+t*f,
    0<=s,t<=1.                                        (11)

No further restriction on the actual s,t is needed below. The
selected original normal has not been changed; (11) is an
exhaustive consequence of actual E support and (9).

## 6. The complete branch a<=b contradicts the original A3

In the assignment (11), the original AE vector is a positive
multiple of f=(-b,-a). Its components in the actual A frame are

    k_A=f.n_A=a*v-b*u>0,
    l_A=-f.j_A=b*v+a*u>0.                             (12)

The first strict inequality is the original positive normal
coefficient Gamma_A+alpha_A in (2). Hence the original magnitude
ratio is exactly

    beta_A/(Gamma_A+alpha_A)=l_A/k_A.                 (13)

Suppose a<=b. Then k_A>0 implies a*v>b*u>=a*u,
so v>u. Furthermore

    l_A-k_A=(b-a)*v+(a+b)*u>0.

Thus the ratio in (13) is strictly greater than one.

If alpha_A>0, its actual support condition gives tau_A=0. The
complete original torque in (2) then gives instead

    beta_A/(Gamma_A+alpha_A)
      =(alpha_A+rho*Gamma_A)/(Gamma_A+alpha_A)<1,

a contradiction.

The only other full force component case is alpha_A=0. The exact
same full torque becomes

    beta_A/Gamma_A=rho/(1-tau_A)>1,
    tau_A>1-rho.

The actual inner-return point in (2) therefore has height

    (P_AB)_y=(1-rho)*u-tau_A*v
                <(1-rho)*(u-v)<0.                    (14)

But the original HB normal is strict Northeast at (1,1). Strict
unit support reach in direction South puts the whole actual B
strictly in y>0, including P_AB. This contradicts (14).

Every original alpha_A and tau_A case has been covered. In
particular the closed parameter equality a=b is included in this
contradiction. The proof has not replaced B by a degree-two body
or used a force equation at B.

## 7. The complete branch b<=a contradicts the original D3

The reflected calculation is recorded explicitly. Its original
DE direction is e=(a,-b), with own D components

    k_D=e.n_D=b*q-a*p>0,
    l_D=-e.k_D_axis=a*q+b*p>0,                         (15)

where k_D_axis=(-q,p) is the tangent denoted k_D in (1)--(3);
the scalar k_D in (15) is used only in the following ratio.
To avoid any application ambiguity, (15) means literally

    beta_D/(Gamma_D+alpha_D)
       =(a*q+b*p)/(b*q-a*p).                          (16)

If b<=a, the strict denominator gives q>p, and the numerator
minus denominator is (a-b)*q+(a+b)*p>0. Thus (16)>1.

For alpha_D>0, tau_D=0 and the complete D3 torque in (3) gives
the opposite strict inequality

    beta_D/(Gamma_D+alpha_D)
      =(alpha_D+kappa*Gamma_D)/(Gamma_D+alpha_D)<1.

For alpha_D=0, that same full torque gives

    beta_D/Gamma_D=kappa/(1-tau_D)>1,
    tau_D>1-kappa.

The unchanged actual inner application would then satisfy

    (P_DC)_y=(1-kappa)*p-tau_D*q
                <(1-kappa)*(p-q)<0.

The original HC normal is strict Northwest at (0,1), so strict
unit support reach in direction South puts the whole actual C
strictly in y>0. The actual P_DC belongs to it, a contradiction.

The exhaustive comparisons a<=b and b<=a cover every positive
unit pair in (10). Thus the entire perpendicular E-axis row in
(11) is impossible. Every closed E-face parameter in Section 5
has been retained; neither endpoint was excluded by a genericity
assumption.

## 8. Complete literal owner-interface conclusion

Both original E-owned normals are actual unit side axes of the
same E. Their relation is equal, opposite or perpendicular.
Section 4 excludes equality and rules out opposite directions;
Sections 5--7 exclude both complete perpendicular assignments.
This proves the stated entire E-owned outer-return theorem.

The separate complete source

    INNER_PENTAGON_ADJACENT_ENDS_ANY_SHARED_INNER_RETURN_EXCLUSION.md
    SHA-256 20225f7fade5c1e4534b8f8efc780cfd8e736efc281af83d51909afa4b2a7004

excludes all original shared inner returns and applies the literal
fixed-singleton preselection rule to both true endpoint stars.
It therefore supplies exactly the two E-owned normals assumed
here in the surviving complete adjacent external-end chart.
Together, after separate complete independent review and root
adoption, these whole sources exclude that entire adjacent class.

That conclusion is assembled at the full original family scope in
a separate complete source. This manuscript does not itself edit
any original flag or count. Every underlying original square,
force, physical circle corner and zero coefficient remains.

## 9. Exact operative inputs and construction disclosure

| Source | SHA-256 | Exact role |
| --- | --- | --- |
| INNER_PENTAGON_ADJACENT_EXTERNAL_ENDS_FOUR_CORNER_AND_OUTER_RETURN_CHART.md | 4d789a72e56cba5b4416f5231cf97fc3145488cfdaec0482ba9fabd808036db3 | Entire original chart, full true A3/D3 force and torque tables, and strict H corner support cover |
| OBLIQUE_SUPPORT_WITH_LOWER_AND_RIGHT_POINTS_FORCES_SIDE_OWNERSHIP.md | 43cf46d235fa6175403150a763cc435be7c2421847f249f72ab1787f28b40739 | Complete force-free middle-owner cover and exact whole B,C support inequalities |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Full strict unit support reach for actual P_AB and P_DC in the original upper H neighbors |
| INNER_PENTAGON_ADJACENT_ENDS_ANY_SHARED_INNER_RETURN_EXCLUSION.md | 20225f7fade5c1e4534b8f8efc780cfd8e736efc281af83d51909afa4b2a7004 | Only the complete whole original caller supplying both E-owned normals, with its independent review and adoption requirement retained |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Entire original force, support, torque and actual mean contract |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a | Literal original graph, genuine unloaded endpoint degrees and permitted full graph reflection |

Root supplied the whole BC support-sum consequence (5)--(9) and
the equal-axis contradiction. Pentagon_owned derived the complete
perpendicular assignment and endpoint ratio contradiction; root
independently reached and verified the same endpoint contradiction
and requested the stronger closed E-face cover. Those are
construction contributions and are not the required separate full
independent review of these exact new bytes.

There is no containing-radius hypothesis in the new theorem. No
equation at loaded B3,C3,E2 is used or shortened. Both actual E
applications and all of its original physical circle masks remain,
including individual zero coefficients. No concurrence point,
boundary-neighbor premise, sampled angle, numerical geometric
certificate, Lean or Lake run, old checker replay, CI, workflow,
old-source repinning, original flag/count mutation, commit or remote
operation enters this source. Separate full independent review
and root adoption are required before treating it as an accepted
whole original owner-interface exit.
