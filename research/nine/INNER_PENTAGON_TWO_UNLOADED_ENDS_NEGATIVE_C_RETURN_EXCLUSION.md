# Two unloaded ends exclude the negative vertical C-return row

Date: October 28, 2026 UTC. Author: pentagon_uniform continuation.

**Status: complete proposed radius-free original-interface exclusion,
frozen for full independent and root review. Together with the two
separately pinned sign results, it closes every strict-Northeast HC
feature when H owns HD and both rim ends are unloaded. The East-HC
feature and the other HD owners remain outside this source.**

The proof uses the complete original H4, A3 and D3 equations, the
unchanged physical side intervals, and actual AB, BC and AE contacts.
It requires no circle equation, physical boundary mask, radius bound,
or concurrence assertion at a loaded body. In particular the original
C3 and E2 in its L124 application remain intact.

## 1. Exact physical and selected domain

Retain the actual six unit squares and original positive contacts

    HA, HB, HC, HD, AB, BC, CD, DE, EA.

H is unloaded of true positive degree four. A and D are both unloaded
of true positive degree three, with their full original neighborhoods
H,B,E and H,C,E respectively. The actual B,C,E retain their original
degrees, loads, force equations and every physical contact. Every
unit is interior-disjoint from every other actual unit.

Use the complete H-owned-HD reduction and the compatible selected
external ownership theorem, at the literal pins below. They supply
the following exact chart without changing a normal or an application:

    H=[0,1]^2, n_HD=North,
    n_HA strictly Southwest, n_HC strictly Northeast,
    P=(p,1), 0<p<1, q=1-p,
    D=P+[0,1](a,b)+[0,1](-b,a),
    a,b>0, a^2+b^2=1.

The original HD magnitude is gamma>0. The complete original D3
equations give an original positive parameter eta and the vectors

    X=eta*(a+b)+gamma*a*b>0,
    Y_C=eta*(b-a)+gamma*b^2,
    Y_E=eta*(a-b)+gamma*a^2,
    Y_C+Y_E=gamma.                                      (1)

The actual D-to-C force (X,Y_C) is applied at R=P+(a,b).
The actual D-to-E force (-X,Y_E) is applied at L=P+(-b,a).
These are physical singletons. C owns CD and E owns DE at strict
relative-side-interior points, with their complete original side
intervals retained.

**Theorem.** The entire domain above with Y_C<0 is impossible.

From (1), this sign forces a>b and

    Y_E=gamma+|Y_C|>|Y_C|>0.                             (2)

The complete height/owner reduction, whose conclusions in the
strict-Northeast HC branch hold for every sign of Y_C, gives

    n_HB strictly Southeast,
    min_B x>0, max_B y<1,
    min_E y>0,
    A owns HA at its actual side-interior point (0,0).    (3)

Its actual C feature cover in the present negative sign branch is
as follows. Define

    N_C=sqrt(X^2+Y_C^2),
    c=X/N_C>0, s=|Y_C|/N_C>0,
    n=(c,-s), j=(s,c), c^2+s^2=1.

At the unchanged HC point S=(1,1), the entire actual C has the pose

    C=S+[-U_C,1-U_C]n+[0,1]j, 0<=U_C<1.                 (4)

The free HC alternative has U_C=0. In the perpendicular C-owned HC
alternative, 0<U_C<1. In both cases the original HC direction N has

    N.n>=0, N.j>0.                                      (5)

In particular the complete original side mean in the second case is
not replaced by an endpoint. The actual minimum-CD support comparison
at S also gives

    q*X>=eta+gamma*b.                                   (6)

These are the complete two C features of the negative row; no further
HC owner is omitted.

## 2. A general consequence of the full original unloaded A3

We now rederive the required A3 conclusion over the whole physical
domain (3), independently of the sign-specific older positive-return
argument. Write the original A-owned axis and its full side interval as

    n_A=(-u,-v), j_A=(v,-u),
    u,v>0, u^2+v^2=1,
    A=[0,1]n_A+[-kappa,1-kappa]j_A, 0<kappa<1.            (7)

The actual A-to-H force is -Gamma*n_A at (0,0), where Gamma>0 is its
original magnitude. The frame (n_A,j_A) has positive orientation.

The physical A-H-B triangle and the A-owned AH normal imply that the
original AB direction has n_A component at most zero. Its j_A component
cannot be negative: that would place its entire A support on tangent
coordinate -kappa, whose world x coordinate is

    -tau*u-kappa*v<0, 0<=tau<=1.

Every actual point of B has positive x by (3). Thus this whole support
feature is impossible, including both endpoints.

### 2.1. The entire parallel AB alternative

If the j_A component is zero, the original AB vector is -beta*n_A,
with beta>0. Its unchanged original support mean has the form

    T_B=t_B*j_A, -kappa<=t_B<=1-kappa.

Because it belongs to B, t_B*v>0 and hence t_B>0. The full original A3
force equation makes its AE vector (Gamma+beta)*n_A, applied at an
original point n_A+t_E*j_A of the opposite side. The full A3 torque
about its actual H application is

    beta*t_B-(Gamma+beta)*t_E=0.

Consequently t_E>0. This actual AE point has world height
-v-u*t_E<0, contradicting the whole-unit fact min_E y>0. This excludes
the complete parallel alternative with every original side mean kept
until the contradiction.

### 2.2. Every remaining AB feature and the actual AE vertex

The remaining original AB vector is exactly

    F_AB=-rho*n_A+sigma*j_A, rho>=0, sigma>0.

Its original A application is on the positive-j_A side. Write it as

    Z=tau*n_A+(1-kappa)*j_A, 0<=tau<=1.                  (8)

If rho>0, its actual support is tau=0. If rho=0, the entire side
interval remains; equation (8) covers every original mean.

The complete A3 force equation now gives

    F_AE=(Gamma+rho)*n_A-sigma*j_A.

Both own components are strict, so its actual A application is the
fixed exposed vertex

    T=n_A-kappa*j_A,
    T_y=kappa*u-v.                                      (9)

Since this actual point belongs to E, (3) implies

    kappa>v/u, u>v, and 0<T_y<u-v.                      (10)

The last inequality uses the strict original side position kappa<1.
It concerns the one actual AE point, not a bound on the whole A.

We also have the exact uniform estimate

    (1-kappa)*(u+v)
      <(1-v/u)*(u+v)
       =2*u-1/u<1.                                     (11)

Indeed u<1 and 2*u^2-u-1=(2*u+1)*(u-1)<0.

Write the unchanged original H-to-B vector as (x,-y), x,y>0.
Its actual H application and minimum support of B is (1,0).
The actual AB point in (8) has

    Z_x=-tau*u+(1-kappa)*v,
    Z_y=-tau*v-(1-kappa)*u.

Thus 1-Z_x>0 and -Z_y>0. Equations (10)--(11), for the complete
closed interval 0<=tau<=1, give

    (1-Z_x)-(-Z_y)
      =1+tau*(u-v)-(1-kappa)*(u+v)>0.                    (12)

The original minimum support inequality on this same B is

    x*(Z_x-1)-y*Z_y>=0,
    x*(1-Z_x)<=y*(-Z_y).

Therefore

    x<y.                                               (13)

We have established (9)--(13) using the full actual A3 and the physical
triangle and contact facts (3). No circle or B equation, and no
positive-Y_C premise, entered this deduction.

## 3. The full H4 compares the actual A and C axes

Write all four unchanged H vectors as

    F_HA=(-U,-V), F_HB=(x,-y),
    F_HC=(r,t), F_HD=(0,gamma),
    U,V,x,y,r,t,gamma>0.

Their actual applications are respectively
(0,0),(1,0),(1,1),(p,1). The complete original H4 force and torque
equations yield

    U=x+r, V=r+q*gamma,
    y=t-r+p*gamma.                                      (14)

The original A-owned unit axis in (7) is
(-U,-V)/sqrt(U^2+V^2); in particular u/v=U/V.

Using (1), the actual support inequality (6) is equivalently

    eta*[q*(a+b)-1]>=gamma*b*(1-q*a)>0.

Here q*a<1. It follows that

    q>1/(a+b)>=1/sqrt(2)>1/2, hence p<q.                 (15)

The exact force expressions also give

    X-|Y_C|=X+Y_C=2*eta*b+gamma*b*(a+b)>0.

Thus c>s. Put K=c/s>1. The first actual HC cone inequality in (5),
applied to its original positive force (r,t), gives

    c*r-s*t>=0, hence t<=K*r.                           (16)

By (13)--(16), the full original equations imply

    U=x+r<y+r=t+p*gamma
      <=K*r+p*gamma<K*(r+q*gamma)=K*V.                  (17)

The last strict comparison uses gamma>0 and p<q<K*q.
Since both (u,v) and (c,s) are positive unit pairs, (17) is precisely
u/v<c/s. The monotonicity of z/sqrt(1+z^2) on positive z gives

    u<c, v>s, and T_y<u-v<c-s.                          (18)

This includes the endpoint equality in (16), namely the entire
C-owned perpendicular HC feature. It did not require making that
normal free or selecting a new mean.

## 4. The actual BC contact provides a uniform geometric margin

At its actual minimum support (1,0), B has normal
(x,-y)/sqrt(x^2+y^2). The sharpened whole-unit support-span lemma,
applied in the positive y direction, gives

    max_B y<=x/sqrt(x^2+y^2)<1/sqrt(2),                  (19)

where the strict inequality is (13). This bound holds for every B
frame and owner, including every original side mean.

The full physical C pose (4) gives exactly

    min_C y=1-(1-U_C)*s>=1-s.

Because the actual B and C touch, their y intervals meet. Hence (19)
forces

    s>1-1/sqrt(2)>1/4.                                 (20)

The last rational comparison follows from 1/sqrt(2)<3/4.
Since c^2+s^2=1,

    c^2<15/16<(39/40)^2, hence c<39/40.                  (21)

For transparency the squared reserve in the middle comparison is
21/1600>0. Equations (20)--(21) imply

    2*c-s<2*(39/40)-1/4=17/10.                          (22)

On the other hand Y_C<0 forces a>b, so

    a>1/sqrt(2)>7/10, hence 1+a>17/10.                   (23)

Combining (22)--(23) supplies the strict, radius-free margin

    1+a>2*c-s.                                         (24)

All strictness comes from original positive forces, actual side
interior positions, or the physical contact comparison. There is no
sampling of the square frames or of the force parameters.

## 5. The entire actual E lies above its required AE point

By (2), define the unchanged E-owned DE frame

    N_E=sqrt(X^2+Y_E^2),
    c_E=X/N_E,
    n_E=(-X,Y_E)/N_E,
    j_E=(-Y_E,-X)/N_E.

Then 0<c_E<c, because Y_E>|Y_C|. The selected strict side-interior
DE application L has height L_y=1+a, and the whole actual E is

    E=L+[0,1]n_E+[ell_E,ell_E+1]j_E,
    -1<ell_E<0.                                        (25)

The positive normal coordinate increases y; the positive tangent
coordinate decreases y. Therefore the exact lowest height is

    min_E y=1+a-(ell_E+1)*c_E
           >1+a-c_E>1+a-c.                             (26)

The complete original ell_E interval is present in this calculation.
By (24), 1+a-c>c-s; by (18), c-s>T_y. Thus

    min_E y>c-s>T_y.                                   (27)

But T from (9) is the original AE application and belongs to E.
This contradicts (27), proving the whole declared negative-Y_C row.

## 6. Complete strict-Northeast union and literal original scope

The three disjoint sign alternatives for the original scalar Y_C
are now exhausted in the common selected H-owned-HD domain with
both unloaded end stars:

| Original sign | Complete exclusion |
| --- | --- |
| Y_C>0 | The separately frozen positive-return theorem, using the complete H4 and A3 |
| Y_C=0 | Section 3.1 of the separately frozen height/owner reduction: the actual C support feature would force its original strictly Northeast HC normal to be East |
| Y_C<0 | Sections 1--5 of this source |

Consequently every original strict-Northeast HC feature in that
domain is impossible, with every free or owned return, original side
interval and physical mask retained.

For H4_D0.L124 substitute (A,B,C,D,E)=(0,1,2,3,4). Both A and D
then have exactly the genuine unloaded degree-three stars used
above. H retains its full four forces; B,C retain their full loaded
degree-three stars; E retains its full loaded degree-two star.
The result applies whether the unloaded ends are physically clear
or touch the containing circle with total coefficient zero. The
permitted graph reflection gives the same conclusion when the
H-owned end is the other unloaded end.

This proof does not assign A3 to the loaded A of H4_D0.L0124.
That family has its separate four-boundary proof. In L124 the
East-HC case, the other HD owners, and the entire remaining
three-boundary assembly require their own arguments. The present
source therefore claims no whole original fine-family closure.

## 7. Exact operative pins and limits

| Source | SHA256 | Exact use |
| --- | --- | --- |
| INNER_PENTAGON_OWNED_END_RETURN_HEIGHT_AND_OPPOSITE_END_OWNER_REDUCTION.md | 23bb6edea9c4988b64636070ebe53acca5ca6617ddf7f595054948fdb8453c4b | All-sign E height and A ownership; complete negative-row C pose and HC cone; zero-sign exclusion |
| INNER_PENTAGON_H_OWNED_UNLOADED_END_FIXED_OPPOSITE_RETURN_VERTICES.md | bc1b08bc93401e25891f1307139c465409e4a3e260670513087b658c210e0f8c | Actual opposite D vertices, complete D3 expressions, support inequality, sharpened whole-unit support span |
| FIXED_SINGLETON_THREE_FORCE_OFF_LINE_NORMAL_SELECTION_AND_H4_OWNED_END_REDUCTION.md | d5e02f317ecbfdbd3d948fd27f5f78d6eda8803fb679c435ef3101780e1f47b1 | Existing compatible C/E-owned returns and strict original side positions; no later normal change |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual A-owned AH axis in the physical A-H-B triangle |
| INNER_PENTAGON_TWO_UNLOADED_ENDS_POSITIVE_C_RETURN_EXCLUSION.md | 50c72f0ead283c957fa466ff6a368d4d4be7e4473791645609975117a444bed1 | Only the separate positive-sign row in Section 6; no sign-restricted A3 conclusion imported into the new negative proof |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a | Literal L124 graph, true unloaded end degrees and permitted reflection |

The theorem is radius-free after these exact physical and selected
owner premises. Every original force, actual contact set, mean,
positive degree, physical circle mask and completion square is
retained. No frozen input, ledger, gate count, roadmap or handoff
is edited. No numerical geometric exclusion, Lean compilation,
CI, commit or remote operation is part of this manuscript.
