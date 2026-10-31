# Complete shared-side return exclusion for a unique C

Date: October 25, 2026.

**Status: complete hand proof; independent full saved-source,
direct-prerequisite, analytic-domain and exact-arithmetic review passed
on October 25, 2026. See REVIEW_ABC_SHARED_SIDE_AND_FAR_SIDE_2026_10_25.md.
This closes the stated complete feature, not a whole UUU gate; no ID changes.** This source excludes the entire genuinely
shared minimum-f BC return with physically unique C in the original
upper-left B-owned AB family. It creates no gate and changes no checkbox.
The strict B-owned singleton BC return with a tilted unique C remains
outside this theorem.

Retain the original H--A--B--C--H component, true H4/A2/B2/C2, intact HXY
petal, all nine physical squares and all three completion squares. A and
B are physically unique. A has its original negative H-pressure, HA is
H-owned, and AB is its original B-owned upper-left singleton. Every
selected force, application mean, physical containment and nonoverlap
condition is unchanged. The full original radius interval is

    q0=6241/1600 <= q <= Q0=1105/256.

The proof uses the actual A2 and B2 equations and physical H/B
nonoverlap. It does not substitute a new normal or place a variable
shared mean at a fixed tip. The H4 and completion hypotheses remain
present even when an individual geometric step does not need them.

## 1. Original coordinates and the complete C-corner cover

Use the original upper-left chart

    zA=(a,b), a>b>3/5, a^2+b^2=q,
    x=a-1, P=(x,b-1), T=(x,b), T-P=e_y,
    f=(s,c), g=(-c,s), c,s>0, c^2+s^2=1,
    n=(u,v), j=(-v,u), 0<u<=v, u^2+v^2=1,
    H=P+[-1,0]n+[r-1,r]j, 0<r<1,
    E=n dot f=su+cv>0, D=n dot g=sv-cu,
    L=T dot f=xs+bc>0, h=T dot g=-xc+bs.

Thus (f,g) is positively oriented,

    n=E f+D g, j=-D f+E g, E^2+D^2=1,
    c=vE-uD, s=uE+vD,
    P=(L-c)f+(h-s)g.                              (1)

For the actual side normal k_BC=-f, the true B2 force equation is

    lambda_B zB=gamma g+nu f, lambda_B,gamma,nu>0.

Consequently its actual circle corner and physical square are

    zB=beta f+Wg, beta,W>0, beta^2+W^2=q,
    B=[beta-1,beta]f+[W-1,W]g,
    h=W-1, 0<tau=beta-L<1,
    delta_B=1-tau=1+L-beta in (0,1).

Physical uniqueness gives W>1/2. The original B moment, including the
actual mean of the shared BC interface, is

    gamma L=nu eta,  eta=L W/beta>0,
    Q=(beta-1)f+eta g.                            (2)

The unchanged radius identity is

    beta^2=L^2+2Ls-2h(1+c),
    a=W+(beta^2-L^2)/2>W, b<beta.                (3)

Because BC is genuinely shared, f is also a C side axis and C has
f interval [beta-2,beta-1]. Positive eta in its proper C2 concurrence
forces its actual circle corner to have positive g coordinate. Its
farther f endpoint is therefore the following complete physical cover:

* beta>3/2: the positive-f endpoint U=beta-1;
* beta<3/2: the negative-f endpoint U=beta-2;
* beta=3/2: a physical radial C, already covered by the full radial
  shared-side theorem.

The complete corrected source
ABC_UNIQUE_SHARED_SIDE_POSITIVE_CORNER_EXCLUSION.md excludes the first
alternative, with every HC owner and mean retained. The equality case is
excluded by NEGATIVE_H_OWNED_UPPER_LEFT_SIDE_RADIAL_SHARED_EXCLUSION.md.
It remains to exclude the entire beta<3/2 alternative, which is done
below. Put

    A0=2-beta>0, U=-A0,
    V=sqrt(q-A0^2)>0, Delta=V-W,
    C=[U,U+1]f+[V-1,V]g, zC=U f+Vg,
    qC=kappa zC, kappa=eta/V in (0,1].            (4)

Here qC is the original proper C2 concurrence, not a replaced load
point. The unchanged shared BC mean satisfies

    max(W-1,V-1)<=eta<=min(W,V).

## 2. Two prefix restrictions from negative A and the actual radius

### 2.1. Negative A gives r>u

This is the degree-independent A/H computation in Section 2 of
NEGATIVE_H_OWNED_UPPER_LEFT_DIAMOND_HK_CONTACT_FAN.md; no K equation or
contact is used. Since zA dot j=bu-av<0, the pressure decreases with r.
At r=u it equals q-aA-bB, where

    A=1+(u-v)/2+uv, B=1+(u+v)/2-u^2,
    A^2+B^2=5/2+u-u^2+2uv <=15/4.

Completing two squares therefore gives, for every r<=u,

    c_H dot zA >= (q-15/4)/2 >=241/3200>0.

The actual negative endpoint thus has

    r>u.                                        (5)

### 2.2. If beta<=3/2, then delta_B>c

Suppose delta_B<=c. Then beta>=L+1-c and L<=1/2+c. Squaring the first
positive comparison and using (3) gives

    h <= [L(s+c-1)-(1-c)^2/2]/(1+c)
      <= [(c+1/2)s+(c^2+c)/2-1]/(1+c).           (6)

The second inequality uses s+c-1>0. The final expression is strictly
below 7/25 on the whole c interval [0,1]. Here is a direct algebraic
proof, with no angle selection. The desired comparison is

    (c+1/2)s < (64-11c-25c^2)/50.

Its right numerator is at least 28. The difference of the squared
sides, multiplied by 2500 and using s^2=1-c^2, is

    P(c)=3471-3908c-4954c^2+3050c^3+3125c^4.

Writing y=c-4/5 in [-4/5,1/5] gives the exact identity

    P(c)=391/25+(2108/5)y
         +y^2(14366+13050y+3125y^2).

The expression in parentheses is increasing on this interval and at
its left endpoint equals 5926. Hence

    P(c)>=5926y^2+(2108/5)y+391/25>0,

where the final strict quadratic comparison follows from

    4*5926*391-2108^2=4824600>0.

Thus (6) implies h<7/25 and W<32/25. This contradicts

    q=beta^2+W^2 <9/4+(32/25)^2 <q0,
    q0-9/4-(32/25)^2=489/40000>0.

We have proved on the full beta<=3/2 prefix that

    delta_B>c.                                  (7)

## 3. Actual H/B nonoverlap forces D>0

Suppose D<=0. The separating-axis theorem for the two actual squares
uses precisely their side axes f,g,n,j. From (1), (5) and (7), their
four forward projection gaps are

    max_H f-min_B f=delta_B-c-rD>0,
    max_H g-min_B g=(r-u)E-(v+1)D>0,
    max_H n-min_B n=E(delta_B-c)-(s+1)D>0,
    max_H j-min_B j=r-u-D delta_B>0.              (8)

The reverse gaps are also strictly positive. Indeed P belongs to H,
T belongs to B, and T-P=e_y has positive projections c,s,v,u on these
four axes. Thus max_B(axis)>min_H(axis) for each axis. All four pairs
of projection intervals overlap in their interiors. The separating-axis
theorem then gives int(H) intersect int(B) nonempty, contrary to actual
physical nonoverlap.

Therefore every original surviving side prefix with beta<=3/2 has

    D>0.                                        (9)

This conclusion has used no C owner, circle mask, force or contact
assumption. It will be applied here only to the actual shared C row.

## 4. Elementary bounds and the full HC fan for negative-f C

Since beta<3/2, W>sqrt(q-9/4)>1, so h>0. The original c>0 gives
Lb>hx. Squaring these positive sides and using
L^2+h^2=x^2+b^2 yields b>h. Together with (3), this gives

    x>h>0, h<b<beta, W<beta+1.

If beta<=4/5, then q<beta^2+(beta+1)^2<=97/25<q0, a contradiction.
Consequently

    4/5<beta<3/2, A0<6/5, V>3/2>A0.             (10)

The last strict bound follows by squaring q0-(6/5)^2>9/4.
Also

    Delta+s>0.                                  (11)

For beta>=1 this is immediate. If beta<1, W>17/10 and V>3/2 give
-Delta=4(1-beta)/(V+W)<1/4, while h=bs-xc<bs and b<beta<1 imply
s>h>7/10. This proves (11) and the useful universal bound Delta>-1/4.

Let m be the actual H-to-C unit normal, R its original application
mean, and lambda_C,mu_C,nu>0 the unchanged C circle, HC and BC
magnitudes. The true C equations are

    lambda_C zC=-nu f+mu_C m,
    mu_C det(R,m)=-nu eta<0.                     (12)

Thus m_g>0, so the entire physical HC support fan is C's minimum-g
side or its two endpoints. At the strict right endpoint
R=(U+1)f+(V-1)g, proper concurrence gives a positive multiple of
qC-R as m, and

    det(R,qC-R)=kappa(U+V)>0,

contradicting (12). The vector cannot vanish because coincidence would
force V=-U, excluded by (10). At the strict left endpoint,

    R_L=U f+(V-1)g,
    qC-R_L=A0(1-kappa)f+[1-(1-kappa)V]g,

and both components are positive by the actual strict vertex feature.
For the side m=g, the unchanged proper concurrence fixes the original
side mean as

    R_S=kappa U f+(V-1)g.                        (13)

Either endpoint of the actual shared HC mean remains included in (13).
The whole surviving HC fan is therefore m=g, or the strict left
endpoint with m_f,m_g>0. No owner, free normal or mean has been
silently removed.

By (9), each surviving normal has

    m dot n=E m_f+D m_g>0.

Its actual common contact application therefore lies on H's front
n side. It has R=P+t j with t in [r-1,r], and in particular

    |R-P|<1.                                    (14)

For the two actual remaining C applications, set

    M_S=L+kappa A0=L[1+(W/V)(A0/beta)],
    M_L=L+A0>=M_S.

Their displacements are exactly

    R_S-P=-(M_S-c)f+(Delta+s)g,
    R_L-P=-(M_L-c)f+(Delta+s)g.                  (15)

## 5. The entire 4/5<beta<=5/4 range contradicts (14)

Two bounds valid throughout (10) simplify this comparison. First,
h=bs-xc and h<b<beta, x>h give

    h(1+c)<beta s,
    s/(1+c)>h/beta.                             (16)

For any lower bound h/beta>t in (0,1), this implies
c<(1-t^2)/(1+t^2) and s>2t/(1+t^2).

Second, put F0=beta^2+2W-1. Since a<sqrt(q-h^2)=sqrt(F0),

    L^2=beta^2+2W-2a>(sqrt(F0)-1)^2.

On the entire domain W>1, F0 increases in beta and q. At beta=4/5,
q=q0, we have W>9/5 because q0-16/25-81/25=33/1600>0. It follows that
F0>81/25 and

    L>4/5.                                      (17)

### 5.1. The full range 4/5<beta<=11/10

Here W>41/25 because

    q0-121/100-(41/25)^2=41/40000>0.

Thus h/beta>32/55. By (16),

    c<2001/4049<1/2, s>3520/4049>6/7.

We also have W/V>9/10. This is immediate for beta<=1. For beta>=1,
the squared ratio

    (W/V)^2=(q-beta^2)/(q-(2-beta)^2)

increases with q and decreases with beta; its endpoint is
4305/4945>81/100. Since A0/beta>=9/11, (17) gives

    M_S>(4/5)(1+81/110)=382/275,
    M_S-c>489/550,
    Delta+s>-1/4+6/7=17/28.

Hence both actual squared distances in (15) exceed 1, since

    (489/550)^2+(17/28)^2-1=9433341/59290000>0.

This contradicts (14), including every actual mean endpoint.

### 5.2. The full range 11/10<=beta<=5/4

The same ratio comparison now gives W/V>5/6, because its squared
endpoint is 3741/5341>25/36. Since A0/beta>=3/5,

    M_S>(3/2)L.

Monotonicity of F0 gives F0(beta,q)>=F0(11/10,q0). At that comparison
endpoint alone W=sqrt(q0-121/100)>41/25, so

    F0>349/100>(93/50)^2, L>43/50.

Also W>55/36 since

    q0-25/16-(55/36)^2=521/129600>0.

Thus h/beta>19/45, and (16) gives

    c<832/1193<7/10, s>855/1193>5/7.

Using V+W<2sqrt(q)<21/5,

    Delta=4(beta-1)/(V+W)>2/21.

Consequently

    M_S-c>59/100, Delta+s>17/21,
    (59/100)^2+(17/21)^2-1=15121/4410000>0.

Both actual distances in (15) again contradict (14). The entire
beta<=5/4 range is excluded, without sampling a pose or changing an
offset.

## 6. The full 5/4<=beta<=7/5 range has a strict g separator

It suffices in the remaining ranges to prove

    Delta+s>1.                                  (18)

Indeed (9) gives

    max_H g=W-1-s+rE <W-s,
    min_C g=V-1,

so (18) strictly separates the two actual squares and forbids HC,
regardless of its owner or original application mean.

By (16), with D0=beta^2+h^2,

    s>s0=2beta h/D0.

Since h+2-s0>0, the sufficient comparison V>h+2-s0 can be squared
without reversing its meaning. Its exact cleared difference is

    D0^2[V^2-(h+2-s0)^2]
      =P(beta,h)
      =(4beta-2h-7)D0^2
        +4beta h(h+2)D0-4beta^2 h^2.             (19)

The entire original range in this section lies in the single rational
trapezoid

    5/4<=beta<=7/5,
    33/20-9beta/10 <h<2/3.                      (20)

For its lower boundary, q0-beta^2-(53/20-9beta/10)^2 is concave in
beta and has endpoint reserves 1/80 and 341/40000, both positive.
For its upper boundary, W^2<=Q0-25/16=705/256<25/9.

Parameterize the entire closed enlargement of (20) by lambda,z in [0,1]:

    B0=750+90z,
    H0=315-81z+lambda(85+81z),
    beta=B0/600, h=H0/600, D1=B0^2+H0^2.

The exact integer polynomial

    G=(4B0-2H0-4200)D1^2
       +4B0 H0(H0+1200)D1-2400B0^2 H0^2
      =600^5 P(beta,h)                           (21)

has coefficient gcd 2. Its primitive polynomial G/2 has degree (5,5)
in (lambda,z). Write its ordinary coefficients as p_rs. Its Bernstein
coefficients on the whole square are defined exactly by

    b_ij=sum_{r<=i,s<=j} p_rs
          binom(i,r)/binom(5,r) * binom(j,s)/binom(5,s).

Every one of these 36 coefficients is strictly greater than
(2/3)b_00>0. For a compact exact audit display, the rows of
floor(100 b_ij/b_00) are

    100  102   97   88   76   68
    280  333  388  447  513  592
    464  571  688  818  966 1137
    654  816  999 1205 1441 1712
    849 1070 1323 1612 1944 2326
   1051 1334 1662 2042 2481 2988

ABC_UNIQUE_SHARED_SIDE_MIDDLE_INTERVAL_CHECK.py rebuilds (21) from
integer arithmetic, separately rebuilds the rational scalar (19),
compares every ordinary coefficient of their normalization, computes
all 36 exact rational b_ij, and reconstructs all 36 ordinary
coefficients through the complete inverse Bernstein identity. The
corresponding exact powers and rational coefficients are saved in
ABC_UNIQUE_SHARED_SIDE_MIDDLE_INTERVAL_CERTIFICATE.json. No sampled
substitution or numerical positivity test is used.

The Bernstein basis is nonnegative and sums to one on [0,1]^2, so
P>0 on the entire closed enlargement. Equation (19) proves
V>h+2-s0 and therefore Delta+s>1. This excludes the whole range (20).

## 7. The full 7/5<=beta<3/2 range has the same strict separator

Put t0=sqrt(q/2)>1. Since a>b, a>t0>b. Therefore

    h=bs-(a-1)c<t0 s-(t0-1)c.

Suppose (18) fails. Here 0<Delta<1, so s<=1-Delta and the strictly
increasing function t0 s-(t0-1)sqrt(1-s^2) gives

    h<t0(1-Delta)-(t0-1)cstar,
    cstar=sqrt(Delta(2-Delta)).

It suffices to prove on this entire range that

    F(q,beta)=W-1-t0(1-Delta)+(t0-1)cstar>0.      (22)

For fixed q let

    C0=t0+(t0-1)(1-Delta)/cstar>t0>1.

The actual derivative is

    F_beta=-beta/W+C0[(2-beta)/V+beta/W]>0.

Thus it is enough to treat the whole q interval at beta=7/5. There
V<2 and W<31/20, so

    Delta=8/[5(V+W)]>32/71>9/20.

Also W>139/100>27/20 and
V^2-(W+1/2)^2=27/20-W<0, hence Delta<1/2. We obtain

    cstar>4/5, t0<3/2,
    C0<3/2+(1/2)(11/20)/(4/5)=59/32<2.

In particular C0 Delta<1<V and Delta+cstar-1>0. Differentiating
at this fixed beta gives the exact identity

    F_q=[V-C0 Delta]/(2WV)
          +(Delta+cstar-1)/(4t0)>0.              (23)

The minimum in (22) is therefore at q=q0,beta=7/5. At that endpoint
direct rational squares give

    W>1393/1000, V>47/25, W<279/200,
    Delta>97/200, cstar>857/1000, t0>139/100.

The expression in (22) increases separately in W, Delta, cstar and
t0 on these comparisons: its last derivative is Delta+cstar-1>0.
Consequently

    F>393/1000-(139/100)(103/200)
                     +(39/100)(857/1000)
      =569/50000>0.

This proves (22), contradicts the assumed failure, and establishes
the strict separator (18) on the entire final interval.

## 8. Exact whole-family join and remaining scope

Sections 5--7 cover every beta in (4/5,3/2). Section 4 proved that
this includes every negative-f unique-C shared return. Section 1
joins the already reviewed positive-f alternative and the physical
radial equality case. Thus the entire original genuinely shared
minimum-f BC return is excluded, with every HC owner, free normal,
application mean and mean endpoint retained until actual geometric
exclusion. In particular no coincident-load or fixed-tip assertion
was used at a variable shared BC mean.

For unique C the proof combines the complete corrected positive-corner
source with the full negative-corner argument here. The already
accepted radial shared theorem supplies the other physical C mask.
This is a complete original BC owner feature, not a new gate. It does
not close the entire B-owned AB leaf or the UUU parent: strict
B-owned singleton minimum-f BC with tilted unique C, and the separate
strict far unique-C return, are not excluded by this source.

All original degrees, all three completion squares and the intact
petal remain unchanged. No Lean compilation or CI was run.
