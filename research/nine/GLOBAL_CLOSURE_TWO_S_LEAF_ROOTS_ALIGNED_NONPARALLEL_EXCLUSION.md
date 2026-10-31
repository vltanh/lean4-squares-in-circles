# An aligned S-leaf root cannot have nonparallel cycle forces beside an origin-interior S-leaf root

Date: October 26, 2026.

**Status: complete proposed whole local interface theorem, pending full
root and independent review.** No original label or ledger is changed.

Keep all original physical squares and the common compatible selected
certificate in

    79/40<=R<=sqrt(1105)/16.

Let H,A,B be an actual positive triangle. A has exactly one other
positive pair edge, to its genuine radial S leaf. B has its true
positive degree two and positive total circle load. H contains O in
its open interior, has its own genuine radial S leaf, and retains its
arbitrary additional original forces. No equation replacing those
forces by H's leaf is imposed. The A frame is aligned with its own
S leaf.

**Theorem.** A's two actual positive triangle forces cannot be
nonparallel. Every physical B mask, original side mean, circle-weight
endpoint, contact owner and additional H force is retained.

The compatible selectors used below are exactly the old finite
aligned-A-star and fixed-tip selections. They do not use a degree-two
equation or a prescribed external force at H.

## 1. The full inherited physical chart and its precise scope

Suppose the A cycle pair is nonparallel. Rotate its leaf east and put

    D=sqrt(R^2-1/4)-1, epsilon=D-1,
    A=[epsilon,epsilon+1] x [h-1,h], w=1-h.

Use the complete feature and selector proof in
TIP_LEAF_BOWTIE_S_ALIGNED_NONPARALLEL_EXCLUSION.md Section 1. That
proof uses A's true leaf equation, the physical triangle side-normal
and support-span facts, and the distinct A-vertex determinant. It
does not use the later identification of H's full external force
with a single intact-petal sum. Its full conclusion, after reflection,
is that the unchanged applications and normals are

    P=(epsilon,h) in A intersect B,
    Q=(epsilon,-w) in A intersect H,
    n=(-b,a), v=Jn=(-a,-b),
    m=(-d,-c), k=Jm=(c,-d),
    a,b,c,d>0, a^2+b^2=c^2+d^2=1,
    K=a*d+b*c>0, L=b*d-a*c,
    h=a*d/K, w=b*c/K.                                  (1)

Here n points A to B and m points A to H. Both contacts are genuine
relative-side-interior applications on their neighbor-owned sides.
No endpoint-valued shared mean has been frozen. The normal letters
c,d are separate from the radial leaf radius D.

In H coordinates n=Lm-Kk and v=Km+Lk. Set

    q_m=Q.m=-epsilon*d+w*c,
    q_k=Q.k=epsilon*c+w*d.                              (2)

Since H lies on the m-outward side of its AH support and O is in
int H, q_m<0. This directly replaces the old Section 2 use of a
single petal's negative concurrence. It implies

    0<epsilon<1/60, -epsilon<q_m<0,
    R>sqrt(17)/2, h>16/25.                              (3)

The last bound is the boundary-point estimate at the actual P; the
full numerical derivation is that source's equations (10)--(11).

The old Sections 3--5 now apply as genuine A/B geometry, with all
their hypotheses unchanged. Their exact consequences needed here are

    B has one physical circle corner and nonparallel pair forces,
    L>0, a<19/20,
    the actual BH normal is either g=v or g=k.           (4)

For clarity, the first circle-mask exclusion uses the actual B-own
side support and the original boundary radius; the nonparallel
claim uses B's actual side-axis contact. The L and a bounds use
only B's proper circle-ray advance and the true A equations.
The complete BH owner cover uses n.g<=0, m.g>=0 and the compatible
fixed-tip selector at two distinct physical applications. None of
these steps uses H's full external force direction.

Write the entire original B as

    p_n=P.n=-epsilon*b+h*a,
    B0=-P.v=epsilon*a+h*b>0,
    X=1+p_n, Y=B0+rho, 0<rho<1,
    V=1-rho in (0,1),
    B=P+[0,1]n+[-rho,1-rho]v,
    z_B=X*n-Y*v, X^2+Y^2=R^2.

Its actual positive proper concurrence is

    q_B=P+A_B*n=(B0/Y) z_B,
    A_B=X*B0/Y-p_n>=0,
    A_B-V=-(1-V)*(X-Y)/Y.                              (5)

The unchanged H chart is

    H=Q+[0,1]m+[-sigma,1-sigma]k, 0<sigma<1,
    p=q_k+1-sigma.

The exact old contact identities are

    g=v:  t=(c-K*V)/L, sigma=(b-V)/L, 0<=t<=1,
          T=P+t*n+V*v=Q-sigma*k, A_B=t;

    g=k:  j=K*V-c, sigma=d-L*V, 0<=j<=1,
          T=P+V*v=Q+j*m-sigma*k,
          A_B=K*V/L.                                  (6)

The last equality follows by intersecting the actual k line through
T with the AB n line. All physical endpoint values of t,j remain.
Both charts also satisfy the original whole-corner estimate

    0<p<367/600.                                       (7)

In the cited proof this uses only B's actual equation and its corner,
not the final petal-routing section. In H coordinates write

    z_B=Z*m-W*k,
    Z=L*X-K*Y, W=K*X+L*Y>0.

That proof gives |Z|<1 and hence (7), with all side means retained.

## 2. The genuine H leaf has only one possible radial support

O in int H prevents H's radial S-leaf support from being an H-owned
side. Such an aligned radial support would put H's opposite face at
distance D-1=epsilon>0 on the same side of O. Thus the true leaf
application is an actual H vertex of norm D.

The two vertices on the minimum-m side have squared norm less than
1+epsilon^2<D^2: |q_m|<epsilon, 0<p<1 and 0<1-p<1. The far-m/
minimum-k vertex has squared norm greater than

    (59/60)^2+(233/600)^2>(61/60)^2>D^2,

where the strict reserve in the first comparison is 30289/360000.
Consequently H's physical S support must be

    F=(1+q_m)m+p*k,
    D^2=(1+q_m)^2+p^2.

Since 1+q_m>1-epsilon,

    0<p^2<4*epsilon<1/15,
    0<p<4/15.                                         (8)

This uses only H's physical leaf classification; none of H's other
forces is removed or identified with that leaf.

## 3. The H-owned transverse normal g=k is impossible

Here B's actual force equation gives F_B.m=mu*L>0. Thus Z>0.
The actual q_B has m coordinate equal to T.m=q_m+j, and (5) gives

    (q_B).m=(B0/Y)Z, 0<B0/Y<1.

The original corner identity also gives

    Z=(q_B).m+L-K.

Therefore L>K. Equations (5)--(6) now give A_B<V, hence X>Y.
The exact H transverse coordinate in this owner chart is

    p=1+K+L-W.                                        (9)

Put S=K+L<=sqrt(2). The opposite order of X,Y and K,L gives

    W=K*X+L*Y < S*(X+Y)/2 <= S*R/sqrt(2).

Since R>sqrt(2), equation (9) yields

    p>1+S*(1-R/sqrt(2))
       >=1+sqrt(2)-R>3/10.

The last coarse comparison uses sqrt(2)>7/5 and R<21/10. This
contradicts (8). This is a whole-frame rearrangement inequality,
not a restricted angular sample.

## 4. The B-owned transverse normal g=v: two exact scalar reductions

This owner is in fact impossible already under O in int H; H's
physical S leaf is not needed in Sections 4--6.

Put S0=sqrt(h^2*b^2+w^2*a^2). The exact A equations in (1) give

    K=a*b/S0, c=w*a/S0, d=h*b/S0,
    L=(h-a^2)/S0>0.

In particular q_m<0 is exactly

    w^2*a<epsilon*h*b.                                (10)

The actual t>=0 in (6) gives V<=c/K=w/b. Since
Y=1+B0-V, we have

    Y>=1+B0-w/b.                                      (11)

### 4.1. The actual upper A height exceeds 3/4

Suppose h<=3/4. Equation (10) and w=1-h give

    a/b<epsilon*h/(1-h)^2<=12*epsilon.

For fixed h,epsilon the expression
(h+epsilon)a+(h-epsilon)b increases with a/b throughout
0<=a/b<=12epsilon<1/5: its derivative has numerator
(h+epsilon)-(a/b)(h-epsilon)>0. Also h>16/25>epsilon.
Using h<=3/4 and V>0 therefore gives

    R^2=X^2+Y^2<X^2+(1+B0)^2
       <=41/16+epsilon^2
           +2*(3/4+8epsilon+12epsilon^2)
                       /sqrt(1+144epsilon^2).          (12)

This last upper bound is strictly less than the actual
R^2=17/4+4epsilon+epsilon^2. Indeed, squaring the positive
comparison reduces it to

    (27/32+2epsilon)^2*(1+144epsilon^2)
       -(3/4+8epsilon+12epsilon^2)^2
      =153/1024-(69/8)epsilon+(1569/64)epsilon^2
           +294epsilon^3+432epsilon^4>0.

Its constant and linear terms already have lower bound
153/1024-(69/8)/60=29/5120>0. This contradicts (12). Hence

    h>3/4.                                            (13)

### 4.2. The actual B-normal component satisfies a<1/2

Suppose a>=1/2. Equation (10) gives w^2/(1-w)<b/(60a).
The increasing function w^2/(1-w) gives these full interval bounds:

| Actual a interval | Uniform upper bound w_* for w |
| --- | --- |
| [1/2,3/5] | 4/25 |
| [3/5,4/5] | 7/50 |
| [4/5,12/13] | 11/100 |
| [12/13,19/20] | 2/25 |

For the first row use b/a<=sqrt(3)<7/4; for the other rows use
respectively b/a<=4/3, 3/4 and 5/12. At the displayed w_* values,
the exact reserves over 7/240, 1/45, 1/80 and 1/144 are respectively

    11/8400, 11/19350, 39/35600, 1/82800.

For fixed a and b=sqrt(1-a^2), define

    Phi(w,e)
       =[1+(1-w)a-e*b]^2
          +[1+(1-w)b+e*a-w/b]^2-[(2+e)^2+1/4].        (14)

All displayed square brackets are positive on these enlarged domains:
b>3/10, w<=4/25 and e<=1/60 suffice. The derivative with respect
to w is strictly negative. The derivative with respect to e is

    2*(a-b-a*w/b-2)<0.

Consequently Phi(w,epsilon)>Phi(w_*,1/60). As a function of a,
with each row's w_* fixed, the latter is strictly concave. To see
this, its nonconstant terms after expansion are

    2(h_*+e)a+2(h_*-e)b-2w_*/b
            -2e*w_* a/b+w_*^2/b^2,
    h_*=1-w_*, e=1/60.

Its second derivative is

    -2(h_*-e)/b^3
      -2w_*(1+2a^2)/b^5-6e*w_*a/b^5
      +2w_*^2*(1+3a^2)/b^6 <0.                        (15)

The final positive term is smaller in magnitude than the second
negative term because b>3w_*/2 and
(1+3a^2)/(1+2a^2)<3/2. Thus each entire interval is bounded
below by the smaller of its two endpoint values.

Here are exact positive lower bounds for those two endpoint values:

| w_* | Lower endpoint reserve | Upper endpoint reserve |
| --- | --- | --- |
| 4/25 | 201529/5760000 | 761/7500 |
| 7/50 | 31271/120000 | 4013/22500 |
| 11/100 | 2477/5625 | 76946/609375 |
| 2/25 | 1042031/2437500 | 72934633/324000000 |

At the first irrational endpoint use 6/7<b<7/8; its two
positive brackets are bounded below by 3373/2400 and 37/24.
At the last irrational endpoint use 3/10<b<1/3; its positive
brackets are bounded below by 2102/1125 and 6151/6000.
These intervals follow by squaring, and every other endpoint is
an exact rational Pythagorean pair. The table is simply the two
endpoint evaluations of the continuous concavity estimate (15).

Thus Phi(w,epsilon)>0 throughout a>=1/2. But (11), with its
positive right side in this domain, gives

    R^2=X^2+Y^2>=X^2+(1+B0-w/b)^2>R^2,

a contradiction. Therefore

    0<a<1/2.                                          (16)

## 5. The geometric advance is below 1/6

Since V>0 and K,L>0, (6), (10), (13) and (16) give

    0<=t<c/L=w*a/(h-a^2),
    t^2<epsilon*h*b*a/(h-a^2)^2
       <(1/120)*h/(h-1/4)^2<1/40<1/36.

The function h/(h-1/4)^2 decreases for h>1/4 and equals three
at h=3/4. Consequently

    t<1/6.                                            (17)

## 6. The true circle-ray advance is greater than 1/6

Write p0=p_n. Then -1/60<p0<h/2<1/2 and B0>0. Equation (5)
gives A_B>1/6 exactly when

    (1+p0)B0>(p0+1/6)Y.

Both sides are positive. Since B0^2=h^2+epsilon^2-p0^2 and
Y^2=R^2-(1+p0)^2, its squared form is

    (1+p0)^2*(h^2+epsilon^2+p0/3+1/36)
         >R^2*(p0+1/6)^2.                             (18)

For -1/60<=p0<=3/8, the left side minus the right side is
bounded below by

    g_1(p0)=(1+p0)^2*(9/16+p0/3+1/36)
                 -(1105/256)*(p0+1/6)^2.

This cubic is strictly concave: its second derivative is
-7049/1152+2p0<0. Its two endpoint values are

    g_1(-1/60)=19420291/41472000>0,
    g_1(3/8)=1407/16384>0.

For 3/8<=p0<=1/2, use h^2>4p0^2 instead. The corresponding
lower bound is

    g_2(p0)=(1+p0)^2*(4p0^2+p0/3+1/36)
                 -(1105/256)*(p0+1/6)^2.

Its derivative is

    16p0^3+25p0^2
       +2*(169/36-1105/256)*p0
       +(7/18-(1105/256)/3)>0.

Indeed the third coefficient is positive, the last term is greater
than -2, and the first two terms are at least 27/32 and 225/64.
Their resulting lower bound is 151/64>0. Therefore g_2 is
increasing and g_2(3/8)=g_1(3/8)>0. This proves (18) on the
whole actual domain, hence

    A_B>1/6.                                          (19)

The genuine perpendicular B contact equation in (6) says A_B=t.
Equations (17)--(19) contradict it. The complete g=v case is
therefore excluded, with all original means and force endpoints.

## 7. Whole local conclusion and limitations

The inherited finite actual-feature cover leaves exactly g=v and
g=k. Sections 3 and 4--6 exclude them respectively, proving the
entire stated aligned-A/nonparallel-cycle interface. H's full
external force is arbitrary throughout. Only its actual physical
S leaf was used in Section 2, and only B and A used their original
degree-two and degree-three equations.

All old preliminary estimates were used at their genuine equation
scope before the old final single-petal routing. In particular no
identity F_C+F_E=M_total at H was inherited after adding H's leaf.
The original compatible physical normal preselection, all extra
units, every physical B mask and circle-weight endpoint, and all
actual side means remain unchanged.

This is a complete local interface exclusion, not a whole bowtie
or coarse-cell assembly by itself. The parallel-A and tilted-A
interfaces require their separate whole joins. No pose sampling,
numerical feasibility claim, Lean compilation, CI, remote write or
shared-ledger mutation is part of the proof.
