# Independent review of the radial-C S123 root half-plane reduction

Date: October 27, 2026.
Reviewer: triangle_bridges, independently of author rooted_blocks.

**Decision: ACCEPTED in full.** No mathematical correction is requested.
The source excludes the complete actual n_x>=0 channel domain after
its stated physical radial-C and direct-root reductions. Its two
remaining tilted direct features and the aligned high root are
correctly left open. Root review and integration remain separate.

Reviewed source:

    S_LEAF_C5_THREE_LOAD_RADIAL_ROOT_HALFPLANES.md
    SHA256 b64691f7a1a8339e0dea16c44ca1842d08726210f0134d2862d8c282151d0bab

I read the complete source, the full far-support/path theorem,
the complete radial-side physical theorem and its original caller,
and the exact domain/mask/mean scopes of the separately reviewed
tilted-channel and unique-C sources. I independently re-derived all
new support identities, root-force signs, inequalities, the original
side-mean bounds and both final scalar systems.

## 1. All direct domains are used at their actual original scope

The graph remains A--B--M--C--U--A plus A--L, with A3, true loaded
B2,M2,C2 and true unloaded side-normal U2. All nine units remain.
The unique-C physical mask has been wholly excluded separately;
it is not obtained by deleting a zero individual radial weight.
The surviving C is the actual full radial rectangle in the original
n,f frame, with its original two circle weights retained.

The inherited complete tilted-channel source gives x>0,t>=0,
x^2+t^2=1, positive q_A=(q,0), k=d-q>=0, and the actual root
ports. Its complete unique-C exclusion and the radial-side theorem
then remove precisely the u<0 direct feature. Their separate full
independent reviews are

    REVIEW_S123_FAR_SUPPORT_AND_TILTED_CHANNEL_HEXAGON_2026_10_27.md
    f0a4fee0e2b8265579af3dfcf19d88c4c95893f6484274d43c80fcc0abdeac7a;

    REVIEW_S123_UNIQUE_FAR_ENDPOINT_HEXAGON_2026_10_27.md
    dffd2c4daa4c015047436b8e67564b473a8e4569aebf1b38acf9fb8680832142;

    REVIEW_RADIAL_SIDE_BOUNDARY_HALFPLANE_HEXAGON_2026_10_27.md
    bee384ea3ba2d3147efeb801b9e12faa6c842da00686c2824ffca7aafbbf45df.

The new proof retains both u=0 with its full original side mean,
and u>0 at the true opposite root vertex. It never treats the
loaded B--M--C path as an unloaded channel.

## 2. Both original direct-force signs follow from the full root

For u>0, the original positive proper root direction gives
u/v=(1-ka)/(1-kb). Both numerator and denominator have their
correct signs; a>b and k>=0 give u<=v. For u=0 this inequality
holds directly with v>0, and its actual mean remains Z=ka.
Thus m_x=-au-bv<0 and m_y=-bu+av>=(a-b)v>0 in both whole
features. Also n_y=-bx-at<0 because b,x>0.
No equation at B,M,C is specialized to obtain these signs.

## 3. Every n_x>=0 channel is covered, including its axis endpoint

If n_x>=0 then t>0, since t=0 would give n=f1 with negative
world x component. Thus the actual channel port is the fixed
original vertex p0+f1. Its support is exactly

    epsilon=(1-da)x+dbt=x+d n_x.

It follows that0<x<=epsilon<1/60 and
0<=n_x<epsilon/d<1/61. The last bound uses the actual
relation d=1+epsilon and monotonicity of epsilon/(1+epsilon).
Its tangent angle from South is below1/sqrt(3720)<1/60,
so it meets the stated1/59 endpoint theorem premise.

The same full support equation gives dbt<=epsilon(1+x).
Dividing by d>1 and t=sqrt(1-x^2) gives
b<epsilon*sqrt((1+x)/(1-x))<1/59. The exact endpoint
comparison is61*59=3599<3600. This retains n_x=0 and
x=epsilon; no strict inequality is taken at an unproved endpoint.

## 4. Both actual B-port alternatives satisfy the full path theorem

For u>0 the actual port is p0+f1+f2. Since1-a<=b,
its first coordinate satisfies-b<P_x<=epsilon<1/30.

For u=0 the original mean is Z=ka. The genuine channel line gives
k=t/(bx+at). Because a<=1,

    k>=1/(1+bx/t)>=1-bx/t.

Hence q=d-k<=epsilon+bx/t. From the same full support bound,

    bx/t<=epsilon*x(1+x)/(d t^2)
          <=epsilon*x/(1-x),

so q<=epsilon/(1-x)<1/59. The actual mean has
P_x=d-a^2k-b=q+k b^2-b. The original inequalities k<=d,
a<1 and kb<db<1 give-b<P_x<q. In particular the full
side interval satisfies|P_x|<1/30 without changing Z.

In both cases P_y=a-bZ with0<=Z<=1. Using a>=1-b^2
and b<1/59 gives29/30<a-b<=P_y<=a<1.
The exact reserve is1681/104430. All required inequalities
are thus uniform over both original owner/mean alternatives.

The actual C has minimum n support d>1>59/60. Its n direction
is within1/59 of South, opposite the positive B-port height.
The real B--M--C boundary path therefore meets every hypothesis
of Section3 of FAR_SUPPORT_THREE_BOUNDARY_PATH_EXCLUSION.md.
That complete theorem uses the actual middle unit M and its two
physical contacts; it does not require M to be unloaded or
replace the path by a contact. Its strict endpoint-angle
contradiction excludes this entire n_x>=0 domain.

## 5. The final strict and side-mean identities are literal

For t>0, the actual port p_AU=p0+f1 has n projection epsilon
and f projection -T. Direct projection gives

    (1-da)x+dbt=epsilon,
    (1-da)t-dbx=-T.

Inverting this orthonormal pair gives exactly

    db=xT+epsilon*t,
    da=1-epsilon*x+tT.

Squaring and adding, and using d=1+epsilon, gives
T^2+2tT=2epsilon(1+x). The original root concurrence
k=t/(bx+at), with dbx+dat=T+t, gives
q=dT/(T+t). Thus every displayed formula in the strict
row follows from the actual original point and full root data.

For t=0 the original x=1. The support condition instead gives
da=1-epsilon, and the radius identity gives db=2sqrt(epsilon).
The original entire side mean is p0+f1+Yf2, with0<=Y<db.
Consequently T=db-Y and q=d-Y/b=dT/(db). The strict-port
quadratic is not silently imposed when Y>0. This separate
weak-axis row is necessary and is correctly retained.

The strict conclusion n_x<0 implies x>epsilon from the support
identity when t>0; when t=0 it follows from x=1. Together with
Section2, the final normal signs and0<=u<=v are valid over the
whole surviving original tilted radial-C domain.

## 6. Exact accepted scope

This theorem removes a complete actual channel half-plane. The
direct A-owned f2 side and the opposite A vertex remain as two
explicit original obligations; the high aligned root is separate.
No original fine or coarse family is prematurely counted closed.

Every original radial circle corner, individual zero weight,
true degree, positive force, actual mean, unloaded body and
completion unit is retained. No numerical pose, reselection,
shared metadata edit, remote mutation, compilation or CI is
used or inferred by this review.

