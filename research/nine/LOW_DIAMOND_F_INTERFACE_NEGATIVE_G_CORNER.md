# The negative-g far corner is strictly interior when cn is nonpositive

**Status: complete hand scalar implication; author, root and separate independent
review passed. See REVIEW_LOW_F_INTERFACE_2026_10_25.md. No full diamond parent
is closed by this source alone.**

This is the negative-g half of the pending center-projection proof for the
f-owned/shared HK row. It retains the original square, its original offset
and all force means. Enlarging r to one below is solely a scalar upper
bound on a corner norm, never a replacement of the actual packing.

## 1. Precise enlarged scalar statement

Use the original ordered negative-endpoint coordinates

    a>b>3/5, a^2+b^2=q>=q0=6241/1600,
    u^2+v^2=1, 0<u<=v, u/v>=8/15,
    0<=p<=u, E=sqrt(1-p^2),
    s=Eu-pv, c=Ev+pu, 0<=r<=1,
    L=(a-1)s+bc, h=-(a-1)c+bs.

Thus s>=0, c>0 and c^2+s^2=1. Define

    N=au+bv, D=av-bu, S=u+v,
    cn=N-S-1/2,
    F(r)=L+1-c+rp.

**Lemma.** If cn<=0, then

    F(r)^2+h^2<q.                                      (1)

The left side is the squared norm of the actual far-f/lower-g K corner
in the original f-interface chart. Its being
the physical far g corner is not assumed. In particular, (1) remains
available when h<-1/2, which is precisely the alternative not addressed
by a comparison of (F,h+1).

The original branch's independently established restriction u/v>5/9 is
stronger than the displayed 8/15. No A2 or K3 equation is added to this
scalar lemma. In the intended use, those true equations and every other
physical square remain unchanged.

## 2. Two uniform endpoint-coordinate bounds

First

    N>S.                                               (2)

To prove this, suppose N<=S. Since a>b and q>=q0>2, one has a>1.
Therefore b<1 and

    a<=1+(v/u)(1-b)<=23/8-15b/8.

The function (23/8-15b/8)^2+b^2 is convex on [3/5,1], so its maximum
occurs at an endpoint. The two endpoint values are 1369/400 and 2.
Consequently q<=1369/400<q0, a contradiction; the exact gap is 153/320.

Second, cn<=0 implies

    D>17/35.                                           (3)

Indeed D>0 follows from a>b and v>=u. As N<=S+1/2 and S<=sqrt(2),

    D^2=q-N^2>=q0-9/4-sqrt(2)>(17/35)^2.

The last strict comparison is exact:

    q0-9/4-289/1225=110913/78400>sqrt(2),
    (110913/78400)^2-2=8573569/6146560000>0.

Both numbers being squared are positive.

## 3. Express the enlarged original corner in the (n,j) frame

Since a>1, b>3/5 and c>0, L>(3/5)c. Hence

    F(r)>1-(2/5)c>0.

The squared norm F(r)^2+h^2 increases with r in [0,1], weakly when p=0.
It therefore suffices to prove (1) with r=1.

In the unchanged positively oriented (n,j) frame, put

    C0=E(1+p)-ps,
    Z0=p(1+p-c),
    A=S-C0, B=v+Z0.

The K corner (F(1),h) has exactly the coordinates

    (N-A,B-D).                                         (4)

For example, the actual endpoint P=(a-1,b-1) has n and j coordinates
(N-S,v-u-D). At comparison r=1 its front/top vertex has coordinates
(N-S,1+v-u-D). The corner (F(1),h) adds f-(E-s)g to that vertex.
Using f=(E,p), g=(-p,E) and Es-u=-pc gives (4).

We will need A>0 and B>0. The latter follows from c<=1, since
Z0=p(1+p-c)>=0. For the former, the exact norm identity is

    C0^2+Z0^2=1+2p(1+p)(1-u)
       <=1+2u(1+u)(1-u)
        =1+2uv^2<1+2uv=S^2.                            (5)

Here p<=u, 0<u<1 and 0<v<1. Thus C0<S and A>0.

Using (2)--(4), the corner's deficit below q satisfies

    q-|corner|^2
       =2NA+2DB-A^2-B^2
       >2SA+(34/35)B-A^2-B^2=:T.                       (6)

No sign-uncertain term is discarded in this comparison.

## 4. Monotonicity in the entire p interval

Write k=34/35. Expanding T with (5) gives the exact expression

    T=-v^2+2uv+kv
         -2p(1+p)(1-u)-(2v-k)Z0.                       (7)

Both subtracted terms increase with p on [0,u], with u,v fixed.
Indeed 1-u>0, while v>=1/sqrt(2)>17/35 makes 2v-k>0. Moreover

    c=Ev+pu<=1,
    c'=u-pv/E<=u<1,
    Z0'=1-c+p(2-c')>=0.                                (8)

The denominators in (8) are positive because E>=v>0. Thus T is bounded
below by its value at p=u. At that endpoint E=v, s=0, c=1 and Z0=u^2.
Equation (7) therefore gives

    T>=Tend:=-v^2+2uv(1-u-v)+(34/35)(v+u^2).            (9)

The endpoint is part of an enlarged scalar domain. The actual AK contact
is never reset to the limiting orientation s=0.

## 5. One monotone polynomial proves the remaining sign

Put w=u/(1+v), so

    u=2w/(1+w^2), v=(1-w^2)/(1+w^2),
    1/4<=w<=sqrt(2)-1<5/12.

Direct expansion of (9) yields

    35(1+w^2)^3 Tend=P(w),
    P(w)=-1-75w^2+280w^3+417w^4-280w^5-69w^6.          (10)

This one polynomial is strictly increasing throughout [1/4,5/12]:

    P'(w)=w[-150+840w+w^2(1668-1400w-414w^2)]>0.        (11)

The first bracket term -150+840w is at least 60. The other bracket
is decreasing there, and its lower endpoint bound at 5/12 is

    1668-1400(5/12)-414(5/12)^2=24307/24>0.

Finally

    P(w)>=P(1/4)=107/4096>0.                            (12)

Equations (6), (9)--(12) give q-|corner|^2>0 at r=1, and the original
r comparison proves (1) throughout the displayed domain. This includes
p=0 and every actual shared-HK mean, which never enters the scalar proof.

## 6. Retained scope

This result supplies the full negative-g corner alternative under cn<=0.
Together with a separately proved positive-g comparison it can exclude
all physical circle corners of K and establish cn>0. That assembly must
still verify the original lower angle bound u/v>5/9 and every premise of
the positive-g comparison. This manuscript does not assign a far circle
corner by a force sign or claim a completed diamond block exclusion.

No force, original mean, completion square or petal is removed. No
numerical optimization, pose sample, coefficient table, Lean compilation
or CI is a proof premise, and no roadmap checkbox changes here.
