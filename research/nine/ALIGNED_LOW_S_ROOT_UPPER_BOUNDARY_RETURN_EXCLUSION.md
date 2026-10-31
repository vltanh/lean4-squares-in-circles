# An aligned low-radius S root forces its upper neighbor's return to be clear

Date: October 27, 2026.

**Status: complete hand theorem, submitted for full root and separate
independent review.** All original means, proper-distance endpoints,
circle masks, and the true root and upper-neighbor equations are retained.

## 1. Original scope and the actual upper boundary frame

Keep the original nine physical units and the compatible selected
certificate. Let H be a genuine S-leaf root of true degree three,
with both other neighbors physically boundary. Assume

    2<R<sqrt(17)/2,
    d=sqrt(R^2-1/4)-1,       a=1-d,
    H=[-a,d] times [h-1,h],
    L=[d,d+1] times [-1/2,1/2].                       (1)

After reflection, the complete local theorem in Sections 1--6 of
S_LEAF_C5_ALIGNED_LOW_RADIUS_EXCLUSION.md gives

    0<a<1/15,       29/50<h<2/3,
    P_B=(-a,h),     n=(-c,s),     c,s>0,
    P_D=(x,h-1),    n_D=-e_y,     3/10<x<=d,
    c/s=(x+a)/h,    c^2+s^2=1.                       (2)

That theorem first proves D is genuinely tilted, and then applies
the original finite singleton selection to make n an actual B side
axis. This scope is independent of B's or D's other neighbors and
does not require the four-boundary C5 path used only in its final
section. In the present theorem B additionally has true degree two
and a positive circle load. Its other actual neighbor is denoted E.

Put j=(-s,-c), and retain B's entire actual side mean:

    B=P_B+[0,1]n+[-rho,1-rho]j,       0<=rho<=1,
    N=P_B dot n=a c+h s>0,
    K=-P_B dot j=h c-a s=x s>0.                       (3)

Use (n,j) coordinates, without moving the original origin. The same
physical local theorem proves B has exactly one physical circle
corner, namely

    Z_B=(N+1,-W),       W=K+rho,
    R^2=(N+1)^2+W^2,
    B=[N,N+1] times [-W,1-W].                         (4)

In particular this is a physical unique-corner conclusion, not an
assumption about which individual circle weights are positive.

We prove that E cannot be physically boundary. The far return feature
will in fact be impossible for any contained E.

## 2. Uniform bounds on the unchanged frame and proper concurrence

Equations (2)--(3) give

    N^2+K^2=a^2+h^2<101/225,
    N<7/10,
    W^2>4-(17/10)^2>1.                               (5)

For fixed a,h, the function

    K=x h/sqrt(h^2+(x+a)^2)

is increasing in x. Since x<=d and d+a=1,

    K<=d h/sqrt(1+h^2)<2d/sqrt(13)<5/9.               (6)

The last comparison uses 324<325. Also

    N>=h^2/sqrt(h^2+(x+a)^2)
       > (4/5)(29/50)^2=841/3125>1/4,               (7)

because sqrt(h^2+(x+a)^2)<sqrt(13)/3<5/4. The final
rational reserve in (7) is 239/12500.

We next show

    rho>7/8.                                         (8)

If rho<=7/8, the triangle inequality applied to (N,K)+(1,rho)
would give

    R<sqrt(101)/15+sqrt(113)/8<2.

For the last exact comparison, after squaring once it suffices that
sqrt(11413)<25711/240; its squared reserve is

    25711^2-11413*240^2=3666721>0.

This contradicts R>2. Thus delta:=1-rho satisfies 0<=delta<1/8.

Let g be the actual unit normal from B to E. In the full B2 force
equation, the H force is along -n, and the positive circle resultant
is along Z_B. Its j component is strictly negative. Hence

    g_j>0.                                            (9)

The two actual B pair normals are therefore nonparallel. The original
proper-concurrence theorem for a physically unique loaded degree-two
unit applies, with both original forces and their original means.
The concurrence is on the inward ray from P_B along n and the positive
radial line through Z_B. Its actual coordinates are consequently

    q_B=(q_n,-K),
    q_n=K(N+1)/W=N+lambda,
    lambda=(K-N rho)/(K+rho)>=0.                      (10)

No point or normal is reselected. In particular lambda=0 is retained.
Equations (6), (8) imply

    0<=lambda<K/(K+rho)<40/103<2/5.                  (11)

## 3. The complete return feature cover

By (9), there are exactly three actual supporting features for E:

* if g_n<0, the near upper corner Q=(N,1-W);
* if g_n=0, an actual mean Q=(q_n,1-W) on the owned j side;
* if g_n>0, the far upper corner Q=(N+1,1-W).

In the middle case, (10) forces its n coordinate to be q_n even when
the proper return distance is zero. This retains every original side
mean and both endpoints. In the corner cases the original mean is
the actual singleton corner.

The near corner already has

    |Q|^2=N^2+(W-1)^2<=N^2+K^2<101/225<(7/10)^2,    (12)

because 1<W=K+rho<=K+1.

At the far corner, properness and (10) give an actual return direction
proportional to (1-lambda,delta). Since g_j>0, this feature has delta>0;
otherwise its proper distance would be zero and lambda would equal
one, contradicting (11). Put t=delta/(1-lambda). Then

    0<t<5/24,
    Q dot g=[N+1+t(delta-K)]/sqrt(1+t^2)
        >[5/4-(3/5)(5/24)]/(25/24)
         =27/25>1>d.                                 (13)

The accepted sharp minimum-support bound for a contained unit says
that its actual minimum supporting value in any direction is at most
d. The actual E would lie beyond the support in (13), so this entire
far-corner feature is impossible. This argument does not require E
to be boundary or to satisfy any force equation.

It remains to bound the genuine owned-j mean.

## 4. A short bound for every actual owned-j return mean

At this mean, (10) gives exactly

    |Q|^2=F(N,K,rho),
    F(N,K,rho)=K^2(N+1)^2/(K+rho)^2+(K+rho-1)^2.       (14)

First, on the entire present domain,

    |Q|<3/4.                                         (15)

Here is a complete scalar comparison retaining the original mean.
For fixed K,rho, F increases with N. Enlarge N to

    N_*(K)=sqrt(101/225-K^2).

For 0<K<=5/9, we have N_*>37/100. The first positive coordinate
K(N_*+1)/(K+rho) has derivative with the sign of

    rho[N_*+101/225-2K^2]-K^3.

Throughout rho>=7/8 this is bounded below by

    (7/8)[37/100+101/225-50/81]-125/729
       =2879/583200>0.                               (16)

The second nonnegative coordinate K+rho-1 also increases with K.
It starts positive at the actual K by (5), so increasing K to 5/9
increases the whole comparison (14). At that upper endpoint,
N_*<3/8, since 18176<18225. Increase N_* further to 3/8.

For fixed N,K, F is convex as a function of rho:

    partial_rho^2 F=6K^2(N+1)^2/(K+rho)^4+2>0.

It therefore suffices to check rho=7/8 and rho=1 at the enlarged
N=3/8,K=5/9. The two exact upper bounds are

    (55/103)^2+(31/72)^2<9/16,
    (55/112)^2+(5/9)^2<9/16.                         (17)

Their reserves are 5058995/54997056 and 12911/1016064. This proves
(15). The scalar enlargements in this paragraph are inequalities
only; they do not change a physical square, application, or force.

For the lower subrange R^2<=65/16, there is the stronger bound

    |Q|<8/11.                                        (18)

Indeed

    d<=sqrt(61)/4-1<23/24,
    K<23/(12sqrt(13))<8/15.                          (19)

The radical comparisons use 2196<2209 and the squared reserve
96^2*13-345^2=783. Repeat the same increasing-K argument up to 8/15.
Now N_*>2/5 throughout that interval, and its derivative numerator
is bounded below by

    (7/8)[2/5+101/225-128/225]-512/3375
       =2519/27000>0.

At K=8/15, N_*=sqrt(37)/15<5/12. The two convex rho endpoints
are therefore bounded by

    (272/507)^2+(49/120)^2<64/121,
    (34/69)^2+(8/15)^2<64/121.                       (20)

The exact reserves are 3700944919/49764686400 and
24124/14402025. This proves (18) at the entire weak lower-radius
endpoint as well.

## 5. The return cannot meet another physical boundary unit

The force-free theorem BOUNDARY_PAIR_CONTACT_SHARP_INNER_RADIUS.md
says that any actual common point of two physical boundary units
must satisfy

    |Q|>=sqrt(R^2-1)-1.                               (21)

It applies to every actual side mean because that mean remains a
point of both physical units. It does not require either individual
circle weight to be positive.

The near corner (12) violates (21), since
sqrt(R^2-1)-1>sqrt(3)-1>8/11>7/10. For the middle feature:

* if R^2>=65/16, (21) requires |Q|>=3/4, contrary to (15);
* if R^2<=65/16, (18) gives |Q|<8/11<sqrt(3)-1, again contrary
  to (21).

The comparison 8/11<sqrt(3)-1 is the exact inequality 361<363.
The far feature was already excluded for every contained unit by
(13). This proves the full theorem: **E cannot be physically boundary.**

## 6. Exact S124 consequence and retained remainder

In the original C5 load family

    0--1--2--3--4--0,       0--L,
    loads on 1,2,4,

the upper neighbor B from (2) is one of the two physically boundary
neighbors of 0. It is a true loaded degree-two body, so the theorem
applies literally. Its other original neighbor must be the actual
unloaded body 3. In particular the actual cycle order, after naming
the remaining two loaded units C,D, is forced to be

    H--B--X--C--D--H,       H--L,

where X is the original unloaded transmitter and D is the lower
neighbor in (2). This is a conclusion about the original graph and
actual bodies; no force is deleted and no channel is substituted
for a physical contact. The real X remains present with its actual
width, original two-force equation and original applications.

This source excludes the whole opposite placement and provides the
exhaustive return features for the remaining placement. It does not
yet exclude the displayed B--X--C--D route, and therefore makes no
whole S124 claim by itself. All three arbitrary completion units
remain, through the unchanged same-nine radius reduction and any
subsequent completion argument.

No Lean compilation, CI, numerical pose, altered mean, remote edit,
or shared-metadata edit is a premise of this proof.
