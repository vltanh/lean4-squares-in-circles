# Both cycle forces at a tilted S-leaf C5 root point strictly away from the leaf

Date: October 26, 2026.

**Status: complete hand structural consequence, accepted after independent
full-source review in REVIEW_S_C5_TILTED_AND_RADIAL_POCKET_ROOT_2026_10_26.md,
including its accepted tilted far-endpoint prerequisite.**
No original completion gate is closed by this source.

Keep exactly the original component A--B--V--C--U--A with a
genuine S leaf L at A, block loads B,C, all original positive
forces, actual normals, means, physical circle weights and three
extra units. Use the entire tilted-root chart and conclusions of
S_LEAF_C5_TILTED_FAR_ENDPOINT_RADIAL.md.

In particular

\[
 \begin{gathered}
 0<\delta=d-1<1/60,\qquad
 A=(d,0)+[0,1]f_1+[0,1]f_2,\\
 f_1=(-a,-b),\quad f_2=(-b,a),\quad
 a^2+b^2=1,\quad a>59/61,\quad 0<b<16/61,\\
 n=x f_1-t f_2,\quad x>0,\quad t\ge0,\quad x^2+t^2=1,\\
 p_{AU}=(d,0)+f_1+Yf_2,\qquad
 Y=0\ (t>0),\quad 0\le Y<db\ (t=0),\\
 m=u f_1+v f_2,\qquad v>0,\qquad
 p_{AB}=(d,0)+Zf_1+f_2,\quad 0\le Z\le1.
 \end{gathered}
\tag{1}
\]

The actual root concurrence is q_A=(q,0), q>0. If k=d-q,
its own coordinates are (ka,kb), with k>=0. Both loaded
endpoint pairs are nonparallel and proper, and the three
directed loaded turns lie in (0,pi) and sum to 2pi. C is
the physical radial unit

\[
 C=[d,d+1]n+[-1/2,1/2]f,\qquad f=t f_1+x f_2,
\]
\[
 p_{CU}=dn-Tf,\qquad 0<T<13/50,\qquad h_A(n)=\delta.
\tag{2}
\]

The unchanged V reserve is one. The complete radial side-channel
support cover and the negative common moment give

\[
 \begin{gathered}
 p_{CV}=dn+f/2,\qquad
 g=-\alpha n+\beta f,\qquad
 \alpha,\beta>0,\quad \alpha^2+\beta^2=1,\\
                         p_{BV}=p_{CV}+g.
 \end{gathered}
\tag{3}
\]

Here g points from C through V to B. The sign in (3) is fixed
by the actual common moment, as in Sections 4 and 7 of the
prerequisite; no reflected endpoint or new mean is chosen.

**Theorem.** The complete tilted family satisfies

\[
              0\le u\le v,\qquad
              m\cdot e_x<0,\quad m\cdot e_y>0,\qquad
              n\cdot e_x<0,\quad n\cdot e_y<0.
\tag{4}
\]

Thus both actual root cycle forces point strictly into the
half-plane away from the genuine leaf. The u=0 original
side-axis mean remains included.

## 1. The entire negative-u direct-contact domain is impossible

Suppose u<0. Since v>0, the actual A application is P_2:

\[
 p_{AB}=(d,0)+f_2=(d-b,a).
\tag{5}
\]

Its squared norm and its projection on the original normal are

\[
 |p_{AB}|^2=d^2+1-2db>d^2+1/4,\qquad
 p_{AB}\cdot m=-da\,u+(1-db)v>0.
\tag{6}
\]

Indeed db<(61/60)(16/61)=4/15<3/8.

B cannot be physically radial. Its inner face and inner
vertices have norm at most sqrt(d^2+1/4), contrary to (6).
Its outer circle vertices are unshareable. If the actual
application were in an outer or tangential face, the original
minimum-m supporting value of B would be -(d+1) or -1/2,
respectively, contrary to the positive projection in (6).
These are all remaining radial support features; no physical
corner weight is used in this cover. Thus B is unique.

Its ports are distinct: |p_AB|>sqrt(d^2+1/4)>R-sqrt(2)
excludes the unique opposite radial-D coincident vertex, and
coincident side-interior ports would be parallel. The complete
local unique-corner calculation from Section 4 of
D_LEAF_C5_TWO_SEPARATED_LOADS_EXCLUSION.md applies. In
particular

\[
     \theta_B>\pi/2\quad\Longrightarrow\quad
                         |p_{BV}-p_{BA}|\le1.
\tag{7}
\]

The root turn is acute:

    (-m) dot n = (-u)x+vt >0.

Since theta_C<pi and the three turns sum to 2pi, theta_B>pi/2.
On the other hand the original root ports give

    (p_AB-p_AU) dot n = -x-t.

For t>0 this follows from Y=0; for t=0 the mean Y drops out
of the projection. Using h_A(n)=delta and (3),

\[
 (p_{BV}-p_{BA})\cdot n
    =(d-\alpha)-(\delta-x-t)
    =1-\alpha+x+t>1.
\tag{8}
\]

Here alpha<1 and x+t>=1. Equation (8) contradicts (7).
Therefore u>=0 throughout the original tilted family.

If u>0, the actual root application is P_12. Properness at
that root port gives

    u/v=(1-ka)/(1-kb)<=1,

because k>=0 and a>=b. The denominator is positive by the
root direct proper-length argument in the prerequisite.
For u=0, of course u<=v as well. Hence 0<=u<=v.
The actual global components now give

\[
 m\cdot e_x=-au-bv<0,\qquad
 m\cdot e_y=-bu+av\ge(a-b)v>0.
\tag{9}
\]

No actual normal has been replaced to obtain these signs.

## 2. A channel pointing toward the leaf would have an impossibly long B chord

The negative vertical component of n is already exact:

    n dot e_y=-bx-at<0.

Suppose n dot e_x>=0. Then bt>=ax. Necessarily t>0,
so p_AU=P_1 and its unchanged support equation is

\[
                 \delta=(1-da)x+dbt.
\tag{10}
\]

The assumed sign gives dbt>=dax. Therefore

\[
                   0<x\le\delta<1/60,\qquad t>x.
\tag{11}
\]

We first verify that B is unique in this entire subdomain,
including its original u=0 side mean.

If u>0, p_AB=P_12 and

    |p_AB|^2=d^2+2-2d(a+b)<d^2.

Every point of a physical radial body has norm at least d,
so B is unique.

If u=0, the original m=f_2 line has Z=ka=a(d-q). In the
absolute f_1,f_2 coordinates its application is therefore

    p_AB=(-a q, 1-db).

The exact root channel intersection gives

\[
 k=\frac{t}{bx+at}
   \ge\frac{1}{1+bx/t}\ge1-\frac{bx}{t},
 \qquad q\le\delta+\frac{bx}{t}.
\tag{12}
\]

From 1-da>=-delta and (10) one has

    dbt<=delta(1+x).

As d>=1 and t^2=(1-x)(1+x), (12) yields

\[
                 0<q\le\frac{\delta}{1-x}
                       \le\frac{60}{59}\delta<2\delta.
\tag{13}
\]

Consequently

\[
 |p_{AB}|^2=a^2q^2+(1-db)^2
       <1+4\delta^2<1+2\delta+\delta^2=d^2.
\tag{14}
\]

The final reserve is delta*(2-3delta)>0. Thus B is unique
in this side-axis case also.

For every Z in [0,1], its original application has

    (p_AB)_y=a-bZ>=a-b>43/61>7/10>R-sqrt(2).

Thus the B ports are distinct, and the same local chord
conclusion (7) applies. By 0<=u<=v and (11),

    (-m) dot n = -ux+vt >=v(t-x)>0.

The root turn is acute and theta_C<pi, so theta_B>pi/2.

Put r=1-Z>=0. Since t>0, the exact n,f coordinates of the
B port difference are

\[
 \begin{split}
 (p_{BV}-p_{BA})\cdot n&=1-\alpha+t+rx>t,\\
 (p_{BV}-p_{BA})\cdot f&=1/2+T+\beta-x+rt>1/2-x>0.
 \end{split}
\tag{15}
\]

Therefore

\[
 |p_{BV}-p_{BA}|^2
    >t^2+(1/2-x)^2
     =5/4-x
     >5/4-1/60=37/30>1.
\tag{16}
\]

This contradicts (7). The contradiction covers n dot e_x=0
as well as the strictly positive sign. Hence n dot e_x<0,
and (4) is proved.

## 3. Full-family use and retained obligation

The source S_LEAF_C5_ALIGNED_DIRECT_NORMAL_HALFPLANE.md
already gives the corresponding entire aligned restriction:
after reflection its actual channel points west/up and its
actual direct force points west/down or vertically down.
The present theorem gives both west signs strictly in the
entire tilted family, with the opposite vertical ordering
chosen in (2).

Together with the two far-endpoint sources, these are original
necessary conditions on the same complete selected certificate.
They can be used in a common completion argument with the
actual radial C, genuine U--C sharing, unchanged U,V sliders,
and all three extras.

They do not close M6.B5L.C5.L13.S. In particular no
three-extra allocation is removed merely by these normal
signs, and no numerical core search is used as a premise.
