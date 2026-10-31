# The entire two-vertex tilted S-leaf bowtie interface is impossible

**Status: complete whole-owner hand exclusion; root and separate
independent full audits passed.** Use the exact component, common
certificate and full domain in TIP_LEAF_BOWTIE_S_TILTED_DOMAIN.md.
This source handles its first interface: B meets the far A vertex W,
H the lower adjacent vertex P, and both normals are neighbor-owned.
Every mutual BH owner, shared mean and physical B mask is retained.

## 1. Exact coordinates and the whole opposite petal

Use the orthonormal vector frame (-u,v) from the domain source, and put
\[
 \begin{gathered}
 q=D-\sigma>0,\quad X=1-\sigma a,\quad
 Y=1-\sigma b,\quad Z=\sigma b,\quad Y+Z=1,\\
 N=\sqrt{X^2+Y^2},\qquad J=\sqrt{X^2+Z^2},\\
 n=(-X,Y)/N,\quad v_B=(-Y,-X)/N,\\
 m=(-X,-Z)/J,\quad k=(Z,-X)/J,\\
 K=\frac{X}{NJ}>0,\qquad L=\frac{X^2-YZ}{NJ},
 \qquad m=Ln+Kv_B,\quad k=-Kn+Lv_B.
 \end{gathered}
\tag{1}
\]
Here n points A to B and m points A to H. Strictness of the
two A vertices gives X,Y>0, and sigma>=0 gives Z>=0.
The actual ports, measured from the original circle origin, are
\[
                   Q=(Da-1,-Db)\in A\cap H,
                  \qquad P=Q+(0,1)\in A\cap B.
\tag{2}
\]
Each is in the relative interior of its neighbor's support side.
In particular B owns n and H owns m.

Let g be the B-to-H normal, with magnitude gamma>0, and write the
positive AB,AH magnitudes as mu,nu. The real equations are
\[
                   F_B=\mu n-\gamma g,\qquad
                   M=F_C+F_E=\nu m+\gamma g.
\tag{3}
\]
The triangle owned-normal lemma gives
\[
                         n\cdot g\le0,\qquad m\cdot g\ge0.
\tag{4}
\]
Thus M·m>0, for every mutual normal, including a free one.

## 2. A nonnegative inner H face is excluded for the whole petal

Put rho_H=Q·m. If rho_H>=0, every H point has m-coordinate at
least rho_H. The genuine end-triangle concurrence is a negative
multiple of M, with strictly negative m-coordinate. Its behind-port
equations therefore make both C,E root normals have positive
m-component. Both actual applications lie on H's maximum-m side,
including all owner and free-normal endpoints. Parallel petal normals
give the same conclusion directly. The side's height1+rho_H>=1
contradicts the complete high-face theorem.

We may therefore assume rho_H<0. Its exact numerator is
\[
                   J\rho_H=1-Da+\sigma(D-a)<0.
\tag{5}
\]
If D<a, this affine numerator decreases with sigma, but even its
value at sigma=D is (D-a)^2+b^2>0. Thus that entire low-D case is
impossible here. If D>=a, its nonnegative slope makes negativity
force Da>1. This proves the first two strict implications below
without presuming a sign for D-a.
In particular
\[
 D>1,\qquad a>\frac1D>\frac{60}{61},\qquad
 b<\frac{11}{61}<\frac3{16},\qquad
 0\le\sigma<\frac{Da-1}{D-a}<1.
\tag{6}
\]
Also rho_H>1-D>-1/60: in (1)--(2),
rho_H=((1-Da)X+DbZ)/J, and X/J<=1.

B is physically unique in this domain. Its actual point P has
\[
                       |P|^2=D^2+2-2D(a+b)<D^2.
\tag{7}
\]
Every point of a physical radial-S square has norm at least D.
Thus B cannot have two physical circle corners. All its unique
circle-corner orientations remain.

A free BH edge is removed by the compatible
GENERAL_FIXED_TIP_NORMAL_SELECTION.md: AB is a fixed side-interior
application of the unique B, whereas a free BH application is a
distinct vertex. The common prelist includes these stars with arbitrary
H degree and preserves every surviving point normal through uncrossing
and thinning. No new normal is chosen after a stress is extracted.

## 3. The complete mutual-owner cover

Equation (4) leaves only g=-n or v_B if B owns the edge, and g=m
or k if H owns it. All shared sides are included.

For g=-n, B's two forces have the same inward direction n. The
parallel-force radial classification makes B radial S along its owned
side axis n, contradicting (7). For g=m, M is a positive multiple
of the H axis m. END_TRIANGLE_AXIS_RESULTANT_SUPPORT_BOUND.md
puts both petal ports on the maximum-m side, whose height
\[
                             1+\rho_H>\frac{59}{60}
\tag{8}
\]
is forbidden by the high-face theorem.

For g=k, L<0 would make the mutual point B's minimum-n/minimum-v_B
vertex P-rho v_B, with rho>0. Its m-coordinate relative to Q is
-Z/J-rho K<0, impossible since Q minimizes m on H. L=0 gives
k=-n, already excluded. Hence L>0 in this case.

For g=v_B, L<0 would make the mutual point H's minimum-m/maximum-k
vertex Q+r k, with r>0. Its n-coordinate relative to P is
-Y/N-rK<0, impossible since P minimizes n on B. L=0 gives
v_B=m, already excluded. Thus both remaining cases have
\[
                          L>0,\qquad K\ge L.
\tag{9}
\]
The last inequality follows from L/K=X-YZ/X<=X<=1.

## 4. The unique circle corner and actual radial advance

Write
\[
 \rho=P\cdot n=
       \frac{2-(D+\sigma)(a+b)+D\sigma}{N},\qquad
 V_0=-P\cdot v_B=\frac{q(a-b)}N>0.
\tag{10}
\]
The B force in either remaining case has positive n-coordinate and
negative v_B-coordinate. Its unique physical circle corner is
\[
              z_B=X_B n-Y_B v_B,\qquad
              X_B=1+\rho,\qquad Y_B=V_0+\rho_B,
\]
\[
              0<\rho_B<1,\qquad V=1-\rho_B\in(0,1),
                  \qquad X_B^2+Y_B^2=R^2.
\tag{11}
\]
The actual B is P+[0,1]n+[-rho_B,1-rho_B]v_B; no position of
its AB mean inside that side has been fixed.

The function rho in (10) increases with sigma. In original vector
coordinates n=(sigma-a-b,a-b)/N; direct differentiation gives
rho'=q(a-b)^2/N^3>0. Consequently (6) gives
\[
 \rho\ge\frac{2-D(a+b)}{\sqrt2}
    >\frac{761}{960\sqrt2}>\frac{11}{20},
           \qquad X_B>\frac{31}{20}>\frac R{\sqrt2}.
\tag{12}
\]
For the first strict bound use a+b<19/16 and D<61/60;
for the next use sqrt(2)<10/7. Thus X_B>Y_B.

The proper B concurrence is P+A_B n, A_B>=0. Its positive
proportionality to z_B gives the exact advance
\[
                        A_B=\frac{V_0X_B}{Y_B}-\rho.
\tag{13}
\]
In particular
\[
                   (A_B-V)Y_B=-\rho_B(X_B-Y_B)<0,
                     \qquad A_B<V.
\tag{14}
\]

## 5. The H-owned transverse contact is impossible

For g=k with L>0, the B application is its minimum-n/maximum-v_B
vertex T=P+Vv_B. Intersecting the actual k line through T with
the AB n line gives
\[
                             A_B=\frac{VK}{L}\ge V.
\tag{15}
\]
This contradicts (14). No H side mean has entered the calculation.

## 6. The B-owned transverse contact is impossible

For g=v_B, its actual application is T=P+t n+Vv_B, 0<=t<=1.
On H it is the minimum-m/minimum-k vertex Q-r k, with r>0.
Equating its m-coordinate gives
\[
                 Lt+KV=\frac ZJ,\qquad
                 V\le\omega:=\frac{Z}{JK}
                      =\frac{\sigma bN}{X}.
\tag{16}
\]
Since V>0, this also forces sigma>0. All strict divisions and
positive-square-root comparisons below therefore retain their endpoints.
The proper B advance is t>=0. Equations (11),(13) give
V_0>=rho rho_B, and hence
\[
 A_D(1-\omega)-(D-\sigma)(a-b)\le0,\qquad
 A_D=2-(D+\sigma)(a+b)+D\sigma.
\tag{17}
\]
Here omega<1: L>0 gives X^2>YZ and therefore
\[
                  \omega^2=Z^2(1+Y^2/X^2)<Z=\sigma b<1.
\tag{18}
\]

Put p=a+b, k_0=a-b and A_1=2-(1+sigma)p+sigma. Since
sigma<1 and p<19/16, we have 0<A_1<1. The left side of (17)
is affine in D. Its value at D=1 is
\[
 F_1=A_1(1-\omega)-(1-\sigma)k_0
       =2(1-a)+\sigma(1-2b)-A_1\omega.
\tag{19}
\]
The coefficient lost on increasing D from1 is
(p-sigma)(1-omega)+k_0<=p+k_0=2a<2. Thus
\[
                              F_1<\frac1{30}.
\tag{20}
\]

First, sigma<1/2. Otherwise (18)--(19) imply
\[
 F_1\ge b^2+\sigma(1-2b)-\sqrt{\sigma b}
      \ge\frac{89}{256}-\frac{\sqrt6}{8}
      >\frac{53}{1280}>\frac1{30}.
\tag{21}
\]
For the middle comparison, the displayed function increases with
sigma on [1/2,1] and decreases with b on (0,3/16]; evaluate at
sigma=1/2,b=3/16. Its derivatives have these strict signs directly.
The rational estimate uses sqrt(6)<49/20.

Now X>1/2 and Y<=1, so N/X<sqrt(5)<9/4. Equations
(19)--(20) give
\[
 F_1\ge b^2+\sigma(1-17b/4)>13\sigma/64,
             \qquad \sigma<\frac{32}{195}<\frac16.
\tag{22}
\]
Consequently X>5/6 and N/X<sqrt(61)/5<8/5. Repeating the
same exact inequality gives
\[
 F_1>\frac{13}{40}\sigma,\qquad
 \sigma<\frac4{39},\qquad
 \omega<\frac2{65},\qquad \rho_B>\frac{63}{65}.
\tag{23}
\]

Finally, (6),(10),(23) and sqrt(2)<10/7 imply
\[
 V_0>\frac{35}{39}\frac{49}{61}\frac7{10}
          =\frac{12005}{23790}>\frac12.
\]
Thus Y_B>1/2+63/65>7/5. Together with (12), the actual circle
corner would satisfy
\[
 R^2=X_B^2+Y_B^2>\left(\frac{31}{20}\right)^2+\left(\frac75\right)^2
          =\frac{349}{80}
          =\frac{1105}{256}+\frac{59}{1280},
\tag{24}
\]
which contradicts the radius window.

Sections 2--6 exhaust every physical B mask, free or owned mutual
normal, shared-side application and parallel-force endpoint. They
exclude the entire two-vertex interface of the tilted S articulation.
No degree-two equation was assigned to H, and the C,E petal and all
completion squares remained physically present.
