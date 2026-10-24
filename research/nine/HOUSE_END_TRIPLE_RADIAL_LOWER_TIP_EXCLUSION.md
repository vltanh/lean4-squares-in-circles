# The entire physical radial lower-tip mask of an end-triple house is impossible

**Status: complete hand physical-mask exclusion; root and separate independent
full hand audits passed.** Use the exact end-triple graph
\[
                         UN,UB,HN,HB,HT,NT,
\tag{1}
\]
with N,B,T loaded and U,H clear. Work throughout
\[
                 R_0=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{2}
\]
Every actual U/roof mean, every physical N/T circle mask, either zero
individual circle weight of B, and all four extra squares are retained.

**Theorem.** The lower loaded degree-two body B cannot have two physical
circle corners. Together with HOUSE_END_TRIPLE_UNIQUE_TILTED_TIP_EXCLUSION.md,
the entire remaining end-triple family therefore has B parallel to U and
exactly one physical circle corner.

No degree-two force or torque equation is imposed on N. The proof puts
the entire required loaded N strictly inside the circle. It uses neither
a secondary minimizer nor a new normal-selection convention.

## 1. Exhaustive reduction to the B-owned tilted side

The parallel H/U frame is already excluded. Use the complete tilted
bypass coordinates, with the true circle origin O kept separately:
\[
 U=[0,1]^2,\quad B\subseteq\{y\le0\},\quad N\subseteq\{y\ge1\},
 \qquad P_B=(\xi,0),\quad P_N=(\xi,1),\quad0\le\xi\le1,
\tag{3}
\]
\[
 H=P+[0,1]u+[0,1]v,\quad P=(d_0,e),\quad
 u=(a,b),\quad v=(b,-a),\quad a,b>0,\quad a^2+b^2=1,
\]
\[
                        d_0\ge1,\qquad1-b\le e\le a.
\tag{4}
\]
The lower and upper H vertices are L=P+v and V=P+u.
The complete quadrant and feature theorem gives, for the actual normals
from B,N into H,
\[
 (n_B)_x\ge0,\quad(n_B)_y>0,\qquad
 (n_N)_x\ge0,\quad(n_N)_y<0.
\tag{5}
\]
Both HB and HN are singletons. All HN points lie on PV. An actual HN
point Q_N has positive horizontal displacement from P_N and satisfies
\[
                           |Q_N-P_N|\le1.
\tag{6}
\]
These are geometric statements independent of N's degree-three load
equation and of its circle-corner mask.

First suppose B is tilted relative to U. The entire H-owned and genuine
free HB alternatives have already been excluded by
HOUSE_END_TRIPLE_RADIAL_HUB_OWNER_EXCLUSION.md, including its Section5.
The actual HB normal is therefore owned by B, with a strict
relative-side-interior application. Write
\[
 w=(-c,-s),\quad k=(s,-c),\quad c,s>0,\quad c^2+s^2=1,
 \qquad B=P_B+[0,1]w+[0,1]k.
\tag{7}
\]
The positive vertical and nonnegative horizontal components in (5)
force
\[
              n_B=-w=(c,s),\qquad L=P_B+\tau k,\qquad0<\tau<1.
\tag{8}
\]
The actual location (4) gives
\[
                    b\le\tau s,\qquad
                    \tau c\le a+b-1<b.
\tag{9}
\]
In particular c<s.

Put
\[
                h=\sqrt{R^2-\tfrac14}-1,\qquad
                        \frac9{10}<h<\frac{51}{50}.
\tag{10}
\]
The top U application P_B cannot be a circle vertex. The outward
radial axis of the physically radial B is consequently w or k.
Let mu>0 and nu>0 be its actual UB and HB magnitudes. Its true outward
circle resultant is
\[
              F_B=(\nu+\mu s)w+\mu c\,k.
\tag{11}
\]
If the radial axis were k, the physical circle cone would require
\[
 \frac{|F_B\cdot w|}{F_B\cdot k}\le\frac1{2(h+1)}<1.
\]
Equation(11) instead gives this ratio greater than s/c>1. Therefore
the radial axis is w, and its actual physical pose gives
\[
                       P_B-O=h w-\frac12k.
\tag{12}
\]

The two physical circle vertices are P_B+w and P_B+w+k. Their actual
weighted tangential parameter, say rho in [0,1], satisfies
\[
 \rho=\frac12+(h+1)\frac{\mu c}{\nu+\mu s}.
\]
Taking B's actual torque about P_B gives
rho(nu+mu*s)=tau*nu+mu*c. Substitution yields the exact relation
\[
                 \nu\left(\tau-\frac12\right)
                          =\mu\left(hc+\frac s2\right)>0.
\tag{13}
\]
In particular tau>1/2. This calculation retains both endpoints of the
physical circle-weight interval; no equal-weight assumption is made.

Every actual HN point has the full form
\[
                  Q_N=P+\sigma u,\qquad0<\sigma\le1.
\]
Combining this with (8) gives its actual chord
\[
 q=Q_N-P_N=(\tau s-b+\sigma a,\ a-\tau c+\sigma b-1).
\tag{14}
\]
The first coordinate is positive and the second nonnegative.

## 2. The full lower-frame bound c<5/8

Suppose c>=5/8. Since c<s, we have s/c<=sqrt(39)/5<5/4.
Also (9) gives tau*c<=sqrt(2)-1<5/12. Consequently
\[
                \tau s<\frac{25}{48}<\frac1{\sqrt2}.
\]
The function sqrt(1-x^2)+x increases up to x=1/sqrt(2).
Using b<=tau*s and a+b>=1+tau*c therefore gives
\[
           \sqrt{1-\tau^2s^2}+\tau s\ge1+\tau c.
\]
Its rearranged right side 1-tau(s-c) is positive. Squaring and using
tau>1/2 yields
\[
                   s^2+(s-c)^2-4(s-c)<0.
\tag{15}
\]
For s=sqrt(1-c^2), the left side is
f(c)=2-c^2-2cs-4s+4c. Its derivative is
\[
 f'(c)=4-2c-2s+\frac{2c^2+4c}{s}>4-2(c+s)>0.
\]
But
\[
 f(5/8)=\frac{263-42\sqrt{39}}{64}>0,
                  \qquad263^2-42^2\cdot39=373>0.
\]
This contradicts (15). Hence, throughout the actual domain,
\[
                         0<c<\frac58,\qquad s>\frac{39}{50}.
\tag{16}
\]

## 3. Both uniform upper-frame angle bounds

Suppose N is tilted to U. Its unique bottom vertex is P_N, and (5)
places Q_N on its right upward incident side. Write
\[
 N=P_N+[0,1]j+[0,1]Jj,\qquad
 j=(\cos\beta,\sin\beta),\quad0\le\beta<\pi/2.
\tag{17}
\]
Thus q is a positive multiple of j, of length at most1.
Put c=cos(psi), s=sin(psi), with 0<psi<pi/2.

First,
\[
                              \beta<\psi/2.
\tag{18}
\]
Indeed D(sigma)=s*q_x-(1+c)*q_y is affine in sigma. At sigma=0
it is strictly positive by tau*s>=b and 1+tau*c>a. At sigma=1,
using tau>=b/s gives
\[
 \begin{split}
 D(1)&=(1+c)(1+\tau)-a(1+c-s)-b(1+c+s)\\
 &\ge(1+c)\left[
 1-a\left(1-\frac{s}{1+c}\right)-b\left(1-\frac cs\right)\right]>0.
 \end{split}
\]
For the final inequality put r=c/s in (0,1). The first coefficient
1-s/(1+c) is at most r, because s<=1. The bracket is therefore at
least 1-ar-b(1-r)>0, since a,b<1. This proves (18).

A second full-domain bound is
\[
             \tan\beta<
                       1-\sqrt{c+\frac{c^2}{4}}.
\tag{19}
\]
From (14), q_x>=sigma*a. Its nonnegative second coordinate gives
\[
 \tan\beta\le\frac{b}{a}+\frac{a-1-\tau c}{\sigma a}
       \le1+\frac{b-1-\tau c}{a}
       <1-\frac{1+c/2-b}{a}.
\]
For K=1+c/2, the exact identity
(K-b)^2-(K^2-1)a^2=(Kb-1)^2>=0 proves
(K-b)/a>=sqrt(K^2-1), which yields (19).

## 4. Every tilted N is strictly inside the circle

Equation(12) gives
\[
           P_N-O=(-A,B_0),\qquad
           A=hc+\frac s2,\quad B_0=1-hs+\frac c2.
\tag{20}
\]
If c<=sqrt(2)-1, the complete algebra of Sections2--3 of
HOUSE_END_TRIPLE_RADIAL_HUB_OWNER_EXCLUSION.md applies. Precisely,
it uses only (20), c<=sqrt(2)-1, (10), and beta<psi/2, all proved
here. It first gives |P_N-O|<R-1; the two adjacent corners are then
strictly inside. For the opposite corner its exact positive deficit is
\[
 R^2-|P_N-O+j+Jj|^2
 =2h+(2hs-2-c)(1+L)+(2hc+s)K_0>0,
\tag{21}
\]
where L=cos(beta)+sin(beta), K_0=cos(beta)-sin(beta).
The source's bound at beta=psi/2 gives the strict margin
(1+sqrt(1+s))*17/120. No HB ownership premise is used by these
algebraic inequalities.

Now suppose sqrt(2)-1<=c<5/8. Equation(19) implies
\[
              \tan\beta<\frac{13}{40}<\tan(\pi/8).
\tag{22}
\]
For the first inequality, at c=sqrt(2)-1 one has
c+c^2/4=(2sqrt(2)-1)/4>(27/40)^2; the left side increases
with c. The second follows from sqrt(2)>53/40.

The deficit in (21) increases with h. At h=9/10 it decreases
with beta on [0,pi/8]. At that fixed h it also decreases with c:
its c derivative is
(-9c/(5s)-1)(1+L)+(9/5-c/s)K_0<0, using 1+L>=2,
K_0<=1. It is therefore bounded below by its value at c=5/8,
beta=pi/8, h=9/10. The elementary bounds
\[
 s>\frac{39}{50},\quad L<\frac{21}{16},\quad K_0>\frac{27}{50}
\]
give the strict positive estimate
\[
 \frac95-\frac{1221}{1000}\frac{37}{16}
                       +\frac{381}{200}\frac{27}{50}
                           =\frac{411}{80000}>0.
\tag{23}
\]
The opposite corner is strictly inside.

It remains to bound the two adjacent corners without assuming P_N is
as central as in the smaller-c case. The farther one is P_N+Jj:
A>0, B_0>0 and beta<pi/4 make its squared norm larger than both
|P_N-O|^2 and |P_N-O+j|^2. Its squared norm is
\[
                 (A+\sin\beta)^2+(B_0+\cos\beta)^2.
\tag{24}
\]
Half its h derivative is
h+c*sin(beta)-s(1+cos(beta))<0: using (10),(16),(22),
it is less than 51/50+1/4-(39/50)(19/10)<0.
We may set h=9/10 for an upper bound.
At that h, (24) increases with c and with beta on the declared
interval. Both A and B_0 increase with c; and its beta derivative
has the sign of A*cos(beta)-B_0*sin(beta)>0.
For example A>3/4, B_0<7/10, cos(beta)>9/10,
sin(beta)<2/5 already prove the last strict inequality.

If c<=29/50, evaluate at c=29/50 and
beta=arctan(13/40). At this comparison point,
\[
 A<\frac{93}{100},\quad B_0<\frac{14}{25},\quad
 \sin\beta<\frac{31}{100},\quad\cos\beta<\frac{24}{25}.
\]
For the first two inequalities use
73/90<sqrt(1659)/50<102/125; the two trigonometric inequalities
follow by squaring. Thus (24) is strictly less than
\[
             (31/25)^2+(38/25)^2=\frac{481}{125}<R_0^2,
               \qquad R_0^2-\frac{481}{125}=\frac{421}{8000}.
\tag{25}
\]

If 29/50<=c<5/8, (19) gives tan(beta)<3/16 because
sqrt(6641)/100>13/16. At h=9/10 and c<=5/8,
\[
                 A<\frac{61}{64},\qquad
                 B_0<\frac{1221}{2000}.
\]
Here sqrt(39)<25/4 and sqrt(39)>156/25 give the stated bounds.
Using sin(beta)<3/16 and cos(beta)<=1 in (24) gives
\[
 (24)<(73/64)^2+(3221/2000)^2<R_0^2,
\quad
 R_0^2-(73/64)^2-(3221/2000)^2
                       =\frac{376919}{64000000}>0.
\tag{26}
\]
Equations(21)--(26) exhaust every tilted N and all four of its corners.

## 5. Parallel N: the entire actual bottom-side mean interval

Suppose N is parallel to U. Both P_N and Q_N lie on its bottom side.
Put ell=Q_N,x-xi>0. Its lower-left corner is P_N-rho*e_x with
\[
                            0\le\rho\le1-\ell.
\tag{27}
\]
The zero vertical coordinate of (14) gives
a+sigma*b=1+tau*c. Write r=c/s and t_0=b/(1+a). Since
tau>=b/s, it follows that
\[
 \sigma\ge\frac{1-a}{b}+\frac cs=t_0+r,\qquad
 \ell=\tau s-b+\sigma a\ge\sigma a
           \ge r+t_0(a-br)\ge r.
\tag{28}
\]
The last inequality uses b<=tau*s<=s, hence a>=c and
a-br>=0. It retains every actual mean in (27).

There is a useful strict improvement throughout c>=1/2:
\[
                            \ell>r+\frac1{32}.
\tag{29}
\]
Indeed tau*c<=sqrt(2)-1<5/12 and s/c<=sqrt(3)<7/4 give
b<=tau*s<35/48, hence a>2/3. Therefore
a-br>=a-tau*c>1/4. Also a+b>=1+tau*c implies
b>tau*c>c/2>=1/4, so t_0>1/8. Equation(28) proves (29).

Take K=1 for c<=1/2 and K=31/32 for c>=1/2. All four N corners
have horizontal absolute value at most
\[
                    Z=K+hc+\frac s2-\frac cs
\tag{30}
\]
and vertical absolute value at most
\[
                         Y_*=2-hs+\frac c2.
\tag{31}
\]
For the left coordinate this is (27)--(29). For the right coordinate
it suffices to bound 1-A by Z. If c<=1/2, r<s<2A.
If c>=1/2, 2A>9/10+39/50 while r+1/32<1+1/32;
again the required inequality is strict. The vertical assertion holds
because B_0>-1/2.

Half the h derivative of Z^2+Y_*^2 is exactly
\[
        cZ-sY_*=h+Kc-s-\frac1s
                      <\frac{51}{50}+\frac58-2<0.
\tag{32}
\]
It remains to bound F(c,K)=Z^2+Y_*^2 at h=9/10. This function
strictly increases with c throughout 0<=c<=5/8 for each of the two
values of K. For completeness, with r=c/s its derivative is
\[
 F_c=1+\frac95K-Kr-\frac95r^3
                         +2(r-K)(1+r^2)^{3/2}.
\tag{33}
\]
Here 0<=r<=5/sqrt(39)<31/32<=K. The exact inequality
\[
 (1+r^2)^{3/2}\le1+\frac32r^2+\frac38r^4
\]
follows by squaring: the difference of the squares is
r^6/8+9r^8/64>=0. Because r-K<0, (33) is bounded below by
the resulting polynomial, which decreases with K. Setting K=1
therefore gives
\[
 F_c\ge(1-r)\left(\frac45+\frac95r-\frac65r^2-\frac34r^4\right)
                 \ge(1-r)\frac{13}{20}>0.
\tag{34}
\]
The last step uses r^2,r^4<=r and r<1.

For c<=1/2, monotonicity gives
\[
 F(c,1)\le F(1/2,1)
      =\frac{1169}{150}-\frac{34\sqrt3}{15}
       <\frac{484}{125}<R_0^2,
                 \qquad R_0^2-\frac{484}{125}=\frac{229}{8000},
\tag{35}
\]
where sqrt(3)>173/100.
For c>=1/2, evaluate F at c=5/8 and K=31/32. There
\[
 Z=\frac{49}{32}-\frac{41}{16\sqrt{39}}<\frac{897}{800},
 \qquad
 Y_*=\frac{37}{16}-\frac{9\sqrt{39}}{80}<\frac{3221}{2000}.
\]
Consequently
\[
 F(c,31/32)<(897/800)^2+(3221/2000)^2<R_0^2,
\quad
 R_0^2-(897/800)^2-(3221/2000)^2
                         =\frac{795411}{16000000}>0.
\tag{36}
\]
Equations(35)--(36) exhaust the full parallel N family, including its
entire interval of actual bottom-side means.

Sections4--5 show that no N corner can meet the circle. This excludes
the entire remaining B-owned tilted radial B.

## 6. Every parallel physical radial B is excluded as well

Finally suppose B is parallel to U and has two physical circle corners.
Write B=[q-1,q]x[-1,0]. Its actual HB application has x>1, so q>1.
The pair equation F_B=-mu*e_y-nu*n_B, together with (5), has
nonpositive horizontal and strictly negative vertical components.
Thus B's outward physical radial axis cannot be +e_x or +e_y:
the radial component of every positive circle resultant has the sign
of that axis, even with an arbitrary split between the two corners.

If its radial axis is -e_x, its center alignment gives
O=(q+h,-1/2). The U corner (0,1) would have squared norm relative
to O strictly larger than
\[
                   (1+h)^2+\frac94=R^2+2,
\]
contrary to containment.

If its radial axis is -e_y, write O=(x_0,h). The actual U mean P_B
lies on B's upper side, so |xi-x_0|<=1/2. Hence
\[
               |P_N-O|^2\le\frac14+(1-h)^2<\frac{13}{50}.
\]
Every point of the unit N is at distance at most sqrt(2) from its
actual point P_N. Therefore all N points have norm less than
\[
       \sqrt{13/50}+\sqrt2<\frac{51}{100}+\frac{99}{70}
                         =\frac{1347}{700}<R_0.
\tag{37}
\]
Again N is strictly circle-clear, contradicting its positive load.
This argument has not required equal radial corner weights, a vertex
U application, or any equation for N beyond its required positive load.

## 7. Whole physical-mask conclusion

The parallel and tilted B frames have both been exhausted. The tilted
frame's H-owned and genuine-free contacts are covered by the preceding
complete source; its B-owned side is excluded here with all actual
tau and sigma values. The parallel frame retains its actual UB mean
and both possible physical radial directions. Thus B cannot have two
physical circle corners in any end-triple house.

The only remaining end-triple family has B parallel to U and a unique
physical circle corner. Its entire U mean, HB ownership/free transition,
N/T masks and roof means still require a whole exclusion or a joint
capacity bound for the four extras. No closure of that parent is
asserted by this physical-mask theorem.
