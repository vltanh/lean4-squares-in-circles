# A tilted radial lower tip must own its house contact

**Status: complete hand owner-family exclusion; root and separate independent
full hand audits passed.** Use the end-triple house labels N,B,T loaded and
U,H clear, with exact positive edges
\[
                       UN,UB,HN,HB,HT,NT.
\tag{1}
\]
Put R_0=79/40 and work throughout R_0<=R<=sqrt(1105)/16 with all four extra squares,
all actual U/roof means and every physical N/T circle mask retained.

**Theorem.** Suppose B is tilted relative to the side-normal transmitter
U and has two physical circle corners. Its actual HB normal cannot be
a side axis of H or a genuine free point normal. It must be owned by B
at a strict relative-side-interior application. Both circle weights of B,
including either individual zero weight, remain allowed. The proof shows that the entire square N
would be strictly inside the containing circle, contradicting its load.

No degree-two equation is imposed on N, whose positive degree is three.
No normal, contact point or extra square is changed.

## 1. The complete actual-contact coordinates

The parallel H/U frame is already excluded. Use the full domain of
`HOUSE_END_TRIPLE_TILTED_BYPASS_DOMAIN.md`:
\[
 U=[0,1]^2,\quad B\subseteq\{y\le0\},\quad
 N\subseteq\{y\ge1\},\quad
 P_B=(\xi,0),\quad P_N=(\xi,1),\quad0\le\xi\le1,
\tag{2}
\]
\[
 H=P+[0,1]u+[0,1]v,\quad P=(d_0,e),\quad
 u=(a,b),\ v=(b,-a),\quad a,b>0,\quad a^2+b^2=1,
\]
\[
                  d_0\ge1,\qquad1-b\le e\le a.
\tag{3}
\]
Denote its upper vertex by V=P+u. HB and HN are singleton contacts.
The endpoint normal from B into H has positive vertical and
nonnegative horizontal component; the normal from N into H has
negative vertical and nonnegative horizontal component. These are the
geometric quadrant conclusions in Section1 of
`HOUSE_END_TRIPLE_UNIQUE_TILTED_TIP_EXCLUSION.md`; that section makes
no unique-corner or degree-two assumption on N. They also follow
directly from the lower/upper H support features and the nonnegative
horizontal components in the full tilted-domain source.

If H owns HB, its actual inward normal from B is u, and
\[
                         Q_B=P+t v,\qquad0\le t\le1.
\tag{4}
\]
The domain excludes both HB and HN being H-owned. Consequently the
actual HN point is V. This uses the full unloaded H force equation
and the actual H,N,T triangle, as proved in that domain; it does not
split N into a fictitious degree-two tip.

Since B is tilted, its top U contact P_B is its unique top vertex.
Label its two inward axes
\[
 w=(-c,-s),\qquad k=(s,-c),\qquad
 c,s>0,\quad c^2+s^2=1,
 \qquad B=P_B+[0,1]w+[0,1]k.
\tag{5}
\]
The u projection of w is negative. The projection of k cannot be
negative, since that would select P_B itself rather than an HB point
strictly to its right. It cannot be zero: the corresponding parallel
HB supports would either share a segment, already excluded, or be a
point-only vertex/vertex axis endpoint forbidden by the retained
strict convention. Thus
\[
                        as-bc>0,\qquad Q_B=P_B+k.
\tag{6}
\]

A physical circle point cannot be shared. Therefore P_B is an inner
vertex of the radial-S square B. Its outward radial axis is either w
or k; the opposite choices would make P_B a circle vertex. The choice
k would make P_B+k a circle vertex, also impossible by (6). Hence its
radial axis is w. Put
\[
             h=\sqrt{R^2-1/4}-1,\qquad
                  \frac9{10}<h<\frac{51}{50}.
\tag{7}
\]
Writing O for the true circle origin in the displayed coordinates,
the physical radial frame gives exactly
\[
                      P_B-O=h w-\frac12k.
\tag{8}
\]
No equal-weight assertion is made.

Comparing (4),(6) in the vertical coordinate gives e=ta-c. Hence
\[
        c\le a+b-1\le\sqrt2-1<\frac{29}{70}<\frac5{12},
                \qquad s>\frac{91}{100}>\frac9{10}.
\tag{9}
\]
For the rational bounds use sqrt(2)<99/70 and
2sqrt(2)-2>(91/100)^2; the latter is equivalent to
28281^2<800000000. The bound h<51/50 follows by squaring
h+1=sqrt(R^2-1/4)<=sqrt(1041)/16<101/50.

In ordinary horizontal/vertical coordinates, (8) yields
\[
 P_N-O=(-A,B_0),\qquad
          A=hc+\frac s2>0,\quad B_0=1-hs+\frac c2.
\tag{10}
\]
The actual chord to V is
\[
 q:=V-P_N=(s+a-tb,\ ta+b-c-1).
\tag{11}
\]
It has positive first and nonnegative second coordinate. Moreover
\[
 q-(s,-1-c)=(a-tb,ta+b),
                       \qquad |q-(s,-1-c)|^2=1+t^2\le2.
\tag{12}
\]
All actual means in (2) and the complete side interval in (4) remain.

## 2. The U application is too central for an adjacent circle corner

From (10),
\[
 |P_N-O|^2=h^2+\frac54-2hs+c.
\]
Since R^2=(h+1)^2+1/4, subtracting (R-1)^2 gives
\[
 |P_N-O|^2-(R-1)^2
                         =2R-1-2h(1+s)+c.
\tag{13}
\]
For fixed c,s this expression strictly decreases with R: its
derivative is 2-2R(1+s)/(h+1)<-2s<0. At R=79/40, use
h>9/10, s>9/10 and c<5/12 to obtain the strict bound
\[
 \frac{59}{20}-\frac95\frac{19}{10}+\frac5{12}
                            =-\frac4{75}<0.
\tag{14}
\]
Thus
\[
                              |P_N-O|<R-1
\tag{15}
\]
uniformly. Every N vertex adjacent to P_N is therefore strictly
inside the circle when P_N is a vertex. The parallel-frame case,
where P_N may be a genuine side mean, is handled separately below.

## 3. Every tilted N is strictly inside the circle

Suppose first N is tilted to U. Its U contact P_N is its unique
bottom vertex. The actual HN normal has nonnegative horizontal and
strictly negative vertical component. Exactly as in the elementary
support-chord lemma of the preceding source, this places V on N's
rightward upward side from P_N. Write its inward axes
\[
                 j=(\cos\beta,\sin\beta),\qquad Jj,
                 \quad0\le\beta<\pi/2,
                 \qquad N=P_N+[0,1]j+[0,1]Jj.
\tag{16}
\]
The actual vector q is a positive multiple of j, of length at most1.
No side mean at HN is replaced by a vertex here.

Put c=cos(psi), s=sin(psi), with 0<psi<pi/2. The vector
q_0=(s,-1-c) has squared length 2+2c>2. Equation(12) implies
\[
                 2q\cdot q_0=|q|^2+|q_0|^2-|q-q_0|^2>0.
\]
Consequently
\[
 s\cos\beta-(1+c)\sin\beta>0,
                      \qquad 0\le\beta<\frac\psi2.
\tag{17}
\]
This is an all-angle consequence of the actual chord, not a chosen
orientation for N.

The base and the two adjacent N vertices are strictly inside by
(15). For the opposite vertex put
\[
             L=\cos\beta+\sin\beta,\qquad
             K=\cos\beta-\sin\beta>0.
\]
Direct expansion using (10) gives its exact squared-radius deficit:
\[
\begin{split}
 D&:=R^2-|P_N-O+j+Jj|^2\\
  &=2h+(2hs-2-c)(1+L)+(2hc+s)K.
\end{split}
\tag{18}
\]
It strictly increases with h, since its h derivative is
2[1+s(1+L)+cK]>0. Replace h by9/10 for a lower bound. At
that value it decreases with beta: L'=K, K'=-L, and
(9/5)s-2-c<0. By (17), its lower endpoint comparison is at
beta=psi/2. There
\[
 L_0=\sqrt{1+s}>\frac{11}{8},\qquad
 K_0=\sqrt{1-s}<\frac13,\qquad c=L_0K_0,
\]
and (18) simplifies exactly to
\[
 D>(1+L_0)\left(\frac95L_0-2-K_0\right)
       >(1+L_0)\left(\frac{99}{40}-\frac73\right)
       =(1+L_0)\frac{17}{120}>0.
\tag{19}
\]
This puts the last N vertex strictly inside as well. Hence no tilted
N can carry its required positive circle load.

## 4. Parallel N, including every actual bottom-side mean

It remains that N is parallel to U. Both P_N and V lie on its
bottom side y=1. Put ell=V_x-xi>0. Its lower-left corner is
P_N-rho e_x with
\[
                          0\le\rho\le1-\ell.
\tag{20}
\]
This interval keeps every actual U mean and HN point, including
their side-interior and endpoint limits.

The zero second coordinate of (11), together with t<=1, gives
a+b>=1+c. Therefore
\[
 (a-b)^2=2-(a+b)^2\le1-2c-c^2.
\]
Put W=sqrt(1-2c-c^2), which is real by (9). Then
\[
              \ell=s+a-tb\ge s+a-b\ge s-W.
\tag{21}
\]
All four N corner horizontal coordinates relative to O have absolute
value at most
\[
                Z=1+hc-\frac s2+W.
\tag{22}
\]
Indeed the left magnitude is A+rho<=A+1-ell<=Z. The other
possible magnitude is at most1-A, and Z-(1-A)=2hc+W>=0.
All vertical corner magnitudes are at most
\[
                          Y_*=2-hs+\frac c2>0,
\tag{23}
\]
because B_0>-1/2 by (7). Thus every N corner has squared norm
at most Z^2+Y_*^2.

For fixed c,s, half the derivative of this bound with respect to h is
\[
                 cZ-sY_*=h+c(1+W-s)-2s<0.
\tag{24}
\]
For example (7),(9), W<=1 give the strict upper bound
51/50+(5/12)(11/10)-9/5=-193/600. It suffices to bound
Z^2+Y_*^2 at h=9/10.

If 0<=c<=1/4, use
\[
 W\le1-c-c^2,\qquad s\ge1-c^2,
 \qquad s\ge\sqrt{15}/4>121/125.
\]
The first inequality follows by squaring its nonnegative right
side: the difference is 2c^3+c^4. Equations(22)--(23) now give
\[
                    Z\le\frac32,
                    \qquad Y_*<\frac{6269}{5000}.
\]
Hence
\[
 R_0^2-Z^2-Y_*^2>
 R_0^2-\frac94-\left(\frac{6269}{5000}\right)^2
                         =\frac{122829}{1562500}>0.
\tag{25}
\]

If 1/4<=c<=sqrt(2)-1, Z at h=9/10 decreases with c. In
the open interval where W>0,
\[
 Z'=\frac9{10}+\frac{c}{2s}-\frac{1+c}{W}<0:
\]
the first two terms are less than6/5, while
(1+c)/W>=5/sqrt(7)>5/3. Continuity includes the endpoint W=0.
The rational comparisons sqrt(15)>484/125 and
sqrt(7)<1323/500 consequently give
\[
 Z\le Z(1/4)=1+\frac9{40}-\frac{\sqrt{15}}8+\frac{\sqrt7}4
                                    <\frac{561}{400}.
\]
Also (9) gives
\[
                    Y_*<2-\frac9{10}\frac{91}{100}
                                  +\frac{29}{140}
                           =\frac{9717}{7000}.
\]
Thus throughout this second complete interval,
\[
 R_0^2-Z^2-Y_*^2>
 R_0^2-\left(\frac{561}{400}\right)^2
       -\left(\frac{9717}{7000}\right)^2
                         =\frac{1308919}{196000000}>0.
\tag{26}
\]
Both (25) and (26) imply every N corner is strictly inside D_R,
since R>=R_0. They cover the entire parallel frame and every mean
in (20), not merely its midpoint or a symmetric placement.

## 5. The entire genuinely free HB family has the same contradiction

Suppose instead HB uses a genuine free point normal. Its physical
application is L on H. At B, the positive vertical and nonnegative
horizontal normal has negative scalar product with w. Its rightward
application cannot be P_B, so its scalar product with k is positive.
Thus the actual B vertex is again
\[
                         Q_B=L=P_B+k.
\tag{27}
\]
The complete physical radial argument in Section1 still gives (7)--(10):
the radial axis k would make this shared vertex a circle point, so the
radial axis is w. Now e=a-c and e>=1-b give exactly the same bound
c<=a+b-1 used in (9).

The actual HN point can be H-owned or not. Retain its entire side:
\[
                     Q_N=P+\sigma u,\qquad0<\sigma\le1.
\tag{28}
\]
Indeed all HN applications are on PV, and its height at least1 makes
sigma positive. Substitution of (27) gives the actual N chord
\[
 q=Q_N-P_N=(s-b+\sigma a,\ a-c+\sigma b-1).
\tag{29}
\]
In particular
\[
       q-(s,-1-c)=(-b+\sigma a,a+\sigma b),
                    \qquad |q-(s,-1-c)|^2=1+\sigma^2\le2.
\tag{30}
\]
Its first coordinate is positive and its second nonnegative. The
entire Section2 bound depends only on (9)--(10), so it is unchanged.
For tilted N, its actual rightward incident side contains Q_N, and
(30) gives precisely the same beta<psi/2 bound as (17). Every step
of Section3 consequently applies to the actual point Q_N.

For parallel N, write ell=Q_N,x-xi and keep the same full mean
interval (20). The zero second coordinate in (29) gives
sigma=(1+c-a)/b. Hence
\[
                 \ell=s+\frac{a(1+c)-1}{\sqrt{1-a^2}}.
\tag{31}
\]
The second term strictly increases with a: its derivative is
(1+c-a)/(1-a^2)^(3/2)>0. The condition a+b>=1+c is equivalent to
\[
 \frac{1+c-W}{2}\le a\le\frac{1+c+W}{2},
                 \qquad W=\sqrt{1-2c-c^2}.
\tag{32}
\]
At its lower endpoint b=(1+c+W)/2 and sigma=1, so (31) gives
ell=s-W. Thus the full domain satisfies ell>=s-W, exactly (21).
All corner bounds (22)--(26) now apply without changing the actual
UN mean or the HN application. Every N corner is strictly inside
D_R, contradicting its positive load. This excludes every genuine
free HB normal directly, without an additional normal-selection rule.

## 6. Whole implication and remaining end-triple families

Sections3--5 exhaust every physical N mask for both the H-owned and
genuinely free HB alternatives of a tilted radial B. In either case
they contradict N's positive circle load. The actual HB normal of
such a B must therefore be B-owned. The singleton and strict endpoint
conventions make its application a point strictly inside B's side;
no vertex/vertex axis endpoint is silently included.

The end-triple still retains tilted radial B with its HB normal owned
by B, and B parallel to U with either physical circle mask and all
actual U means. These remaining families are not declared closed here.
N's degree-three force was never replaced by a degree-two equation,
T's full physical mask and roof means remained, and all four extra
squares stayed in place. No numerical scan, new normal convention,
secondary minimizer, Lean compilation or CI is a premise of this theorem.
