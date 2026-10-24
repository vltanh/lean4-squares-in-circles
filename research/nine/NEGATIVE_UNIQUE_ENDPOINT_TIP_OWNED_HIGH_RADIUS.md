# A negative unique boundary endpoint cannot own its root contact at high radius

**Status: complete whole-owner hand theorem; root and separate independent
full hand audits passed.** Work throughout
\[
             \frac{\sqrt{17}}2\le R\le\frac{\sqrt{1105}}{16},
             \qquad q=R^2,\qquad \sigma=\frac1{\sqrt2}.
\tag{1}
\]
Let H,A,B be actual contained interior-disjoint unit squares. The
positive edges HA and AB are the two and only two positive pair edges
at A. A has one physical circle corner z with positive weight; B
physically touches the circle. H and B may retain arbitrary other
positive forces. Assume
\[
                              c_H\cdot z<0.
\tag{2}
\]
Every other physical packing square remains.

**Theorem.** The actual HA normal cannot be a side axis of A. This
includes every genuine shared HA interval and every original
application mean, including its endpoints. No physical HB contact,
triangle, root degree, root-axis resultant or secondary minimizer
is assumed.

The missing HB contact is material: the corresponding all-radius
triangle theorem uses it to force a sign. The present theorem handles
the additional whole sign alternative over the complete high-radius
domain (1).

## 1. Actual concurrence and a transverse coordinate bound

NEGATIVE_UNIQUE_NEIGHBOR_INNER_CONTACT.md puts the entire H/A
intersection on A's inner faces. Choose an orthonormal A frame about
the unchanged circle origin so that the owned HA face is horizontal:
\[
 \begin{split}
 z&=(a,b),\qquad a,b>3/5,\qquad a^2+b^2=q,\\
 A&=[a-1,a]\times[b-1,b],\qquad n_{HA}=e_y.
 \end{split}
\tag{3}
\]
No ordering of a,b is imposed. Write g for the actual outward A-to-B
normal. The true A force equation is
\[
                  k(a,b)=\mu e_y-\gamma g,\qquad k,\mu,\gamma>0.
\tag{4}
\]
Its first component gives \(g_x<0\), so the pair forces at A are
nonparallel. The complete nonparallel proper-concurrence lemma in
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma2.1, applies to this
actual degree-two endpoint with its boundary neighbor B. It gives
\[
       q_A=\kappa z\in A,\qquad \kappa>0,\qquad
       Q=(\kappa a,b-1)\in H\cap A,
\tag{5}
\]
where Q is the unchanged actual HA point or shared-side mean.

The circumradius of H and (2) imply
\[
                  \kappa a^2+b^2-b=Q\cdot z<\sigma R.
\tag{6}
\]
The following complete scalar consequence is useful:
\[
                 0<\beta:=\kappa b<2/3,\qquad
                       b<5/3,\qquad 1<a<2.
\tag{7}
\]
Here is the full argument, whose scope needs no HB contact.
If beta>=2/3, multiplying (6) by3b would give
\[
              f(R,b):=2R^2-5b^2+3b^3-3\sigma Rb<0.
\]
For fixed \(0<b\le R<21/10\), comparison from \(R_0=79/40\)
to the actual R gives
\[
 f_R=4R-3\sigma b>79/10-9/2=17/5>0,
\]
using \(\sigma<5/7\). Also
\(2R_0^2>39/5\) and \(\sigma R_0<7/5\). Thus
\[
 f(R,b)>
 \frac15(15b^3-25b^2-21b+39)>0.
\]
For the last strict sign, put \(x=b-3/2\) and use the exact identity
\[
 \begin{split}
 15b^3-25b^2-21b+39
   &=(15b+20)x^2+\frac{21}{4}x+\frac{15}{8}\\
   &\ge20\left(x+\frac{21}{160}\right)^2
                              +\frac{1959}{1280}>0.
 \end{split}
\tag{8}
\]
This contradiction proves beta<2/3. Because \(q_A\in A\),
beta>=b-1, giving b<5/3. Finally \(q>34/9\) gives a>1,
and \(b>3/5,\ q\le1105/256\) give a<2. Every mean endpoint
is retained.

## 2. The complete nonpositive vertical-normal alternatives

First suppose \(g_y=0\). Then \(g=-e_x\) and its actual application
on A is
\[
                              T=(a-1,\beta).
\]
B lies to the left of this actual right support point. For any unit
square K with right support point \((X,Y)\), \(X,Y>0\), its corners
satisfy the orientation-uniform bound
\[
       \max_{v\text{ corner of }K}|v|^2
       \le\max\{X^2,(X-1)^2\}+(Y+1)^2.
\tag{9}
\]
At a side support this is the aligned interval bound. At a vertex
support the inward axes are \((-c,s),(-s,-c)\), with c,s>=0 unit.
The adjacent corners have norm squared at most \(X^2+(Y+1)^2\).
For the opposite corner use
\[
               -X(c+s)+Y(s-c)\le Y-X.
\]
If Y>=X this follows from
\((Y-X)s-(X+Y)c\le Y-X\). If Y<X, write the same expression
as \((Y-X)(c+s)-2Yc\) and use c+s>=1. This proves (9)
for all support features and aligned endpoints.

By (7), \(0<a-1<1,\ 0<\beta<2/3\). Therefore (9) makes
every B corner have squared norm less than
\[
                             1+(5/3)^2=34/9<q.
\]
B would be circle-clear, a contradiction.

If instead \(g_y<0\), its strict inner-vertex cone puts its actual
application at \(P=(a-1,b-1)\). Write the untouched HA mean as
\(Q=P+s e_x,\ 0\le s\le1\). Actual torque at A gives
\[
                               k(b-a)=\mu s\ge0.
\tag{10}
\]
This keeps s=0, including the radial-D coincidence. Since b>=a
and b<5/3, monotonicity along the circle gives
\[
       a+b>\sqrt{q-25/9}+5/3>1+\sqrt{q-1}.
\tag{11}
\]
For the second inequality, \(q>34/9\) implies
\[
 \sqrt{q-1}-\sqrt{q-25/9}
   =\frac{16/9}{\sqrt{q-1}+\sqrt{q-25/9}}<2/3.
\]
But the universal actual boundary-contact radius theorem,
C7_PINNED_VERTEX_CONTACT_TYPES.md, Section3, applies to A and B
without a C7 premise and gives
\[
             |P|\ge\sqrt{q-1}-1.
\]
Since \(|P|^2=q+2-2(a+b)\), its squared form contradicts (11).
Thus both whole alternatives \(g_y\le0\) are excluded.

## 3. The full upward-normal geometry and the sharp support cap

It remains that \(g_x<0,\ g_y>0\). The actual A/B contact is
then exactly A's upper-left vertex
\[
                              T=(a-1,b).
\]
The proper relation \(T-q_A=\lambda g\) has \(\lambda>0\);
equality would require both \(\kappa=1\) and \(\kappa a=a-1\).
Put
\[
                   \delta=1-\kappa,\qquad
                   t=-g_x/g_y=\frac{1-\delta a}{\delta b}>0.
\tag{12}
\]
The sign \(g_y>0\) gives delta>0, and \(g_x<0\) gives
delta<1/a. The actual outward support of A in direction g is
\[
                          h=\frac{b-(a-1)t}{\sqrt{1+t^2}}.
\tag{13}
\]

A contained unit beyond a supporting line has minimum support at most
\[
                         d=\sqrt{R^2-1/4}-1<61/60.
\tag{14}
\]
Indeed every unit center has norm at most \(d+1/2\), while its
projection in that direction is at least its minimum support plus
1/2. This is the full sharp center/support bound in
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section1.
Consequently the actual B requires h<=d. We contradict this
over both complete coordinate orders below.

## 4. The entire coordinate order a>=b

The actual H lies below \(y=b-1\), and Q is a point on its top
support. For a>=b>0 this geometry strengthens (6) to
\[
                              Q\cdot z<(a+b)/2.
\tag{15}
\]
To see this, if the top support is a side, the relative coordinates
of Q from c_H have y=1/2 and x<=1/2, giving
\((Q-c_H)\cdot z\le(a+b)/2\).
Otherwise Q is the top vertex; write H's two inward axes as
\((c,-e),(-e,-c)\), with c,e>=0 and c²+e²=1. Then
\[
 (Q-c_H)\cdot z
       =\tfrac12\{(b-a)c+(a+b)e\}\le(a+b)/2.
\]
Combining either case with (2) proves (15), for every actual mean.

Put
\[
                         S=a+b,\qquad T_0=3S-2q.
\]
Equations (12),(15) give
\[
 0<T_0,\qquad
 \delta>\frac{2q-a-3b}{2a^2}
         =\frac{2a-T_0}{2a^2}.
\tag{16}
\]
In particular S>2q/3. On the full radius interval (1),
\[
 (a-b)^2=2q-S^2
       <2q-\frac{4q^2}{9}\le\frac{17}{36}<\frac{49}{100}.
\]
The comparison function decreases for q>=17/4. Hence
\[
         b>\frac{16}{15},\qquad
         \frac{29}{20}<a<\frac95,\qquad b<\frac32.
\tag{17}
\]
The lower b bound follows from
\(S>17/6,\ a-b<7/10\).
The lower a bound follows from \(a\ge R/\sqrt2\).
For the upper a bound use
\(a^2<1105/256-(16/15)^2<81/25\).

The function \(3\sqrt{2q}-2q\) decreases for q>=17/4, so
\[
 T_0\le3\sqrt{2q}-2q
       \le3\sqrt{17/2}-17/2<1/4.
\tag{18}
\]
The last strict comparison is exactly1224<1225 after squaring.
In particular \(2a-T_0>0\). The ratio in (12) strictly decreases
with delta. Therefore (16)--(18) give
\[
 \begin{split}
 t&<\frac{aT_0}{b(2a-T_0)},\\
 \frac{t}{T_0}
   &<\frac1{(16/15)(2-5/29)}
      =\frac{435}{848}<\frac{13}{25}.
 \end{split}
\tag{19}
\]

Let theta=arctan(t). Use
\(\sin\theta\le t\) and \(1-\cos\theta\le t^2/2\).
The entire support loss in (13) satisfies
\[
 \begin{split}
 b-h
   &=b(1-\cos\theta)+(a-1)\sin\theta\\
   &<\frac34\frac{169}{625}T_0^2
          +\frac45\frac{13}{25}T_0\\
   &<\frac{4667}{10000}T_0<\frac12T_0.
 \end{split}
\tag{20}
\]
Thus
\[
                     h>b-\frac12T_0
                         =q-\frac{3a+b}{2}.
\tag{21}
\]

For completeness this last lower bound has a whole-domain minimum.
Fix q and let b_0 be the smaller circle coordinate at
\(a_0+b_0=2q/3\):
\[
 b_0=\frac q3-\frac12\sqrt{2q-\frac{4q^2}{9}}>\frac{16}{15}.
\tag{22}
\]
It exists because q<9/2. The same estimates as (17) hold for
b_0<=b<=sqrt(q/2). On this entire interval,
\[
 \frac{d}{db}\left(q-\frac{3\sqrt{q-b^2}+b}{2}\right)
        =\frac12\left(\frac{3b}{a}-1\right)>0,
\]
since \(b\ge b_0>16/15,\ a<9/5\).
At b=b_0 the expression equals b_0. Equation (21) consequently
gives
\[
                              h>b_0>16/15>61/60.
\tag{23}
\]
This contradicts the necessary cap (14).

## 5. The entire coordinate order b>=a

Now (7) and (1) imply
\[
       \frac{29}{20}<b<\frac53,\qquad
                       \frac65<a<\frac32.
\tag{24}
\]
Here b>=R/sqrt(2)>29/20 and a<=R/sqrt(2)<3/2.
Also \(a^2>17/4-25/9=53/36>36/25\).

Since \(\beta=\kappa b<2/3\),
\(\delta>1-2/(3b)\). Equation (12) yields
\[
 \begin{split}
 t&<\frac{3b/(3b-2)-a}{b}\\
  &<\frac{87/47-6/5}{29/20}
       =\frac{612}{1363}<\frac9{20}.
 \end{split}
\tag{25}
\]
The comparison numerator is positive, and \(3b/(3b-2)\)
decreases throughout the actual b interval. All replacements in
(25) therefore have the displayed inequality direction.

Equations (13),(24),(25) now give
\[
 h>\frac{29/20-(1/2)(9/20)}{\sqrt{1+(9/20)^2}}
    =\frac{49}{2\sqrt{481}}
    >\frac{49}{44}>\frac{61}{60},
\tag{26}
\]
because481<484. This again contradicts (14). The common
a=b endpoint is included in either complete argument.

## 6. Full physical scope and the ABC application

The true A equation forces \(g_x<0\). Sections2--5 exhaust
\(g_y<0,\ g_y=0,\ g_y>0\), with both entire coordinate orders
in the last case. No B frame or side owner was specified, and every
B physical circle mask and zero individual corner weight remains.
All actual shared HA means survive the exact coordinate Q in (5).
H and B keep all their original other forces.

In the triangle-attached C4 load orbit ABC, the actual boundary
path and intact-petal pressure supply a negative unique endpoint A.
On the complete \(R^2\ge17/4\) domain this theorem removes every
A-owned HA and every genuinely shared HA. A surviving negative
endpoint contact is H-owned singleton, or free with an actual
shared AB side: if AB were a singleton, the existing fixed-tip
normal selection would remove the free HA. The other endpoint,
middle load, intact H-X-Y petal and all three extras remain.

The proof does not assume HB, does not change H's true degree four
or B's true degree two in that application, and does not classify
the remaining full ABC orbit. The lower-radius A-owned/shared
domain remains open; it is not an endpoint limit of this theorem.
No sampled sign, parameter subdivision, Lean compilation or CI
is a premise.
