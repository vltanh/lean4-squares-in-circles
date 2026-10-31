# Two opposite radial-incident ports with a nonshared return channel are impossible

Date: October 26, 2026.

**Status: complete analytic physical-subfamily proof, accepted after root
and separate independent saved-source and physical-scope reviews.** See
REVIEW_C6_RADIAL_OPPOSITE_AND_DOUBLE_SHARED_ROOT_2026_10_26.md and
REVIEW_C6_RADIAL_TWO_OPPOSITE_NONSHARED_CERTIFICATE_REDUCTION_2026_10_26.md.
No angle grid or coefficient packet is
introduced.

Work in the original radius window

\[
 K_0:=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\frac14}-1.
\tag{1}
\]

The positive component is the original alternating all-side C6, with
one physical two-circle-corner loaded square S, two physical-unique
loaded squares B,C, and three actual unloaded degree-two transmitters.
Keep both radial corner weights, the original normals, all means and
sliders, and every additional physical square.

The additional hypotheses are:

* both unique turns are strictly greater than \(\pi/2\);
* both S-incident applications on B,C are their actual vertices
  opposite their unique circle corners;
* the B-to-C transmitter is not genuinely shared at either end.

**Theorem.** This entire six-body core is impossible.

The unconditional upper-turn theorem gives \(\theta_S\ge\pi/2\).
The equality case is already classified by
[SIX_CYCLE_ONE_RADIAL_RIGHT_TURN_CLASSIFICATION.md](SIX_CYCLE_ONE_RADIAL_RIGHT_TURN_CLASSIFICATION.md);
both its S-incident unique applications are adjacent vertices, contrary
to the present physical hypothesis. Thus all three actual turns are
strictly greater than \(\pi/2\) in the only branch requiring proof.

## 1. The original opposite-port chart

The complete local strict-turn feature cover puts the two applications
at each unique load on one inner side. Since its S-incident application
is the opposite vertex and its other interface is not shared, its
B-to-C application is the adjacent-to-circle vertex. Both of these
interfaces have strict loaded-vertex normals.

Normalize the actual B-to-C channel horizontally, with its outward
side above the origin:

\[
                   T_B=(l,H),\qquad T_C=(l+1,H),\qquad H>0.
\tag{2}
\]

The positive height comes from the actual force-polygon theorem and
common moment. At the left endpoint the two own circle axes can be
written

\[
 v=(-c,s),\qquad u=(s,c),\qquad
 c=\cos\eta>0,\quad s=\sin\eta>0.
\tag{3}
\]

The inward directions at the adjacent port are v and \(-u\);
their strict negative horizontal components follow from the actual
strict rightward normal.

We first fix the circle-corner sign without choosing a square-root
branch. In these own axes write \(z=av+bu\), with
\(a,b>1/2\), and put \(Z=z_y=H+s\), \(t=s/Z\).
The actual concurrence is \(q=(1-t)z\); its height is H.
The opposite port is \(Q=z-v-u\), of height \(H-c\).
Thus \(V=q-Q=Xv+Yu\), where \(X=1-ta,\ Y=1-tb\),
is nonzero and points in the actual strict inward vertex normal
direction. Properness and that strict feature give \(X,Y>0\).
Writing \(L=|V|>0\), the unchanged common moment has the sign of
\(\det(q,(1,0))=-H<0\), so
\[
             \det(q,V/L)=-\frac{(1-t)(a-b)}L<0.
\]
Hence \(a>b\) and \(X<Y\). The strict unique turn gives
\((V/L)_x<0\), or \(cX>sY\); therefore \(c>s\).
It follows that \(z_x=-ca+sb<0\). We may now define the
positive square-root branch without circularity:

\[
 Z=H+s,\quad A=\sqrt{R^2-Z^2}>0,\quad
 z=(-A,Z),\quad T=z-v=(-A+c,H).
\tag{4}
\]

The negative circle-corner sign in (4) was established before this
definition. The original S-incident opposite vertex is

\[
                     Q=z-v-u=(-A+c-s,H-c).
\tag{5}
\]

Put

\[
 a=cA+sZ,\quad b=cZ-sA,\quad
 t=\frac{s}{Z}\in(0,1),\quad
                    q=(1-t)z.
\tag{6}
\]

Here \(a,b>1/2\) are the actual unique circle-corner coordinates,
\(a^2+b^2=R^2\), and q is the original proper radial concurrence.
The actual incoming direction from S is

\[
 V=q-Q=(tA+s-c,c)=Xv+Yu,\qquad
 X=1-ta,\quad Y=1-tb,\quad L=|V|,\quad G=V/L.
\tag{7}
\]

The complete properness identities are

\[
 X=\frac{cb}{Z}>0,\qquad
 0<\frac{sb}{Z}<sc\le\frac12,\qquad
 Y=1-\frac{sb}{Z}>0.
\tag{8}
\]

For the middle inequality, use \(b/Z=c-sA/Z<c\).
In particular \(L>0\). The actual reserve-one transmitter fixes
the corresponding original radial port as

\[
                              P=Q-G.
\tag{9}
\]

No transverse slider or application mean has been replaced.

There are two useful strict signs in this chart. The triangle's
interior angle at B is less than \(\pi/2\), so
\((-G)\cdot(1,0)>0\), or \(G_x<0\). Equation (7) then gives
\(c>s\), and hence

\[
                            0<\eta<\frac\pi4.
\tag{10}
\]

Further, \(\det(q,(1,0))=-H<0\), and the unchanged common
moment has the same sign on the incoming channel. As
\(\det(v,u)=-1\),

\[
       \det(q,G)=-\frac{(1-t)(a-b)}L<0.
\]
Consequently
\[
                              a>b>\frac12.
\tag{11}
\]

The reflected right endpoint has the identical chart with its own
angle. Its actual radial port has the same squared norm

\[
                       |P|^2=r_0^2:=d^2+\frac14
                                =R^2-2d-1.
\tag{12}
\]

The actual B-to-C reserve is

\[
                         A_B+A_C=1+c_B+c_C.
\tag{13}
\]

## 2. A norm root must have \(A>c\)

This is a local statement about any actual endpoint (4)--(12).
Write

\[
                 h=a+b,\qquad \delta=a-b>0,\qquad C=c+s.
\]

Suppose \(A\le c\). Since \(A=ca-sb\) and \(s\le c\),

\[
 a\le1+(s/c)b\le1+b,\qquad
 \delta\le1,\qquad h\ge\sqrt{2R^2-1}.
\tag{14}
\]

The coordinates of G in the v,u basis are \(X/L,Y/L\).
Because \(a>b\) and \(t>0\), \(X<Y\). The strict sign \(G_x<0\)
means \(X/Y>s/c\). Thus for some
\(\eta<\phi<\pi/4\),

\[
                         G=\sin\phi\,v+\cos\phi\,u.
\tag{15}
\]

The linear functional
\((a-1)\sin\phi+(b-1)\cos\phi=Q\cdot G\)
has its minimum on this closed angle interval at an endpoint.
For \(b\le1\) it is strictly increasing, because \(a>R/\sqrt2>1\).
For \(b\ge1\) it is concave, since its second derivative is its
negative and the function is nonnegative. Therefore

\[
             Q\cdot G\ge
                  \min\left\{Z-C,\frac{h-2}{\sqrt2}\right\}.
\tag{16}
\]

We next prove both alternatives in
\[
                         h+Q\cdot G>2+d.
\tag{17}
\]

First, the assumption \(A\le c\) gives \(Z^2\ge R^2-c^2\).
For every \(c^2+s^2=1\),

\[
 c^2+2cs<\frac{13}{8},
\tag{18}
\]

as follows from
\[
 \frac{13}{8}-(c^2+2cs)
 =\frac18\left[
       5\left(c-\frac85s\right)^2+\frac15s^2\right]>0.
\]
Also \(C\le\sqrt2<10/7\). Hence

\[
 \begin{split}
 c^2+(C+3/8)^2
 &=1+c^2+2cs+\frac34C+\frac9{64}\\
 &<1+\frac{13}{8}+\frac{15}{14}+\frac9{64}
 <K_0^2.
 \end{split}
\tag{19}
\]

The final exact reserve is \(89/1400>0\). Thus \(Z-C>3/8\).
Since \(R^2=(d+1)^2+1/4\) and \(d>9/10\),

\[
 (2R^2-1)-(d+13/8)^2
       =d^2+\frac34d-\frac{73}{64}
       >\frac{551}{1600}>0.
\tag{20}
\]

Equations (14), (19), and (20) give \(h+Z-C>2+d\).

For the second alternative, the comparison
\[
                         h>2+(2-\sqrt2)d
\tag{21}
\]
implies \(h+(h-2)/\sqrt2>2+d\). It follows directly from (14):
\[
 \begin{split}
 (2R^2-1)-\{2+(2-\sqrt2)d\}^2
 &=4(\sqrt2-1)(d^2+d)-\frac52\\
 &>\frac{59}{250}>0,
 \end{split}
\tag{22}
\]
where \(d>9/10\) and \(\sqrt2>7/5\) give the displayed rational
reserve. Both squared quantities in (20) and (22) are positive,
so the square comparisons have the stated direction.

Thus (17) holds. But \(Q=z-v-u\) and \(|G|=1\) give

\[
 |P|^2=|Q-G|^2=R^2+3-2h-2Q\cdot G
                <R^2-2d-1=r_0^2,
\tag{23}
\]

contradicting the actual norm equation (12). We have proved

\[
                                A>c
\tag{24}
\]

at every original opposite-port root in this family.

## 3. One whole-interval norm monotonicity forces symmetry

Fix the actual R,H and interpolate \(\eta\) only between its two
actual endpoint values. No interpolated packing is asserted.
The scalar domain is connected for the following exact reasons.

The function \(s\) increases, so \(0<Z=H+s<R\) persists between
the actual endpoints. Moreover

\[
 b=cZ-sA>0
 \quad\Longleftrightarrow\quad
 Z>sR
 \quad\Longleftrightarrow\quad
                        H>s(R-1).
\tag{25}
\]

The squaring in the first equivalence has positive sides. The
last inequality persists from the larger endpoint angle. Therefore
b remains positive on the entire interval, and

\[
              (A-c)'=-b/A<0.
\tag{26}
\]

The actual larger endpoint obeys (24); hence \(A>c\) throughout.
Direct differentiation gives

\[
 a'=b(1-c/A)>0,\qquad
 b'=-a(1-c/A)<0,\qquad
 t'=\frac{Hc}{Z^2}>0.
\tag{27}
\]

Thus \(\delta=a-b\) increases and remains positive from its
actual smaller endpoint. The positivity of X,Y,L in (8) persists
by the same identities. All derivative denominators are positive.

Define the original reconstructed norm function
\[
                              F_O(\eta)=|P|^2.
\]
With
\[
 L^2=2-2th+t^2R^2,\qquad
 J=(1+t)h-tR^2-2,
\]
the exact formula is
\[
                       F_O=R^2+3-2h-\frac{2J}{L}.
\tag{28}
\]

Its derivative is

\[
 F_O'=\frac{2\delta}{L^3}
      \left[(1-c/A)\mathcal C
                      +t'(1-t)\delta\right]>0,
\tag{29}
\]
where
\[
 \mathcal C=L^3+tL^2+(1-t)(2-th)>0.
\tag{30}
\]

For a direct verification, treating h,t as independent gives
\[
 \partial_h F_O
  =-\frac2{L^3}
       \{L^3+2-t(1+t)h+t^3R^2\},
\]
\[
 \partial_t F_O
  =\frac{2(1-t)(2R^2-h^2)}{L^3}
  =\frac{2(1-t)\delta^2}{L^3}.
\]
The first brace equals (30), and \(h'=-\delta(1-c/A)\);
this proves (29). Positivity in (30) uses
\(2-th=X+Y>0\), and every factor in (29) is positive by
(24)--(27).

Both actual endpoints have norm \(r_0^2\). Strict monotonicity
on their whole interval therefore forces

\[
                              \eta_B=\eta_C.
\tag{31}
\]

## 4. The original radial chord fixes a single scalar family

Write the common parameters without endpoint subscripts.
Equation (13) gives

\[
                              A=c+\frac12.
\tag{32}
\]

Set \(k=c-s-tA>0\), so \(V=(-k,c)\). The original radial
ports are reflected:

\[
 P_B=(-x,y),\quad P_C=(x,y),\qquad
 x=\frac12+s-\frac{k}{L},\quad
 y=H-c-\frac cL.
\tag{33}
\]

Since \(k/L<1\) and \(s>0\), \(x>-1/2\). Their actual
radial inner side has length one, so \(2|x|=1\); necessarily
\(x=1/2\). Hence

\[
 \frac{k}{L}=s,\qquad \frac cL=c,\qquad
                L=1,\quad k=s,\quad tA=c-2s>0.
\tag{34}
\]

The equality \(c/L=c\) follows from the first equality and the
positive unit-normal coordinates. In particular, with

\[
                     u_0=s/c,\qquad 0<u_0<1/2,
\tag{35}
\]
we have
\[
                         Z=\frac{u_0A}{1-2u_0}.
\tag{36}
\]

The actual S-outward normals in (34) are \((-s,c)\) and \((s,c)\).
Their positive vertical components place S below its horizontal
inner side. Its unchanged physical radial mask therefore gives
\(y=-d\). Equations (33)--(34) imply

\[
                         H=2c-d,\qquad Z=2c+s-d.
\tag{37}
\]

This uses the actual square and its two physical circle corners;
it does not assume that the radial concurrence lies in the disk.

## 5. The circle equation lies below the original radius window

Put
\[
 c=\frac1{\sqrt{1+u_0^2}},\quad
 A=\frac12+c,\quad M=1+c(2+u_0).
\tag{38}
\]
Then \(d+1=M-Z\). The common original circle equation is
\[
 A^2+Z^2=(d+1)^2+\frac14=(M-Z)^2+\frac14.
\]
Using (36), it becomes
\[
       (1-2u_0)(A^2-M^2-\tfrac14)+2u_0MA=0.
\tag{39}
\]

Multiplication by \(1+u_0^2>0\) and the exact square relation
for \(\sqrt{1+u_0^2}\) reduce (39) to

\[
 E(u_0):=-4+9u_0+8u_0^2+5u_0^3
       +\sqrt{1+u_0^2}\,(-3+8u_0+5u_0^2)=0.
\tag{40}
\]

Let \(U=9/28\). The two polynomial factors
\[
 P(u)=-4+9u+8u^2+5u^3,\qquad Q(u)=-3+8u+5u^2
\]
are strictly increasing for \(u\ge0\). At U,
\[
 P(U)=-\frac{2515}{21952}<0,\qquad
 Q(U)=\frac{69}{784}>0,
\]
\[
 E(U)=\frac{-2515+69\sqrt{865}}{21952}<0.
\tag{41}
\]
The last sign is an exact positive-square comparison:
\[
                     2515^2-69^2\cdot865=2206960>0.
\]

For \(0\le u\le U\), if \(Q(u)\le0\), then
\(E(u)\le P(u)\le P(U)<0\). If \(Q(u)>0\), the increasing
polynomials and square root give \(E(u)\le E(U)<0\).
Thus every root in (35) satisfies
\[
                                u_0>U.
\tag{42}
\]

On the other hand, (36)--(38) give the exact radial coordinate
\[
 d(u)=\frac{1}{\sqrt{1+u^2}}
       \left(2+u-\frac{u}{1-2u}\right)
                   -\frac{u}{2(1-2u)}.
\tag{43}
\]

The first bracket decreases strictly on \(0<u<1/2\), since
its derivative is \(1-(1-2u)^{-2}<0\). The last positive
fraction increases. If the bracket is nonpositive, then \(d(u)<0\),
already impossible. Otherwise its positivity holds on the interval
from U to the actual \(u_0\), so the product of its two positive
decreasing factors decreases strictly. Equation (42) consequently
gives
\[
 d=d(u_0)<d(U)
             =\frac{199}{5\sqrt{865}}-\frac9{20}
             <\frac{91}{100}.
\tag{44}
\]

The final exact square comparison is
\[
 \left(\frac{34}{25}\right)^2
       -\frac{199^2}{25\cdot865}
                       =\frac{1983}{108125}>0.
\]

But the original lower radius bound gives the opposite strict
inequality:
\[
 d>\frac{91}{100},\qquad
 K_0^2-\frac14-\left(\frac{191}{100}\right)^2
                        =\frac{101}{40000}>0.
\tag{45}
\]

This contradiction excludes the whole stated original feature family.

## 6. Scope

The proof excludes two actual opposite S-incident vertices when the
B-to-C transmitter has no genuine shared endpoint and both unique
turns are strict. It preserves every original radial weight and
all actual transmitter sliders. The three additional squares are
retained; the contradiction already occurs in the physical core.

If the B-to-C transmitter owns a unique loaded side, its actual
application is a variable mean and its chart differs from (4).
Those one-owner and two-owner alternatives have not been frozen to
the adjacent endpoint and are not excluded by this source. Cases
with one unique turn at most \(\pi/2\) also remain separate.
No unrestricted one-radial gate, coarse graph family, or global
nine-square theorem is declared closed here. No Lean compilation,
CI, sampled pose, or interval-sign certificate is used.
