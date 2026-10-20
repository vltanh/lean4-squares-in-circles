# The three zero sources cannot all be nonpositive

## 1. Scope and the captured domain

Work on the original G0--G2 boundary cycle at
\(Q=9789/2500\), with the established normalization \(y_E\le0\).
Then
\[
                         \max(y_H,y_A,y_T)>0.          \tag{1}
\]
There is no additional owner, radial-kind, frame-order or mismatch
hypothesis in (1).

Suppose otherwise. The
[global radial and angle capture](HAND_G3_ALL_NONPOSITIVE_ZERO_SOURCES_ARE_OUTER.md)
proves that all seven states are outer, all signed tangents are
nonpositive, every zero owner is 2, and every quarter owner is 2 or 3.
Put
\[
 l=\frac{21}{200},\qquad P=\frac{13}{25},\qquad
 e=\frac{18}{25},\qquad
 R=\sqrt Q,\quad c=\sqrt{Q/2}-\frac12,
 \quad a_0=\sqrt{Q-\frac14}-\frac12.
\]
The three zero errors exceed l, and the total positive variation p
satisfies
\[
                         3l<p<P.                     \tag{2}
\]
Each zero error is less than \(P-2l=31/100\). Write every state
as \((a,-b)\), where
\[
 (a+\tfrac12)^2+(b+\tfrac12)^2=Q,
 \qquad 0\le b\le c\le a\le a_0.
                                                               \tag{3}
\]
The additional L/H chart conclusions of the radial capture are not
needed below.

We use a single fixed sum of the seven actual separation inequalities,
with edge multipliers in cyclic order HG,GA,AB,BT,TD,DE,EH:
\[
                          (1,1,1,1,1,e,1).            \tag{4}
\]
No multiplier depends on an angle or a radial chart.

## 2. Choose an actual high owner according to the error sign

For a quarter edge from \((a,-b)\) to \((A,-B)\), its two high
projections are
\[
 P_2=a\cos d+b\sin d+B,
 \qquad P_3=a+A\sin d+B\cos d.
\]
If d>=0, (3) gives
\[
 P_3-P_2=(a-B)(1-\cos d)+(A-b)\sin d\ge0.
                                                               \tag{5}
\]
Thus any actual owner 2 also supplies actual owner 3.

If \(d=-z\le0\), put \(t=\tan(z/2)\). Here z<P and t<1/3.
The same difference becomes
\[
                   P_3-P_2=\sin z\{ta+b-A-tB\}.       \tag{6}
\]
Sorted circle containment gives \(ta+b\le(1+t)c\).
On the target outer arc, \(A+tB\) is concave in B, so its
minimum is the smaller of \(a_0\) and \((1+t)c\).
The latter is smaller: \(a_0>7/5\), whereas
\((1+t)c<(4/3)(9/10)=6/5\). Consequently P3<=P2.
An actual owner 3 therefore supplies actual owner 2 at negative error.

We may hence select owner 3 at positive quarter error and owner 2 at
nonpositive quarter error. These are original feasible projections;
there is no physical change of frame in this selection.

## 3. The fixed dual sum and its exact slider supports

Set
\[
 W(t)=\frac{1+\cos t+\sin t}{2}\quad(t\ge0),
 \qquad f(t)=W(t)-a_0\sin t
            =\frac{1+\cos t}{2}-(a_0-\tfrac12)\sin t.
                                                               \tag{7}
\]
Collect the two coordinate coefficients at each state in the weighted
projection sum (4). For a force \((u,v)\), the full-circle bound is
\[
           ua+vb\le R\sqrt{u^2+v^2}-\frac{u+v}{2}.     \tag{8}
\]
We will use (8) at G,B,E, and sharper exact sorted-arc supports at
H,A,T,D. Let \(\mathcal D\) be the weighted sum of widths minus
these seven support upper bounds. Actual feasibility implies
\[
                             \mathcal D\le0.           \tag{9}
\]

Consider a zero source H,A or T, with positive zero error v. If its
incoming quarter has nonpositive error, its force is
\((\sin v,1-\cos v)\). If that quarter has positive error q,
its force is
\[
                     (\sin q+\sin v,\cos q-\cos v).
                                                               \tag{10}
\]
In both cases q+v<=P-2l=31/100, taking q=0 in the first case.
The force ratio in (10) is \(\tan((v-q)/2)\), which is less
than 1/6. Indeed
\[
 \frac16\{1-(31/200)^2/2\}-\frac{31}{200}
                         =\frac{4639}{480000}>0.
\]
Since \(a_0<3/2\), the ratio of the outer-arc inward normal at
b=0 is \(1/(2a_0+1)>1/4\). The linear support in (10) is therefore
attained at b=0 and is exactly
\[
                         a_0(\sin q+\sin v).           \tag{11}
\]
This also follows directly by differentiating the arc support as a
function of b.

On \([0,31/100]\), f is strictly concave. In fact
\(a_0-1/2<183/200\), and
\[
 f''(t)\le-\frac12\{1-(31/100)^2/2\}
                  +\frac{183}{200}\frac{31}{100}
             =-\frac{7693}{40000}<0.                  \tag{12}
\]
Thus
\[
                  f(q)+f(v)\ge f(0)+f(q+v).            \tag{13}
\]

For a positive GA, BT or EH error q, its source-anchor force is
independent of q; only (10) and its width change. Inequality (13)
therefore permits setting this quarter error to zero and adding q
to its following zero error in the expression for \(\mathcal D\).
This does not increase that expression. All three zero errors remain
at least l, every combined zero error remains at most 31/100, and p
is unchanged. These are reductions of a scalar lower bound, not
assertions of a deformed feasible packing.

After these three reductions write the negative GA, BT, EH errors
as r,u,t>=0, and the three zero errors as v,x,w>=l. Put
\[
                             S=v+x+w.                 \tag{14}
\]
Then \(3l\le S\le P\). Every remaining absolute error is at most P.

## 4. The remaining one-variable terms

Write
\[
\begin{aligned}
 g(r)&=1+\cos r-R\sqrt{2-2\sin r},\\
 d(z)&=\frac e2-c+e(\tfrac12-c)\cos z
                         +e(\tfrac12+c)\sin z,\\
 h(t)&=\frac{1+e}{2}+\cos t
                    -R\sqrt{1+e^2-2e\sin t}.
\end{aligned}                                                     \tag{15}
\]
The full-circle supports at G and B give precisely g(r),g(u).

For negative DE error \(-z\), D has force
\((e\cos z,1-e\sin z)\). Its second coefficient exceeds its first
throughout \([0,P]\). To see this, the degree-five alternating
upper bound gives
\[
 \sin P<\frac12,
 \qquad \frac12-\{P-P^3/6+P^5/120\}
                       =\frac{3653707}{1171875000}>0.
                                                               \tag{16}
\]
For \(0\le s\le1/2\), \(\sqrt{1-s^2}+s\le(\sqrt3+1)/2<11/8\).
Consequently \(e(\cos z+\sin z)<(18/25)(11/8)=99/100<1\).
The exact sorted-arc support at D is therefore
\(c(1+e\cos z-e\sin z)\), giving d(z).
The full-circle support at E then gives h(t). Hence, if DE is
nonpositive, the reduced expression is
\[
 \mathcal D\ \ge\ f(v)+f(x)+f(w)+g(r)+g(u)+d(z)+h(t),
 \qquad S=r+u+z+t.                                    \tag{17}
\]

Two derivative comparisons will be useful:
\[
                     g'(r)>\frac65,
                     \qquad d'(z)<\frac{21}{20}
                     \quad(0\le r,z\le P).            \tag{18}
\]
For the first, set s=sin r, so \(0\le s<1/2\). Since
\(c+1/2>1399/1000\) and \(\sqrt{1+s}\ge1+4s/9\),
\[
 g'(r)=-s+(c+\tfrac12)\sqrt{1+s}
       >\frac{1399}{1000}-\frac12\left(1-\frac{1399}{2250}\right)
       =\frac65+\frac{89}{9000}.
\]
For the second, Cauchy--Schwarz and c<9/10 give
\[
 d'(z)\le e\sqrt{2c^2+\tfrac12}
             <e\sqrt{\frac{53}{25}}<\frac{21}{20},
 \qquad
 (21/20)^2-e^2(53/25)=\frac{873}{250000}>0.
                                                               \tag{19}
\]

## 5. Positive DE error also reduces to (17)

If DE has positive error z, D has force (e,1), with exact support
\((1+e)c\). E has force
\[
                      (\cos t+e\sin z,e\cos z-\sin t).
\]
Its norm squared is \(1+e^2-2e\sin(t-z)\). The combined DE--EH
part of the lower bound is therefore
\[
 J(z,t)=\frac{1+e}{2}-(1+e)c
       +e(\cos z+\sin z)+\cos t
       -R\sqrt{1+e^2-2e\sin(t-z)}.                    \tag{20}
\]
The other terms are the f and g terms in (17), and
\[
              S+z=r+u+t,\qquad 0\le z\le P-3l=41/200.
                                                               \tag{21}
\]

First decrease z and t together, holding t-z fixed, until one is
zero. The derivative in the reverse direction is
\[
 e(\cos z-\sin z)-\sin t
 \ge e\{1-(41/200)^2/2-41/200\}-P
                  =\frac{37271}{1000000}>0.            \tag{22}
\]
Thus this change does not increase the scalar expression. If z
reaches zero, (17) results immediately.

Otherwise t reaches zero first. Now r+u=S+z. At t=0,
\[
 \frac{d}{dz}J(z,0)
   =e(\cos z-\sin z)
     -\frac{Re\cos z}{\sqrt{1+e^2+2e\sin z}}
   >-\frac{Re}{\sqrt{1+e^2}}> -\frac65.                \tag{23}
\]
The final strict comparison follows from
\[
 (6/5)^2(1+e^2)-Qe^2=\frac{61191}{390625}>0.
\]
Pair a decrease of z with an equal decrease of r, then u if
necessary. This is possible because r+u=S+z>z. Equations (18)
and (23) show again that the scalar expression decreases.
At the end DE and EH both have zero error and (17) applies.
All intermediate arguments remain in their displayed intervals;
positive and negative total variation decrease together.

## 6. Concentrate the remaining negative errors and zero errors

In (17), transfer r and u to z, keeping t fixed. The first derivative
comparison in (18) and the second comparison in (19) imply
\[
             g(r)+g(u)+d(z)\ge2g(0)+d(z+r+u).          \tag{24}
\]
All new arguments are at most S<=P.

Next apply the concavity (12) to the three zero errors, each at
least l. It gives
\[
                 f(v)+f(x)+f(w)\ge2f(l)+f(S-2l).      \tag{25}
\]
The intermediate merged arguments are at most S-2l<=31/100.
Thus every original feasible cycle under the putative signs must
satisfy
\[
 0\ge\mathcal D\ge K(S,z)
   :=2f(l)+f(S-2l)+2g(0)+d(z)+h(S-z),
 \quad 3l\le S\le P,\quad 0\le z\le S.              \tag{26}
\]

## 7. Whole-domain concavity reduces (26) to four endpoints

Put A=1+e^2 and s=sin t. Differentiation of (15) gives
\[
 h''(t)=-\cos t+
 Re\frac{e-As+es^2}{(A-2es)^{3/2}}.                  \tag{27}
\]
The derivative with respect to s of the quotient in (27) has the
sign of
\[
 3e^2-A^2+eAs-e^2s^2
 \le3e^2-A^2+eA/2
                   =-\frac{79576}{390625}<0.
\]
Hence the quotient is at most \(e/A^{3/2}\). Also
\[
 \left(\frac{11}{20}\right)^2 A^3-Qe^4
                      =\frac{654105829}{97656250000}>0.
\]
Since \(\cos t\ge1-P^2/2=1081/1250\), (27) proves
\[
                         h''(t)<-\frac{787}{2500}.
                                                               \tag{28}
\]
On the same interval,
\[
                         d''(z)\le e(c-\tfrac12)
                                  <\frac{36}{125}.
\]
It follows that
\[
                         K_{zz}< -\frac{67}{2500}<0.
                                                               \tag{29}
\]
The minimum at each fixed S is therefore at z=0 or z=S.

Define those two endpoint functions as K0(S),K1(S). The first has
second derivative \(f''(S-2l)+h''(S)<0\).
For the second, S>=3l and
\[
 \sin S\ge\sin(3l)>3/10,
 \qquad 3l-(3l)^3/6-3/10=\frac{156651}{16000000}>0.
\]
Consequently
\[
 d''(S)<e\{2/5-(1399/1000)(3/10)\}<0,
 \qquad (1399/1000)(3/10)-2/5=\frac{197}{10000}>0.
\]
Thus K1 is concave as well. The minimum of (26) is among exactly
\[
                K0(3l),\quad K0(P),\quad K1(3l),\quad K1(P).
                                                               \tag{30}
\]
These are intrinsic endpoints of two concavity reductions, not an
angle partition or a sampled state inventory.

## 8. Exact rational evaluation at the four endpoints

The following short rational enclosures suffice:
\[
\begin{gathered}
 f(l)>\frac{901}{1000},\qquad
 f(31/100)>\frac{87}{125},\qquad
 g(0)>-\frac45,\qquad d(0)>-\frac{207}{250},\\
 \frac{1549}{5000}<\sin(3l),\qquad
 \frac{19}{20}<\cos(3l)<\frac{951}{1000},\\
 \frac{621}{1250}<\sin P,\qquad
 \frac{4339}{5000}<\cos P<\frac{217}{250},\\
 \sqrt{QA}<\frac{2439}{1000},\qquad
 \sqrt{Q(A-2e\sin(3l))}<\frac{41}{20},\qquad
 \sqrt{Q(A-2e\sin P)}<\frac{887}{500}.
\end{gathered}                                                     \tag{31}
\]
For completeness, the f bounds follow by substituting
\[
 f(t)\ge1-t^2/4-\frac{183}{200}(t-t^3/6+t^5/120).
\]
The positive rational reserves at l and 31/100 are respectively
\[
 \frac{883687669839}{2560000000000000},\qquad
 \frac{67703821789}{80000000000000}.
\]
All trigonometric bounds in (31) follow from the alternating
polynomials
\[
 t-t^3/6+t^5/120-t^7/5040\le\sin t\le t-t^3/6+t^5/120,
\]
\[
 1-t^2/2+t^4/24-t^6/720\le\cos t\le1-t^2/2+t^4/24.
\]
Using the displayed sine lower bounds, the three squared-root
reserves in the last line of (31) are, in order,
\[
 \frac{81849}{25000000},\qquad
 \frac{601423}{156250000},\qquad
 \frac{440293}{156250000}.
\]

Direct substitution in (15), with c<9/10, now yields
\[
\begin{aligned}
 K0(3l)&>3\frac{901}{1000}-\frac{196}{125}
                    +\frac{19}{20}-\frac{41}{20}
          =\frac7{200},\\
 K0(P)&>2\frac{901}{1000}+\frac{87}{125}-\frac{196}{125}
                    +\frac{4339}{5000}-\frac{887}{500}
          =\frac{119}{5000},\\
 K1(3l)&>3\frac{901}{1000}-\frac7{25}-\frac{2439}{1000}
       +\frac{18}{25}\left(-\frac25\frac{951}{1000}
                                  +\frac75\frac{1549}{5000}\right)
          =\frac{6997}{312500},\\
 K1(P)&>2\frac{901}{1000}+\frac{87}{125}-\frac7{25}
                    -\frac{2439}{1000}
       +\frac{18}{25}\left(-\frac25\frac{217}{250}
                                  +\frac75\frac{621}{1250}\right)
          =\frac{18619}{625000}.
\end{aligned}                                                     \tag{32}
\]
Every value on the right exceeds 1/50. Equations (26)--(30)
therefore imply \(0\ge\mathcal D>1/50\), a contradiction.
This proves (1).

The proof retains all original weak owners through (5)--(6), then
uses one fixed cyclic stress, sorted-circle support, derivative
comparisons and concavity. It requires no numerical optimizer,
angle mesh, generated row inventory, oracle premise, Lean run or CI.
