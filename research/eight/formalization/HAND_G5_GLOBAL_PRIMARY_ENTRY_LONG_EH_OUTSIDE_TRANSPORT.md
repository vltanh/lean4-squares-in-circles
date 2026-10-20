# The long positive EH1 endpoint moves inward from a negative DE3 error

## 1. Local theorem and the normal-primary application

Put
\[
 q_L=19577/5000,\qquad Q=9789/2500,\qquad h=7/10.
\tag{1}
\]
Let D,E,H be sorted, contained at a common actual ceiling
\(q_L\le q\le Q\), with true-core avoidance and signed
tangents negative, nonpositive, positive respectively.
Assume
\[
                  b_H>211/250=.844,\qquad a_H<1.
\tag{2}
\]
Let E be either an outer q state or a point on the actual
true-core boundary. Require also that H is already outer at
q, or that increasing H's primary leaves its other retained
witness unchanged or improved. This holds automatically for
an aligned HG witness, whose projection uses only H's tangent.
Retain actual DE3 and EH1 at errors
\[
 \theta_E-\theta_D=-n<0,
 \qquad \theta_H-\theta_E=p>11/50,
 \qquad n,p\le h.
\tag{3}
\]

**Outside transport.** Keeping D, H's tangent and frame, and
all other states and frames fixed, first raise H's primary
to its q-circle if needed. Then changing only E gives one
of the following actual endpoints:

* EH0 is feasible;
* EH1 is feasible with positive error at most \(11/50\);
* DE is aligned and EH1 has error \(p-n>11/50\).

At the third endpoint the original H/D span is positive.
In particular it cannot occur when \(p-n\le0\). Thus a
nonpositive selected DE3/EH1 total always reaches one of
the first two endpoints. The theorem includes total zero,
weak contacts, both E radial kinds, and both possibilities
for the order of n and p.

The E frame moves only toward H and stops no later than D
or at the indicated short-EH error. The real frame interval
does not expand. Both positive and negative variations
decrease by the E-frame movement. E's circle never increases;
on an outer arc it stays equal to q. All actual neighboring
inequalities other than these two remain identical.

In the HG-aligned genuine-negative GA1 class, (2) follows
from the actual GA0 failure. The first two endpoints join
[the full EH0 or short-EH1 H/G transport](HAND_G5_GLOBAL_PRIMARY_ENTRY_ALIGNED_HG_NEGATIVE_GA_EH0.md),
which reaches GA0 with strict H-circle loss and preserves
all A,B,T,D data. Consequently, if BT2 is retained, every
input of that class with an actual nonpositive DE3/EH1 total
is sharp, with strict inequality when GA0 was unavailable.
There is no AB/TD alignment or T-sign input.

This note concerns an actual DE3 witness at a negative error.
An original DE2 witness is not silently replaced by DE3.
For a positive E total the displayed aligned-DE endpoint
is retained as an explicit alternative.

## 2. H can be made outer without changing its tangent

Raise only H's primary to
\[
                  a_H^q=\sqrt{q-(b_H+1/2)^2}-1/2.
\tag{4}
\]
Sorting and true-core avoidance persist. The EH1 projection
increases. In the intended normal-primary application, HG
is aligned and depends only on H's tangent, so it too is
unchanged. A primary lift therefore preserves every actual
constraint used in that application.

The upper bound in (2) persists even after the lift:
\[
 9/4+(168/125)^2-Q>0,
\]
so \(b_H>.844\) forces \(a_H^q<1\). The primary lift is
at the same actual q. It does not assert a loss at H yet;
the final H/G transport supplies the strict H loss.

In the local theorem without the HG application, the H
primary lift is permitted exactly when H's other retained
constraint is unchanged or improved by it. If that other
constraint has not been specified, require H to be outer
already and omit the lift. The E-only part below then
keeps all of H fixed.

## 3. The actual radial arcs and the EH contact derivative

Write E's unsigned coordinates as \((a,b)\). On the core
boundary,
\[
 a_C(b)=
 \begin{cases}
 7/12,&0\le b\le1/2,\\
 \displaystyle1/2+\sqrt{1/144-(b-1/2)^2},
      &1/2\le b\le1/2+1/(12\sqrt2).
 \end{cases}
\tag{5}
\]
On the sorted outer arc,
\[
 a_O(b)=\sqrt{q-(b+1/2)^2}-1/2.
\tag{6}
\]
Set \(v=-a'(b)\). Every relevant arc has \(0\le v\le1\).
The identities that distinguish the curved core and outer
arcs are
\[
 b-va=(1-v)/2\quad\hbox{on curved core},
 \qquad b-va=-(1-v)/2\quad\hbox{on outer}.
\tag{7}
\]
The flat core has v=0 and \(0\le b\le1/2\).

Move the E frame toward H by \(\tau\ge0\), so
\[
                       n_\tau=n-\tau,
                       \qquad p_\tau=p-\tau.
\tag{8}
\]
Stop if EH0 appears, if \(p_\tau=11/50\), or if
\(n_\tau=0\). Before such a stop both errors have their
original strict signs.

Initially keep b fixed. The EH1 slack decreases as p
decreases, because its derivative in p is
\[
                    (a-1/2)\cos p+(b+1/2)\sin p>0.
\tag{9}
\]
At fixed b the negative-DE3 slack increases, since its
\(\tau\)-derivative is
\[
                    (a+1/2)\cos n+(b-1/2)\sin n>0.
\tag{10}
\]
The last sign uses \(a>1/2\), \(b\ge0\), and
\(\tan n<1\).

If EH1 first reaches contact, follow that contact on the
same actual radial arc. Implicit differentiation gives
\[
 \beta:=\frac{db}{dp}
   =\frac{(a-1/2)\cos p+(b+1/2)\sin p}
           {\cos p+v\sin p}>0.
\tag{11}
\]
Thus b decreases along the motion. Sorting becomes stricter.
The denominator is positive, and the core derivative joins
smoothly across b=1/2, so neither is a stopping obstruction.
E stays on its true core or outer circle. Its corner value
is constant on the outer arc; on the flat core it increases
with b, and on the curved core its derivative is
\[
 \frac{d}{db}\{(a+1/2)^2+(b+1/2)^2\}
                    =2(1-v)\ge0.
\tag{12}
\]
Since b decreases, the core corner never increases either.

## 4. Negative DE3 improves on both radial kinds, for either total sign

Its actual margin is
\[
 M=a_D-1/2-(a+1/2)\sin n+(b-1/2)\cos n.
\tag{13}
\]
Put \(x=\tan n\), \(y=\tan p\). Both lie in \([0,1)\),
without assuming which is larger. With
\(db/d\tau=-\beta\), direct differentiation of (11)--(13)
gives the exact identity
\[
 \frac{1+vy}{\cos n}\frac{dM}{d\tau}
 =1-\frac{1-v}{2}(x+y)+(b-va)(x-y)-vxy.
\tag{14}
\]
Each entire radial arc has an immediate positive lower bound:

* On the outer arc, (7) makes (14)
  \[
                  1-x\{(1-v)+vy\}\ge1-x>0.
  \tag{15}
  \]
* On the curved core, (7) makes it
  \[
                  1-y\{(1-v)+vx\}\ge1-y>0.
  \tag{16}
  \]
* On the flat core it is
  \[
        1-(1/2-b)x-(1/2+b)y
                          \ge1-\max\{x,y\}>0.
  \tag{17}
  \]

The coefficients in the last line are nonnegative and sum
to one. These whole-domain identities are also valid at the
flat/curved core junction. Thus DE3 strictly improves along
every nontrivial contact segment. Unlike the earlier
negative-total version of this calculation, no inequality
between n and p is needed.

The only additional radial boundary is b=0. The next section
shows that it supplies an advertised endpoint and is not an
unproved alternative.

## 5. Zero tangent: actual EH0 on the core, or a short EH1 error outside

First suppose b=0 on the core and EH1 is at contact. Then
\(a=7/12\). Put \(k_0=1/12\), and write H's outer corner
as \((X_H,Y_H)\). The contact equation says
\[
 X_H=1+\tfrac12\cos p-k_0\sin p.
\]
Define
\[
                  Z=1+k_0\cos p+\tfrac12\sin p.
\]
The exact identity and one positive-square bound give
\[
 X_H^2+Z^2
 =325/144+(7/6)\cos p+(5/6)\sin p
 \le325/144+\sqrt{74}/6
 <541/144<q_L\le q.
\tag{18}
\]
Since H is on its actual q-circle, \(Y_H>Z\). Substitution
into the original EH0 projection yields
\[
       a_H\cos p+b_H\sin p-W(p)
                           =\sin p\,(Y_H-Z)>0.
\tag{19}
\]
Thus the actual EH0 witness is available at this endpoint.
The strict circle reserve in (18) is
\[
                        q_L-541/144=14261/90000>0.
\]

Now suppose b=0 on the outer circle and EH1 is at contact.
Let \(a_0(q)=\sqrt{q-1/4}-1/2\). Positive squaring gives
\(a_0(q)>7/5\), since \(q_L-1/4-(19/10)^2>0\).
Contact would require
\[
 a_H=\tfrac12+\tfrac12\cos p-(a_0(q)-1/2)\sin p.
\tag{20}
\]
The right side strictly decreases with p on \([0,h]\).
If \(p\ge11/50\), use \(a_0(q)-1/2>9/10\),
\(\cos p\le1\), and the cubic lower sine polynomial:
\[
 a_H<1-\frac9{10}S_3(11/50)
       =\frac{2008993}{2500000}<\frac{211}{250}<b_H.
\tag{21}
\]
This contradicts sorting. Consequently an outer zero-tangent
contact cannot be reached before the short-EH endpoint.

If E starts at zero tangent while EH1 has slack, keep it
there while moving its frame. Equations (9)--(10) apply
until the first EH contact or one of the angular endpoints.
At contact use (19) or (21), respectively. No tangent-floor
case has been discarded.

## 6. Completion, same-circle scope, and equality transfer

The contact curve has positive denominator, and all its
non-angular boundaries have been settled. The process reaches
EH0, a positive EH1 error at most \(11/50\), or DE alignment.
At DE alignment, \(p_{\rm end}=p-n\). Thus the third endpoint
can occur before the short-EH stop only when
\(p-n>11/50\). In particular every nonpositive total is
reduced to one of the first two endpoints.

The E state remains a canonical true-core or outer state.
For a core output the hard-class radial alternative
\(a_E\le7/12\) is automatic. For an outer output,
\(a_E\ge\sqrt{q/2}-1/2\) and all contained sorted endpoint
tangents are at most that same number. Hence
\(a_E\ge\max\{b_H,b_D\}\). Both versions of that alternative
remain valid when the subsequent H/G transport decreases
H's tangent.

Every center and circle in this construction is at the same
actual q. At an original boundary-neighbor input, E's decreasing
tangent preserves strict sorting, and the continuous actual
neighboring separations preserve the winding and physical
neighbor order, exactly as in the boundary-domain bridge.
The local argument itself needs only the displayed necessary
constraints and radial curves.

In the aligned-HG genuine-negative GA application, G,A,B,T,D
and their actual coordinates remain unchanged during this E
step. If either of the first two endpoints is reached, the
H/G theorem linked in Section 1 changes H and G only and
records a strict H-circle loss. It preserves the just-obtained
E state, its radial alternative, and every AB/BT/TD/DE
witness. If BT2 is retained, the arbitrary-sign hard theorem
then gives \(q\ge q_*\), and its equality characterization
contradicts the strict H loss at \(q=q_*\).

The local construction and first-two-endpoint join also
preserve an actual BT3 when that is the unchanged opposite
owner. The sharp conclusion is stated here only when BT2
has already been supplied. No loss at a transported E is
substituted for the required anchor loss at H, and no
transported E is identified with its original ancestor.
