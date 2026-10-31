# Two-RR seven-cycles cannot have a shared direct return

Date: October 30, 2026. Author: joint-pockets continuation.

**Status: complete whole-feature hand exclusion, frozen for independent
review.** The exact two-RR short-C7 geometry fixes three radial
loaded bodies. If the fourth, physically unique-circle loaded body
shares a side segment with its direct radial neighbor, its original
force and torque equations force that shared mean strictly outside
the actual shared interval.

The proof is uniform over the entire radius interval \(2<R\le
\sqrt{1105}/16\). It retains both actual completion squares and all
their physical contacts, and needs no Phi-minimum premise.

## 1. Exact original family

Keep the original compatible physical certificate whose entire
positive component is
\[
                  X-U_+-A-U_3-D-B-U_--X.
\tag{1.1}
\]
The four loaded bodies are \(X,A,B,D\). The first three have two
physical circle corners; \(D\) has one physical circle corner.
Every individual radial corner weight, including either zero
endpoint, remains. The three \(U\)'s are genuine unloaded
full-positive-degree-two side transmitters, with their unchanged
normals and actual application means.

All nine actual squares remain contained in the original disk, with
disjoint open interiors, and
\[
                          2<R\le\frac{\sqrt{1105}}{16}.
\tag{1.2}
\]
Every extra physical contact, including all zero-weight contacts
at a core body, remains. There are no omitted positive forces
at a core vertex: (1.1) is the whole positive component.

**Theorem.** The actual direct contact \(B-D\) cannot be a
positive-length shared segment.

This is the entire shared direct-return branch of the two-RR
short-C7 remainder. The pattern is the one identified in [N],
Section 8, where its two actual extras are a central square
and an occupied radial/unique side-pocket square. The proof
below also applies when the exact pattern (1.1) is assumed
directly; their locations do not enter its contradiction.

## 2. The three radial loads fix the remaining angular arc

Put
\[
 d=\sqrt{R^2-\tfrac14}-1,\qquad
 \phi=\arctan\frac1{2d},\qquad
 \rho=\sqrt{d^2+\tfrac14}=\frac1{2\sin\phi}.
\tag{2.1}
\]
The complete actual radial channel calculation [R], Section 8,
makes each RR channel's outward consecutive loaded-center gap
exactly \(4\phi\). The physical circle-spoke order identifies these
as the actual two consecutive gaps through \(X\), rather than
freely chosen minor arcs.

Choose the radial frame of \(B\) to be \(e=(1,0)\), \(f=(0,1)\).
Reflect the whole coordinate description if necessary so that the
remaining loaded center \(D\) lies on the counterclockwise arc
from \(B\) toward \(A\). Then
\[
 \begin{gathered}
 B=[d,d+1]\times[-\tfrac12,\tfrac12],\\
 e_A=(\cos\gamma,\sin\gamma),\qquad
 A=[d,d+1]e_A+[-\tfrac12,\tfrac12]Je_A,\\
 \gamma=2\pi-8\phi,\qquad
                0<\arg c_D<\gamma.
 \end{gathered}
\tag{2.2}
\]
These are descriptions of the original bodies, not motions of them.

The exact estimates in [T], Section 2, and the same strict lower
radius in (1.2) give
\[
 \frac{14}{15}<d<\frac{61}{60},\qquad
 \frac{\pi}{7}<\phi<\frac{\pi}{6},\qquad
 \frac{2\pi}{3}<\gamma<\frac{6\pi}{7}<\pi.
\tag{2.3}
\]
For the strengthened lower d bound,
\[
 \sqrt{15}/2>29/15
\]
has squared reserve \(11/900\), so \(R>2\) implies
\(d>\sqrt{15}/2-1>14/15\). In particular \(D\)'s actual center
has positive f coordinate, by (2.2).

## 3. Complete shared-face cover at the radial neighbor

Suppose \(B,D\) share a positive-length segment. Two unit squares
sharing a side segment have parallel full frames. We check every
actual side of \(B\).

The outer radial side \(x=d+1\) cannot have a contained neighbor.
A unit beyond it has width at least one, hence a point with
x coordinate at least \(d+2>R\).

If the shared side were the inner radial side \(x=d\), the
neighbor \(D\) would have center
\[
                         (d-\tfrac12,t).
\]
Its boundary-circle condition, with \(d-\tfrac12>0\), gives
\[
              d^2+(|t|+\tfrac12)^2=R^2,
 \qquad |t|=\sqrt{2d+\tfrac54}-\tfrac12>1.
\tag{3.1}
\]
The strict final inequality follows already from \(d>1/2\).
But positive overlap between its vertical side interval
\([t-\tfrac12,t+\tfrac12]\) and \(B\)'s interval
\([-\tfrac12,\tfrac12]\) requires \(|t|<1\).
Thus inner radial sharing is impossible, including its potential
closed contact limits.

It remains that \(D\) shares a tangential side. Its center has
f coordinate \(+1\) or \(-1\). The physical center order (2.2)
forces \(+1\). Write the other center coordinate as \(a\). Its
farthest-corner equation is
\[
          (|a|+\tfrac12)^2+\frac94=R^2.
\]
Define
\[
                      k=\sqrt{R^2-\frac94}
                       =\sqrt{d^2+2d-1}.
\tag{3.2}
\]
Here \(k>1\) because \(R>2\). The alternative
\(a=-(k-\tfrac12)\) puts the entire radial projection of \(D\)
in \([-k,1-k]\), strictly left of \(B\), and cannot share a
segment with it. Consequently the only actual shared geometry is
\[
                 \boxed{D=[k-1,k]\times[\tfrac12,\tfrac32].}
\tag{3.3}
\]
Since \(k>d\) and \(k<d+1\), their complete shared interval is
\[
                       B\cap D=[d,k]\times\{\tfrac12\}.
\tag{3.4}
\]
Both inequalities follow directly by squaring (3.2), using
\(d>1/2\). The physical unique circle corner of \(D\) is
\[
                            z_D=(k,\tfrac32).
\tag{3.5}
\]

Thus all original B-side choices, both tangential signs, both
radial center signs, and every endpoint of the true shared interval
have been accounted for. No shared mean has yet been chosen.

## 4. A uniform exact bound for the radial port height

The strict \(+e\) support of the actual radial \(A\) is its inner
vertex
\[
 p_A=d e_A-\tfrac12Je_A=(u,v).
\tag{4.1}
\]
Indeed \(\cos\gamma<0\) and \(\sin\gamma>0\), so maximizing
the first coordinate chooses radial coordinate d and tangential
coordinate \(-1/2\), uniquely. Its polar description is
\[
 \begin{split}
 u&=d\cos\gamma+\tfrac12\sin\gamma,\\
 v&=d\sin\gamma-\tfrac12\cos\gamma,\\
 \arg p_A&=\gamma-\phi=2\pi-9\phi,\\
 v&=-\frac{\sin9\phi}{2\sin\phi}.
 \end{split}
\tag{4.2}
\]

We prove the uniform full-interval estimate
\[
                         u<0,\qquad \frac12<v<\frac{21}{20}.
\tag{4.3}
\]
By (2.3),
\[
      \frac{\pi}{2}<2\pi-9\phi<\frac{5\pi}{7}<\frac{3\pi}{4}.
\]
Thus \(u<0\) and \(v>\rho/\sqrt2\). Also
\[
             \rho^2=d^2+\tfrac14>
             \left(\frac{14}{15}\right)^2+\frac14
             =\frac{1009}{900}>1,
\]
Hence \(v>1/\sqrt2>1/2\).

For the upper bound set
\[
                  x=\sin^2\phi=\frac1{4d^2+1},
           \qquad z=x-\frac15.
\]
The lower d bound gives
\[
 x<\frac{225}{1009},\qquad
 z<\frac{116}{5045}<\frac1{40},
\tag{4.4}
\]
with \(4640<5045\) for the last comparison. The exact
ninth-angle identity gives
\[
 \begin{split}
 v&=-\frac12(9-120x+432x^2-576x^3+256x^4)\\
  &=\frac{1199}{1250}+\frac{508}{125}z
       -\frac{1848}{25}z^2+\frac{928}{5}z^3-128z^4.
 \end{split}
\tag{4.5}
\]
This is an algebraic identity over the entire interval, with no
angle sample or numerical approximation.

Since \(z<1/40\),
\[
 \frac{1848}{25}-\frac{928}{5}z>
 \frac{1732}{25}>64.
\]
Dropping the nonpositive fourth-order term and completing the square
therefore yields
\[
 \begin{split}
 v
 &\le \frac{1199}{1250}+\frac{508}{125}z-64z^2\\
 &\le \frac{1199}{1250}+\frac{(508/125)^2}{256}\\
 &<\frac{24}{25}+\frac{81}{1024}
  <\frac{21}{20}.
 \end{split}
\tag{4.6}
\]
Here \(508/125<9/2\), and the last strict comparison follows
from \(8100<9216\), because \(21/20-24/25=9/100\).
The estimate permits negative \(z\); completing the square is
global and no one-sided substitution in the linear term is used.
This proves (4.3).

## 5. The original side channel has this exact normal and mean

Because \(k>1\), \(u<0\), and \(1/2<v<21/20<3/2\),
the point
\[
                         p_D=(k-1,v)
\tag{5.1}
\]
lies in the relative interior of the actual left side of \(D\).
The entire \(A\) lies in \(x\le u\); the entire \(D\) lies in
\(x\ge k-1\). Their closest set distance is therefore exactly
\[
                         L=k-1-u>0,
\tag{5.2}
\]
attained at \(p_A,p_D\).

The original \(A-U_3-D\) channel, with its full unloaded force
and torque, attains the actual minimum-norm difference vector of
\(D-A\), by [L], Lemma N.1. That minimum vector is unique by
strict convexity of Euclidean squared norm, as in Lemma N.2.
The explicit vector in (5.2) is \(Le\), so the original channel
normal is exactly \(e\). Its actual side reserve is one, hence
\(L=1\).

Furthermore \(p_A\) is \(A\)'s unique exposed point in this
normal. Its original application is therefore precisely (4.1).
Telescoping the original true-two \(U_3\) equations gives the
unchanged other application \(p_A+e=p_D\). In particular its
actual transverse mean is exactly \(v\), rather than a chosen
midpoint or a new mean on \(D\)'s side.

The side transmitter is consequently parallel to the same
\(e,f\) frame at this contact. No common frame has been imposed
on \(A,X,U_+,U_-\).

## 6. The full unique-loaded star forces its shared mean below d

Let the actual shared \(B-D\) mean be
\[
                          p_{BD}=(t,\tfrac12).
\]
Equation (3.4) retains its entire original range:
\[
                              d\le t\le k.
\tag{6.1}
\]
At the true loaded degree-two body \(D\), the original forces
toward \(U_3\) and \(B\) have positive magnitudes \(\mu,\nu\)
and outward normals \(-e,-f\), respectively. Its one physical
circle corner is (3.5), so its positive circle force is
\(\chi z_D\), for some \(\chi>0\).

The complete original force equation at this body is
\[
                \chi(k,\tfrac32)-\mu e-\nu f=0.
\]
Thus
\[
                         \mu=\chi k,\qquad
                         \nu=\frac32\chi.
\tag{6.2}
\]
The original torque equation about the circle origin is equally
literal: the circle force has zero origin moment, while the two
pair forces give
\[
                             \mu v-\nu t=0.
\tag{6.3}
\]
Consequently
\[
                              t=\frac{2k}{3}v.
\tag{6.4}
\]

On the other hand (3.2) gives the global exact inequality
\[
                    k^2=d^2+2d-1\le2d^2,
\]
because their difference is \((d-1)^2\). Using (4.3),
\[
 t=\frac{2k}{3}v
    <\frac{2\sqrt2\,d}{3}\frac{21}{20}
     =\frac{7\sqrt2}{10}d<d.
\tag{6.5}
\]
The final strict comparison is \(98<100\). This contradicts
the actual mean interval (6.1), including its lower endpoint.

Every original force at \(D\) has been retained, and both original
side means were kept until the actual geometry fixed the channel
application. No virtual edge, replacement packing, truncated star
or independently chosen support point was introduced. The entire
shared direct-return family is impossible.

## 7. Literal remaining direct-contact features

The already accepted no-other-boundary-contact source [J], Section 5,
excludes a positive free vertex/vertex direct edge \(B-D\) in the
same original pattern under its stated common generic selection.
It uses the mixed shared-block theorem at the singleton block
\(\{D\}\) or the actual block \(\{D,U_3\}\), retaining every
physical extra contact.

Combining that result with the present complete shared-segment
exclusion leaves precisely the two singleton side-owner
alternatives for \(B-D\): \(B\) supplies a side and \(D\) a
vertex, or \(D\) supplies a side and \(B\) a vertex.
Their full actual features and both completion squares remain.
The present theorem does not claim those two alternatives impossible
or close the whole two-RR mask, the mixed C7 parent, or the
unrestricted nine-square theorem.

## 8. Complete frozen operative inputs

| Label | Complete source | SHA-256 | Literal use |
| --- | --- | --- | --- |
| [R] | RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md | 2d78bc2892c11e58007881ff84d57cc6606dce201bb46d412ef216c12577191e | The original RR center gap is \(4\phi\) at its actual physical circle order, with all radial weight endpoints retained. |
| [T] | RADIAL_RADIAL_SIDE_TRANSMITTERS_ARE_TRANSVERSELY_FREE_OF_ALL_BOUNDARY_CORE_BODIES_2026_10_30.md | 658e5ddc2a2f0494510d82057495f74d5274fd053f77e0e7e00724fdd98209ed | Only the complete exact window and \(\pi/7<\phi<\pi/6\) proof in Section 2. No canonical motion is used. |
| [L] | PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md | ec8be96131806c998d8a768526d2deb644c28be72559d34e033c8d07d917ffab | Complete actual normal-channel and minimum-difference-vector theorems, retaining full true-two forces and applications. |
| [N] | RADIAL_RADIAL_TRANSMITTERS_CAN_SLIDE_OUTWARD_AND_CANNOT_FORM_A_CLOSED_TWO_BODY_BLOCKER_NETWORK_2026_10_30.md | 0fbcce339700b2d2e23fa30a516a64c2773e868b90ed60f695fcc93ac4cafff7 | Only identification of the exact original two-RR C7 pattern and its retained actual extras. The main proof directly assumes that pattern. |
| [J] | RADIAL_RADIAL_TRANSMITTERS_HAVE_NO_NONCONSECUTIVE_BOUNDARY_CORE_CONTACT_2026_10_30.md | f87e7d86c332a8ba699311788a9eca0d0a2bf109db5e218aa54ff21274ceeb36 | Used only in this source's Section 7: its Section 5 excludes the complementary free-VV edge under the existing common selection. |

The shared-face cover, full-interval height bound, actual-channel
identification and original mean contradiction are proved above.
Every direct source has been read in full. A separate independent
whole-source review is required before adoption of this new
feature-family exclusion.

No original flag or metadata is changed. No numerical pose or angle
search, grid, optimizer, computational packing certificate,
Lean/Lake invocation, CI dispatch or remote edit is used.

