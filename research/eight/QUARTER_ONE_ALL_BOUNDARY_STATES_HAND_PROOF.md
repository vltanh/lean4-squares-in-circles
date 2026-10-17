# Every boundary pair with one quarter increment: a hand proof

This theorem completes the middle row of the common three-row quarter
table. It treats both radial boundary curves, both tangent signs, and all
four separating axes retained by the common-point theorem. Its hypothesis
is a relative frame in the stated interval; the global theorem putting
all pairs into such intervals is a separate dependency.

## 1. States, signs, and the precise assertion

Throughout let

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 p=\frac{13}{200},\quad q=\frac{203}{200},\quad
 g=\frac{291}{250},\quad K=\frac{73}{10},\quad a_c=\frac7{12}.
\]

A positive outer state \(O=(a,b)\) satisfies
\[
 (a+\tfrac12)^2+(b+\tfrac12)^2=Q,\qquad 0\le b\le a.
\]
Write its endpoints as \((a_o,0)\), \((c_o,c_o)\). A positive
core state \(C=(a,b)\) lies on the side
\[
 a=a_c,\quad 0\le b\le\tfrac12,
\]
or the corner
\[
 a=\tfrac12+\sqrt{\tfrac1{144}-(b-\tfrac12)^2},\qquad
 \tfrac12\le b\le d:=\tfrac12+\frac{\sqrt2}{24}.
\]
The markers are
\[
 L_O=-\frac9{100}+pa+qb,\qquad
 L_C=K(a_c-a)+gb.                                           \tag{1}
\]
Give source \((a,b)\) and target \((A,B)\) signs
\(\sigma,\tau\in\{-1,1\}\); their local centers are
\((a,-\sigma b)\), \((A,-\tau B)\). Put
\[
 \phi=\frac\pi2+x,\quad |x|\le\frac7{10},\qquad
 W=\frac{1+\cos x+|\sin x|}{2}.
\]

**Theorem.** Suppose the positive directed center gap is
\[
 \delta=\phi+\sigma\arctan(b/a)-\tau\arctan(B/A)>0,
\]
and the two squares have disjoint interiors with a separator among the
four retained axes. Then
\[
 \boxed{\mathcal C:=\phi+\sigma L_s(a,b)-\tau L_t(A,B)
       >\frac{157}{200}=.785.}                              \tag{2}
\]
It is enough to prove (2) on the two source axes
\[
 \begin{array}{ll}
 \text{secondary:}&\sigma b+A\cos x+\tau B\sin x\ge W,\tag{3}\\
 \text{negative primary:}&a+A\sin x-\tau B\cos x\ge W.\tag{4}
 \end{array}
\]
Indeed, reflect the physical pair and reverse its order, then rotate so
the new source frame is zero. The transformation is
\[
 (s,t,\sigma,\tau,\phi)\longmapsto(t,s,-\tau,-\sigma,\phi).
\]
It preserves \(\delta\), \(\mathcal C\), and the state domains,
and sends the two retained target axes to the two source axes. This is a
physical reflection followed by an order reversal, not an assertion that
the two source-axis inequalities are interchangeable.

## 2. Elementary bounds used below

Squaring gives
\[
 1.4145<a_o<1.415,\quad .899<c_o<.9,\quad .558<d<.56,
 \qquad R<1.979<2.                                        \tag{5}
\]
On the outer arc, put \(r=(b+1/2)/(a+1/2)\). Then
\(da/db=-r\), \(0<r\le1\), and
\(r\ge100/383>3/13\). Thus \(L_O\) is increasing and
\(L_O-b\) is decreasing. Their endpoint values give
\[
 0<L_O<.882,\qquad -.019<L_O-b<.002.                       \tag{6}
\]
On the core,
\[
 0\le L_C<K(7/12-.558)+g(.56)<.84.                        \tag{7}
\]
Every core center has norm less than \(.8\): on the side use
\(85/144<16/25\), and on the corner use
\(\sqrt2/2+1/12<4/5\).

One additional sloping outer support will be useful:
\[
 a+.7b\le\sqrt{1.49Q}-.85<1.566.                          \tag{8}
\]
The first inequality is Cauchy--Schwarz applied to
\((a+1/2,b+1/2)\); the second is the rational comparison
\(1.49Q<2.416^2\).

For \(0\le z\le.7\) we use the alternating Taylor bounds,
including
\[
 \sin z\le z,\quad \sin z\ge z-z^3/6>.9z\quad(z>0),
\]
\[
 1-\cos z\le z^2/2,\qquad
 1-\cos z\ge z^2/2-z^4/24>.47z^2\quad(z>0),              \tag{9}
\]
and \(\sin z+\cos z\ge1\). In particular \(\cos z>.75\).
The shared Machin-series argument in
LOW_HIGH_ALIGNED_CONTACT_HAND_PROOF.md gives \(\pi>3.14159\).
All decimal constants in this proof are exact terminating rationals.

### 2.1. Two cases that need no axis calculation

If \(\sigma=1,\tau=-1\), (6)--(7) give
\[
 \mathcal C\ge\phi\ge\pi/2-.7>.785.                       \tag{10}
\]

For a core/core pair use the marker estimate in
CORE_CORE_WHOLE_PAIR_HAND_PROOF.md, with \(K=7.3\). For its
coefficient \(g_0=1.077372\),
\[
 |\arctan(b/a)-K(a_c-a)-g_0b|<.18.
\]
Changing \(g_0\) to \(g\) changes this expression by less than
\((g-g_0)(.56)<.06\). Therefore the odd quarter marker residual
\(\psi=\sigma(\arctan(b/a)-L_C)\) has \(|\psi|<.24\).
The same core/core lemma proves \(\delta>4/3\), from the
disjoint incircles and the core-center bound \(.8\). Consequently
\[
 \mathcal C=\delta-\psi_s+\psi_t>4/3-.48>.785.             \tag{11}
\]
This covers every sign and every axis for a core/core pair.

### 2.2. A three-endpoint support lemma

For \(\lambda\ge.975\), define
\[
 \begin{split}
 E_{\lambda,c}(x)&=\frac\pi2+x+c+\frac{p+q+\lambda}{2}
  +\lambda\cos x+\lambda\max(\sin x,0)-RN_\lambda(x),\\
 N_\lambda^2&=p^2+q^2+\lambda^2
                    +2\lambda(p\cos x+q\sin x).
 \end{split}                                               \tag{12}
\]
This envelope is concave separately on \([-.7,0]\) and
\([0,.7]\). To see this, direct differentiation gives
\[
 N_\lambda''+N_\lambda/4
 =\frac{(p^2+q^2-\lambda^2)^2}{4N_\lambda^3}\ge0.           \tag{13}
\]
The norm is positive and increasing, because
\(-p\sin x+q\cos x>0\). On the negative half,
\(N_\lambda\le N_\lambda(0)<1.5\lambda\): after squaring,
the sufficient quadratic is
\[
 (5/4)\lambda^2-2p\lambda-p^2-q^2>0,
\]
which is positive and increasing from \(\lambda=.975\).
Thus \(E''<\lambda(-.764+.75)<0\). On the positive half,
\(N_\lambda<2\lambda\) follows from
\[
 3\lambda^2-2\lambda(p+.645q)-p^2-q^2>0,
\]
again positive and increasing from \(.975\). Equations (13),
\(R<2\), and \(\cos x+\sin x\ge1\) give \(E''<0\).
Therefore it suffices to test \(-.7,0,.7\).

Use
\[
 .6442<\sin(.7)<.64424,\qquad
 .76484<\cos(.7)<.764844,
\]
from Taylor degrees seven/five and six/eight respectively. Together with
\(R<1.979\), \(\pi>3.14159\), the complete endpoint arithmetic is:

| \(\lambda\) | \(c\) | \(x\) | Upper \(N_\lambda\) | Lower \(E_{\lambda,c}\) |
|---:|---:|---:|---:|---:|
| .975 | .0919 | -.7 | .9 | .954814 |
| .975 | .0919 | 0 | 1.454 | .787729 |
| .975 | .0919 | .7 | 1.85 | 1.102859 |
| 1.015 | .088 | -.7 | .916 | .9698436 |
| 1.015 | .088 | 0 | 1.483 | .786438 |
| 1.015 | .088 | .7 | 1.87 | 1.1357406 |
| 1.164 | .09 | -.7 | .992 | 1.00990076 |
| 1.164 | .09 | 0 | 1.594 | .792269 |
| 1.164 | .09 | .7 | 2.007 | 1.15106456 |

Each norm comparison follows by squaring, using the upper cosine and
the appropriate lower or upper sine in its defining square. Thus all
three envelopes exceed \(.785\). We also retain the stronger baseline
\[
 F_0:=\frac\pi2+.09+\frac{p+q+g}{2}+g
             -R\sqrt{(p+g)^2+q^2}>.792269.                \tag{14}
\]

## 3. The source secondary axis

In every use of (3), subtract a nonnegative multiple \(\lambda\)
of its margin from \(\mathcal C\). This gives a lower bound consisting
of separate source and target linear functionals and \(\phi+\lambda W\).

### 3.1. Positive outer source and positive outer target

Take \(\lambda=.975\). The source functional after the two
constant outer marker terms cancel is
\(pa+(q-\lambda)b=pa+.04b\). It is concave as a function of
\(b\), hence its minimum occurs at an endpoint and exceeds \(.0919\).
The target functional has full-circle lower support
\[
 \frac{p+q+\lambda(\cos x+\sin x)}2-RN_\lambda(x).
\]
Together these give \(\mathcal C>E_{.975,.0919}>.785\).
This is also the complete theorem in
QUARTER_ONE_OUTER_SAME_HAND_PROOF.md.

### 3.2. A negative source must be small on this axis

Suppose \(\sigma=-1\). If the target is core, (3) is impossible,
since its left side is at most the target norm, less than \(.8<W\).
If the target is outer, (3) gives
\(b\le A\cos x+\tau B\sin x-W\).
When \(\tau\sin x\ge0\), circle support yields
\[
 b\le R-\tfrac12-(\cos x+|\sin x|)\le R-1.5<.479.
\]
When \(\tau\sin x\le0\), discard that nonpositive term to get
\[
 b\le(a_o-.5)\cos x-.5-.5|\sin x|<.415.
\]
In particular a negative core source must be on its side, with
\(a=a_c\) and \(L_C=gb\).

### 3.3. Core source and positive outer target

Take \(\lambda=g\). For a positive source,
\(L_C-gb=K(a_c-a)\ge0\). For a negative source, Section 3.2
gives \(-L_C+gb=0\). The full-circle support of the target
then gives, in both cases,
\[
 \mathcal C\ge E_{g,.09}>.785.                              \tag{15}
\]

### 3.4. Negative outer source and positive outer target

Take \(\lambda=q\). The source contribution is
\(-L_O+qb=.09-pa\ge.09-pa_o\). The target constant adds
another \(.09\), so its envelope constant is
\(.18-pa_o>.088\). Thus
\[
 \mathcal C>E_{q,.088}>.785.                               \tag{16}
\]

### 3.5. Both signs negative, with an outer target

Take \(\lambda=g\) for a core source and \(\lambda=q\) for
an outer source. The target functional is
\[
 -.09+(p-\lambda\cos x)A+(q+\lambda\sin x)B.
\]
Its \(A\) coefficient is negative and its \(B\) coefficient
positive throughout the interval, so it increases along the outer arc
as \(B\) increases. Its minimum is at \((a_o,0)\). For a core
source the remaining contribution is zero and the target's marker
\(L_O(a_o,0)>0\) may be dropped. For an outer source its lower
bound \(-L_O(a_o,0)\) cancels the target marker. Both cases give
\[
 \mathcal C\ge\phi+\lambda W-\lambda a_o\cos x.             \tag{17}
\]
At \(x=0\) the right side exceeds \(\pi/2-g(.415)\).
For \(x\ge0\) its difference from that value is
\[
 x+\lambda\sin x/2+\lambda(a_o-.5)(1-\cos x)\ge0.
\]
For \(x=-z\), (9), \(\lambda\ge1\), and
\(a_o-.5>.9\) give the lower bound
\[
 -z+\lambda\sin z/2+\lambda(a_o-.5)(1-\cos z)
 \ge-.55z+.4z^2\ge-\frac{121}{640}.
\]
Therefore (17) exceeds
\(\pi/2-g(.415)-121/640>.8986725>.785\).

### 3.6. Positive outer source and positive core target

Take \(\lambda=g\). The outer source functional \(L_O-gb\)
decreases to its diagonal value \(-.09-.084c_o\). The target
functional is
\[
 -K a_c+(K-g\cos x)A-g(1+\sin x)B.
\]
It decreases along the core boundary, since its \(A\) coefficient
is positive, its \(B\) coefficient negative, and \(A\) is
nonincreasing with \(B\). Its minimum is at \((d,d)\). Thus
\[
 \mathcal C\ge F(x):=\phi-.09-.084c_o-L_C(d,d)
                          +gW-gd(\cos x+\sin x).
\]
At zero, \(F(0)>\pi/2-.49344>1.077355\). For \(x=-z\),
\[
 F(-z)-F(0)=-z+g(.5-d)(\cos z-1)+g(.5+d)\sin z\ge0,
\]
because the cosine term is nonnegative and
\(g(1.05)(.9)>1\). For \(x\ge0\), the difference is at least
\(x-g(d-.5)\sin x\ge(1-.06g)x\ge0\).
This finishes every case on the secondary axis.

## 4. The source negative-primary axis

The separator (4) is independent of the source sign. For a positive
target it is therefore enough to prove the negative-source case: changing
the source sign adds \(2L_s\ge0\). With a negative target and a
positive source, (10) already applies.

### 4.1. Both states outer

For a positive target and negative source, the whole-interval hand
theorem QUARTER_ONE_OUTER_OPPOSITE_HAND_PROOF.md proves (2).
For both signs negative, use the separate hand corollary
QUARTER_ONE_OUTER_NEGATIVE_PRIMARY_HAND_COROLLARY.md. It proves
\[
 \mathcal C>39463631/50000000>.785
\]
by an outer endpoint support and two nonnegative trigonometric
differences, as proved in Section 2.9 of
QUARTER_ZERO_ALL_BOUNDARY_STATES_HAND_PROOF.md. These two source-primary
regimes are not inferred by interchanging the source axes.

### 4.2. Core source, positive outer target

It is enough to take \(\sigma=-1\). If \(x\le0\), (4) is
impossible since its left side is at most \(a_c<W\).
For \(x\ge0\), (4) implies
\[
 B\le\tfrac1{12}\sec x+(a_o-.5)\tan x-.5
 <1.22x-\tfrac7{18}.                                     \tag{18}
\]
Here \(\cos x>.75\), \(\sin x\le x\), and
\(a_o-.5<.915\) give the final bound \(1.22x-7/18\).
By (6)--(7),
\[
 \mathcal C>\pi/2+x-.842-B
 >\pi/2+7/18-.842-.22x
 \ge\pi/2+7/18-.996>.785.                                 \tag{19}
\]

### 4.3. Core source and outer target, both negative

Use \(L_C<.84\) and \(L_O>B-.019\). If \(x=-z\le0\),
(4) implies
\[
 B\cos z\ge W-a+A\sin z
 \ge-\tfrac1{12}+\tfrac12\cos z+1.399\sin z>0.
\]
Since \(\cos z\le1\), the last expression also bounds \(B\)
from below. Hence
\[
 \mathcal C>\pi/2-.859-\tfrac1{12}-z
                         +\tfrac12\cos z+1.399\sin z.
\]
Relative to its value at zero, the variable part is at least
\[
 z\left[.399-z/4-(1.399/6)z^2\right]\ge0
 \qquad(0\le z\le.7),
\]
so the cost exceeds \(\pi/2-.859-1/12+.5>1.1284\).
For \(0\le x\le.1\), (4) gives
\(B\ge1-a_c-1.415(.1)>0\), and therefore
\[
 \mathcal C>\pi/2-.859+1-a_c-.1415>.785.
\]
For \(x\ge.1\), simply use
\(\mathcal C\ge\phi-.84>\pi/2+.1-.84>.785\).

### 4.4. Outer source and core target, both negative

Subtract \(g\) times the margin in (4). The source's full-circle
support is
\[
 .09+(p+q+g)/2-R\sqrt{(p+g)^2+q^2}.
\]
The target functional satisfies
\[
 L_C-gA\sin x-gB\cos x
 =K(a_c-A)-gA\sin x+gB(1-\cos x)
 \ge-ga_c\sin x+gB(1-\cos x),                             \tag{20}
\]
because \(K+g\sin x>0\) and \(A\le a_c\).
For \(x\ge0\), the resulting difference from \(F_0\) is at least
\[
 x+(g/2)(\cos x-1)-(g/12)\sin x
 \ge x[1-g/12-.7g/4]\ge0.                                \tag{21}
\]
For \(x=-z\), it is at least
\[
 h(z)+gB(1-\cos z),\qquad
 h(z)=-z+(g/2)(\cos z-1)+(13g/12)\sin z.                  \tag{22}
\]
On \([0,.6]\), Taylor bounds give
\[
 h(z)\ge z[13g/12-1-gz/4-(13g/72)z^2]\ge0.
\]
On \([.6,.7]\), \(h''=-(g/2)\cos z-(13g/12)\sin z<0\);
its endpoint values, by the same Taylor polynomials, give
\(h(z)>-.025\). Separation supplies the needed additional term:
\[
 B\cos z\ge W-a+A\sin z
 >1.1945-1.415+.558(.564)=.094212.
\]
Here \(W\ge W(.6)>1.1945\), \(\sin(.6)>.564\), and
\(.825<\cos(.6)<.826\). Thus \(B>.11\), and
\(1-\cos z>.174\). Equations (14), (22) yield
\[
 \mathcal C> .792269-.025+g(.11)(.174)
             =.78954796>.785.                             \tag{23}
\]

### 4.5. Outer source, positive core target on the corner

Take the worst source sign \(\sigma=-1\). Here \(B\ge.5\).
For \(x=-z\le0\), the left side of (4) is at most
\(1.415-.5(\sin z+\cos z)<W\), so this is impossible.
For \(0\le x\le.3\), (4) would require
\[
 a\ge W-A\sin x+B\cos x
 \ge .5+\cos x-\tfrac1{12}\sin x
 \ge1.5-.3^2/2-.3/12=1.43>1.415,
\]
also impossible. Thus \(.3<x\le.7\). Combine the same lower
bound on \(a\) with (8) to obtain
\[
 b<\frac{533}{350}-\frac{10}{7}\cos x+\frac5{42}\sin x.
\]
Using (6)--(7), \(\cos x\ge1-x^2/2\), and \(\sin x\le x\),
\[
 \mathcal C>P(x):=\pi/2-.842-\frac{33}{350}
                       +\frac{37}{42}x-\frac57x^2.         \tag{24}
\]
This quadratic is concave. Its values at \(.3\) and \(.7\)
exceed \(.8345\) and \(.9011\), respectively. Therefore (2)
holds on the entire core corner.

### 4.6. Outer source, positive core target on the side

Now \(A=a_c\), \(0\le B\le.5\), again with \(\sigma=-1\).
Subtracting \(g\) times (4)'s margin and using the source circle
support gives
\[
 \mathcal C\ge F_0+x+(g/2)(\cos x-1)+(g/2)|\sin x|
                -(7g/12)\sin x-gB(1-\cos x).              \tag{25}
\]
If \(x\ge0\), the difference from \(F_0\) is at least
\[
 x[1-g/12-.7g/2]\ge0.
\]
If \(x=-z\), that difference is
\[
 -z+g(.5+B)(\cos z-1)+(13g/12)\sin z.                     \tag{26}
\]
First, feasibility requires \(z<.5\). Indeed, since \(B\ge0\),
(4) would otherwise require
\[
 a\ge .5+(13/12)\sin z+.5\cos z>1.415
 \qquad(.5\le z\le.7).
\]
The right side increases on that interval, and its lower Taylor bound
at \(.5\) already exceeds \(1.4565\).

For \(0\le z\le.4\), use \(A\ge B\) and
\(\sin z+\cos z\ge1\) in (4) to get \(a-B\ge1\), so
\(B<.415\). Expression (26) is then at least
\[
 z[13g/12-1-(.915g/2)z-(13g/72)z^2]\ge0;
\]
the bracket decreases and is positive at \(.4\).

For \(.4\le z<.5\), (4) gives the sharper bound
\[
 B\cos z<.915-(13/12)\sin z-.5\cos z.
\]
The subtracted expression increases on this interval. At \(.4\),
its lower Taylor estimate gives an upper numerator
\[
 .915-(13/12)(.4-.4^3/6)-.5(1-.4^2/2)
 =.033222\ldots <.04(.875).
\]
As \(\cos z\ge.875\), we have \(B<.04\). The \(B=0\)
part of (26) is \(h(z)\ge0\) by the Taylor estimate in Section 4.4.
Thus the whole difference is greater than
\(-g(.04)z^2/2\ge-g/200\). From (14),
\[
 \mathcal C> .792269-.00582=.786449>.785.                   \tag{27}
\]

## 5. Explicit coverage and arithmetic audit

Each cell below names a proof section. The sign order is source, target.
For the negative-primary axis, “increase” means adding \(2L_s\ge0\)
to its negative-source proof. No unlisted sign or boundary type remains.

| Axis | Source/target | ++ | +- | -+ | -- |
|---|---|---|---|---|---|
| Secondary | C/C | 2.1 | 2.1 | 2.1 | 2.1 |
| Secondary | C/O | 3.3 | 2.1 | 3.3 | 3.5 |
| Secondary | O/C | 3.6 | 2.1 | impossible, 3.2 | impossible, 3.2 |
| Secondary | O/O | 3.1 | 2.1 | 3.4 | 3.5 |
| Negative primary | C/C | 2.1 | 2.1 | 2.1 | 2.1 |
| Negative primary | C/O | 4.2, increase | 2.1 | 4.2 | 4.3 |
| Negative primary | O/C | 4.5--4.6, increase | 2.1 | 4.5--4.6 | 4.4 |
| Negative primary | O/O | 4.1, increase | 2.1 | 4.1 | 4.1 |

The exact reflection/reversal in Section 1 covers the retained target
axes as well. Closed side/corner junctions and \(x=0\) occur in the
stated closed intervals; tied axes may be assigned to any valid row.

The optional replay verify_quarter_one_all_boundary_hand.py verifies
80 displayed strict rational comparisons and records the nine envelope
endpoint bounds. The two cited outer-primary proofs have their own
fixed rational replays. These computations are direct arithmetic checks
of the hand proof, with no sampled or adaptively subdivided premise.
This proves (2). \(\square\)
