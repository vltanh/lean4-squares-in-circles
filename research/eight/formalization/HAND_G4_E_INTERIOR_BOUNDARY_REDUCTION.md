# An E-interior boundary reduction for the aligned-zero hard-owner class

## 1. What is reduced, and what remains fixed

Put \(Q=9789/2500\). Consider the aligned-zero hard-quarter
class with original signs
\[
 (y_H,y_G,y_A,y_B,y_T,y_D,y_E)
   =(b_H,-b_G,b_A,-b_B,b_T,-b_D,-b_E),\qquad b_i\ge0,
\]
and original own-frame bounds
\[
 a_i\ge b_i,\qquad
 (a_i+1/2)^2+(b_i+1/2)^2\le Q.
\]
Use the frames and nonnegative angles
\[
 \theta_H=\theta_G=t,\quad\theta_A=\theta_B=0,
 \quad\theta_T=\theta_D=-u,
\]
\[
 \theta_E=-u+\delta,
 \qquad \epsilon=t+u-\delta,
 \qquad t,u,\delta,\epsilon\ge0,
 \qquad\alpha:=t+u=\delta+\epsilon\le7/10.                     \tag{1}
\]
Retain original transverse witnesses on HG, AB and TD, original
axis 0 on GA, axis 2 on BT, axis 3 on DE and axis 1 on EH.
These signs, alignments and owners are hypotheses of this note.

The theorem has the same conclusion for the weaker five-anchor
system in which G and T are omitted. Keep only H, A, B, D and E,
their stated signs, sorting, circles and frames, and assume
\[
\begin{split}
 b_H+a_A\cos t-b_A\sin t&\ge1+W(t),\\
 a_B\cos u-b_B\sin u+b_D&\ge1+W(u),\\
 b_A+b_B&\ge1,
\end{split}
\]
together with the two mixed inequalities in (2). These are the
composites of HG with GA and BT with TD at aligned outer zero
edges. Every estimate below uses precisely these composites and
the five retained circles; it never needs replacement G or T
centers. In this formulation only the four non-E anchors are fixed.

One may also replace each containing-circle ceiling Q by any
common actual ceiling \(q\le Q\) throughout the hypotheses and
the E relaxation. All uniform estimates below continue to use Q.
The minimizing E state then remains within q, while every fixed
A/B corner value, including a strict loss below q inherited from
a previous reduction, is retained without alteration.

Fix all six non-E vertices and their frames. Their original values
are never changed in the estimates below. Form the auxiliary E
relaxation consisting of \((a,b,\delta,\epsilon)\) with
\[
\begin{gathered}
 a\ge b\ge0,\qquad (a+1/2)^2+(b+1/2)^2\le Q,\\
 \delta,\epsilon\ge0,\qquad\delta+\epsilon=\alpha,\\
 a_D+a\sin\delta+b\cos\delta\ge W(\delta),\\
 a_H+a\sin\epsilon-b\cos\epsilon\ge W(\epsilon),\qquad
 W(z)=\frac{1+\cos z+\sin z}{2}.                              \tag{2}
\end{gathered}
\]
The actual E state is a member of this relaxation. Extra physical
gap and core conditions may be omitted here because (2) is used
only as a necessary relaxation. The same two original axis
formulas are retained throughout.

**Boundary-reduction theorem.** If (2) is nonempty, the minimum of
\((a+1/2)^2+(b+1/2)^2\) over (2) has at least one of
\[
                         b=0,\qquad\delta=0,
                              \qquad\epsilon=0.              \tag{3}
\]
Thus this particular E-interior relaxation does not require a
separate interior orientation minimum. The E-zero alternative is
excluded by `HAND_G5_E_ZERO_HARD_QUARTER_SPLIT_EXCLUSION.md` when
joined to the fixed six-vertex data above.

This is an auxiliary variational reduction, not an assertion that
the original E center has one of the properties in (3). It does
not move any original vertex in a later equality claim. The two
aligned mixed endpoints in (3), the other original owner/sign
classes and nonzero zero-edge errors remain to be controlled.

If the relaxation is additionally restricted by the bad-mismatch
condition \(S=u+\delta\ge s_0\), there is one further possible
boundary:
\[
                               S=s_0.                         \tag{4}
\]
It must not be discarded. In particular, (3) alone does not prove
that a bad-S minimum has E zero. With both reflected mismatch
conditions imposed, the analogous boundary \(t+\epsilon=s_0\)
must also be retained.

## 2. A short total-span bound from the actual A/B chain

Write
\[
 f(b)=\sqrt{Q-(b+1/2)^2}-1/2,
 \qquad C_0=\sqrt{Q/2}-1/2<.9.
\]
The original zero and hard-quarter witnesses give
\[
 a_A\cos t-b_A\sin t\ge1+W(t)-b_H,
 \qquad
 a_B\cos u-b_B\sin u\ge1+W(u)-b_D.                            \tag{5}
\]
Since \(b_H,b_D\le C_0\), the circular-cap formula gives
\[
 b_A+\tfrac12\le\mathcal L(t,C_0),\qquad
 b_B+\tfrac12\le\mathcal L(u,C_0),
\]
where
\[
 \mathcal L(z,B)=\cos z\sqrt{Q-(3/2-B+\cos z)^2}
                  -\sin z(3/2-B+\cos z).
\]
The exact factorization in Section 4 of
`HAND_G5_E_ZERO_HARD_QUARTER_SPLIT_EXCLUSION.md` proves that
\(z\mapsto\mathcal L(z,C_0)\) is convex and decreasing throughout
\([0,.7]\). That scalar lemma is independent of the E state.
Since the original AB witness gives \(b_A+b_B\ge1\), convexity
at the fixed total \(t+u=\alpha\) implies
\[
                2\le\mathcal L(0,C_0)+\mathcal L(\alpha,C_0).
                                                                    \tag{6}
\]
The cap increases with B. At \(z=.22\), alternating Taylor
bounds give
\[
 .9758<\cos z<.976,\qquad \sin z>.218,
 \qquad\sqrt{Q-(.6+\cos z)^2}<1.197.
\]
Therefore
\[
 \mathcal L(0,.9)<1.165,
 \qquad\mathcal L(.22,.9)
   <.976(1.197)-.218(1.5758)
    =\frac{2061869}{2500000}.
\]
Their sum is \(4974369/2500000<2\). Monotonicity in (6) proves
\[
                                  \alpha<.22.                 \tag{7}
\]

## 3. Quantitative primary-sum control and exclusion of E's other boundaries

Equation (5), \(W\ge1\), and the signs of sine and cosine give
\[
 a_A\ge2-b_H>1.1,\qquad a_B\ge2-b_D>1.1.
\]
Containment then gives \(b_A,b_B<.665\), because
\(1.6^2+1.165^2>Q\). The actual AB relation consequently gives
\[
                              .335<b_A,b_B<.665.              \tag{8}
\]
Adding the two inequalities in (5), before estimating their
common coordinates, gives
\[
\begin{split}
 b_H+b_D\ge{}&4-(a_A+a_B)
   +(b_A+\tfrac12)\sin t+(b_B+\tfrac12)\sin u\\
 &+(a_A-\tfrac12)(1-\cos t)
                  +(a_B-\tfrac12)(1-\cos u).
\end{split}
\]
The decreasing, strictly concave function f and AB imply
\(a_A+a_B\le2f(1/2)\). Thus, with
\(m_0=2-f(1/2)\),
\[
             \frac{b_H+b_D}{2}
                   \ge m_0+\frac{167}{400}\sin\alpha.        \tag{9}
\]
Here \(\sin t+\sin u\ge\sin(t+u)\) was used and the remaining
nonnegative terms were discarded.

Simple positive squaring gives
\[
 f(1/2)<1.20752,
 \qquad m_0>.79248,
 \qquad f(m_0)<.9984,
 \qquad f'(m_0)<-.86.
\]
For the first two nontrivial radius comparisons, the exact
reserves are
\[
 1.70752^2+1-Q=\frac{959}{39062500},\qquad
 1.4984^2+1.29248^2-Q=\frac{1046}{9765625}.
\]
Apply concavity again to H and D and then to the tangent line at
\(m_0\) in (9). This proves the useful shared-chain estimate
\[
             \boxed{\ a_H+a_D
                     <1.9968-.718\sin\alpha<2.\ }            \tag{10}
\]
The sharper coefficient from the calculation is .7181.

Also \(a_A,a_B<283/200\), so (5) gives
\(b_H,b_D>2-283/200>.5\). In particular \(a_H,a_D>.5\).
If \(\alpha=0\), (2) implies \(a_H+a_D\ge2\), contradicting
(10). We may henceforth suppose \(0<\alpha<.22\).

Every feasible point of (2), not merely its original member,
satisfies
\[
                                  a>1.05.                     \tag{11}
\]
To prove this, put \(T=\sin\delta+\sin\epsilon>0\). Add the two
mixed constraints, use (10), \(0\le b<C_0<.9\), and
\[
 \cos\delta+\cos\epsilon\ge1+\cos\alpha,
 \quad|\cos\delta-\cos\epsilon|\le1-\cos\alpha.
\]
The result is
\[
 (a-\tfrac12)T
    >.0032+.718\sin\alpha-1.4(1-\cos\alpha)
    >.5626\sin\alpha.
\]
For the last comparison use \(\tan(\alpha/2)<.111\).
Since \(T\le\sin\alpha/\cos(\alpha/2)\) and
\(\cos(\alpha/2)>.99\),
\[
                     a-\tfrac12>.5626(.99)>.55,
\]
which proves (11). Thus every feasible E point has
\(a>b\), since \(b<C_0<.9\). Neither a diagonal-coordinate
boundary nor a core-primary boundary can occur in the minimization.

## 4. At an interior E minimum, both original mixed contacts are active

The feasible set (2) is nonempty and compact. Minimize its corner
value
\[
                         q_E=(a+1/2)^2+(b+1/2)^2.
\]
Suppose a minimizer has \(b>0\) and \(\delta,\epsilon>0\).
By (11), all its primary and sorted-coordinate inequalities are
strict.

If only EH is active, decrease b slightly; EH improves, the
slack DE inequality remains valid, and \(q_E\) decreases. The
same decrease is possible if neither contact is active. If only
DE is active, use the small direction
\[
                         (da,db)=(-\cos\delta,\sin\delta).
\]
It preserves that exact DE contact, while
\[
 \tfrac12\,dq_E=-(a+1/2)\cos\delta
                     +(b+1/2)\sin\delta<0,
\]
because \(a>b\) and \(\delta<.22<\pi/4\). EH remains valid
for a sufficiently small step. These contradictions prove that
both original mixed inequalities are equalities at such a minimizer.

## 5. The exact E orientation function is strictly concave

Fix the unchanged H and D primaries. Write
\[
 d_0=a_D-\tfrac12>0,\qquad h_0=a_H-\tfrac12>0,
 \qquad m=d_0+h_0<1,
 \qquad n=h_0-d_0,\quad |n|<1,
\]
\[
 \omega=\alpha/2,
 \qquad\zeta=(\epsilon-\delta)/2,
 \qquad -\omega\le\zeta\le\omega.
\]
Set
\[
 A=\tfrac12\cot\omega,
 \quad B=\tfrac12\tan\omega,
 \quad M=\frac{m}{2\sin\omega},
 \quad N=\frac{n}{2\cos\omega}.
\]
Solving the two contact equalities in Section 4 gives
\[
 U=A\cos\zeta-M,
 \qquad V=B\sin\zeta+N,
\]
\[
 x:=a-\tfrac12=U\cos\zeta-V\sin\zeta,
 \qquad b=U\sin\zeta+V\cos\zeta.                            \tag{12}
\]
The determinant of the two contact equations is
\(-\sin\alpha\ne0\), so this is a smooth, uniquely determined
contact curve. Its corner function is exactly
\[
\begin{split}
 q_E(\zeta)={}&(A^2+2A)\cos^2\zeta
               +(B^2-2B)\sin^2\zeta
               +(A+B)\sin\zeta\cos\zeta\\
 &+[-2M(A+1)+N]\cos\zeta
             +[2N(B-1)-M]\sin\zeta
             +M^2+N^2+\tfrac54.
\end{split}                                                     \tag{13}
\]
The expression is the actual corner formula on any portion where
\(b\ge0\); the possibility of a sign change is the boundary
\(b=0\) already retained in the theorem.

Using \(A+B=\csc\alpha\) and \(A-B=\cot\alpha\), ordinary
differentiation yields
\[
\begin{split}
 \sin\alpha\,q_E''={}&-2(\cot\alpha+2)\cos(2\zeta)
                           -2\sin(2\zeta)\\
 &+m\cos\omega[(\cot\omega+2)\cos\zeta+\sin\zeta]\\
 &-n\sin\omega[\cos\zeta+(\tan\omega-2)\sin\zeta].
\end{split}                                                     \tag{14}
\]

The apparent large cotangent terms cancel uniformly. Put
\(c=\cos\omega\), \(s=\sin\omega\). Since
\(|\zeta|\le\omega\),
\[
 -2\cot\alpha\cos(2\zeta)
         +\cos\omega\cot\omega\cos\zeta
 \le\frac{c^2-(2c^2-1)^2/c}{s}\le3s.                        \tag{15}
\]
For the final inequality multiply by the positive cs. Its
difference factors as
\[
 c^3-(2c^2-1)^2-3c(1-c^2)
             =(c-1)(-4c^3+4c+1)\le0.
\]
The factor on the right other than \(c-1\) is
\(1+4c(1-c^2)>0\).

Use \(0<m<1\), \(|n|<1\), \(0<\tan\omega<2\), and
\(|\sin\zeta|\le\sin\omega\) in the remaining terms of (14).
Together with (15) this gives
\[
 \sin\alpha\,q_E''
   \le5\sin\omega+2\sin^2\omega
                     +2\sin\alpha+2-4\cos\alpha.
\]
Finally \(\omega<.11\), \(\alpha<.22\), and
\(\cos\alpha>1-.22^2/2=.9758\) prove the uniform strict bound
\[
 \boxed{\ \sin\alpha\,q_E''
   <5(.11)+2(.11)^2+2(.22)+2-4(.9758)
    =-\frac{889}{1000}<0.\ }                                 \tag{16}
\]
No angle subdivision, fitted weight, or numerical stationary point
is used in this concavity proof.

## 6. Finish the boundary reduction and retain the mismatch boundary

At the supposed interior minimizer from Section 4, the contact
curve (12) locally preserves both original equalities. The
conditions \(b>0\), \(a>b\), and the strict primary bound (11)
remain valid for a sufficiently short variation. Strict concavity
(16) supplies a nearby point with smaller corner value, also
satisfying the upper circle bound Q. This contradicts minimality.
Hence every minimum has one of the three boundaries in (3).

For an additional condition \(S=u+\delta\ge s_0\), repeat the
same argument inside its closed feasible subinterval. The local
variation is available unless its endpoint \(u+\delta=s_0\)
is active. This proves the explicitly enlarged list (3)--(4).
The same reasoning retains both mismatch endpoints if the
reflected condition is imposed as well.

This theorem supplies a continuous E-interior reduction only in
the original hard-owner class stated in Section 1. It leaves the
aligned mixed endpoints and, when relevant, the explicit mismatch
boundary as genuine remaining cases. It does not prove that all
candidate cycles enter this class or that the original E state
can be replaced in a terminal equality statement.
