# Intermediate order also holds at the aligned-HG negative-primary endpoint

## 1. Necessary-system theorem

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad h=7/10,
 \quad \lambda=1/\sqrt{Q-1},\quad S_0=2\sqrt{Q-1}-3,
 \quad p=50/49,\quad K=13/12.
\tag{1}
\]
Retain a sorted true-core necessary cycle at ceiling \(q\le Q\),
with real frame spread at most h. H,A have nonnegative signed
tangents, B,D,E have nonpositive signed tangents, G has normal
negative tangent, and T has arbitrary signed tangent. Retain
\[
 HG,AB,TD\in\{0,2\},\quad GA1,\quad BT2,
 \qquad DE\in\{2,3\},\quad EH\in\{0,1\},
\tag{2}
\]
as well as the original implication \(TD0\Longrightarrow y_T>0\)
when the system is stated independently of an original candidate.
Assume
\[
       \theta_H=\theta_G>\theta_A,
       \qquad\text{actual GA0 is unavailable}.
\tag{3}
\]

**Order theorem.** Then
\[
                           \theta_H=\theta_G>\theta_T.
\tag{4}
\]
The proof retains every original state and frame. It assumes
neither AB nor TD alignment, any T sign, nor either E-primary
total. It does not itself align AB or supply GA0.

The middle estimate needed for (4) is the following extension
of the signed hard-middle estimate. Put \(g=b_G\), and suppose
\(r=\theta_T-\theta_G\ge0\). Then either actual AB owner gives
\[
                           g+y_T\le S_0+\tfrac34 r.
\tag{5}
\]
Its proof uses only the three actual GA1/AB/BT2 inequalities
and the A/B circles, together with the local negative-primary
cuts derived next.

## 2. Local cuts and elementary constants

Write \(t=\theta_G-\theta_A>0\). The genuine-negative GA1
comparison gives \(b_G<.156<1/2\), and hence true-core
avoidance gives \(a_G\ge7/12\). Aligned HG gives
\(b_H+b_G\ge1\), so \(b_G>.1\). The same comparison therefore
gives
\[
 1+(b_G+1/2)^2+K^2+2(b_G+1/2)\cos t+2K\sin t<Q,
 \qquad 0<t<9/100.
\tag{6}
\]
These are the local comparisons in Sections 2--3 of the
[aligned-HG negative-GA transport](HAND_G5_GLOBAL_PRIMARY_ENTRY_ALIGNED_HG_NEGATIVE_GA_EH0.md).
They use no EH owner or E-frame restriction.

For later use set
\[
 e=\sec t,\quad \tau=\tan t,
 \qquad 1\le e<201/200,
 \quad 0\le\tau<91/1000,
 \quad .585<\lambda<.586,
 \quad R<1.979.
\tag{7}
\]
The secant and tangent bounds follow from the alternating
Taylor bounds at .09. The two exact lambda-square reserves are
\[
 1-(.585)^2(Q-1)=220879/100000000,
 \qquad (.586)^2(Q-1)-1=753361/625000000.
\]
The special choice of lambda has the useful exact identity
\[
                         R\lambda/\sqrt{1+\lambda^2}=1.
\tag{8}
\]

Translate G's frame to zero and set
\[
 \theta_A=-t,\quad\theta_T=r\ge0,\quad
 d=\theta_B-\theta_A,\quad u=\theta_B-\theta_T,
 \qquad s=t+r=d-u\in[0,h].
\tag{9}
\]
Every individual angle in (9) has absolute value at most h.
Let \(W(z)=(1+\cos z+|\sin z|)/2\), and let
\(X_i=a_i+1/2,\ Y_i=b_i+1/2\) denote the middle corners.

## 3. AB0: one decreasing primary contribution

The actual GA1 inequality gives
\[
          g\le a_A\sec t-(7/12)\tan t-W(t)\sec t.
\tag{10}
\]
Add to this the actual BT2 inequality and lambda times the
nonnegative actual AB0 margin. Apply the A and B circle
supports once each. The resulting exact upper bound is
\[
 \begin{split}
 g+y_T\le{}&A(t)+R\sqrt{1+\lambda^2+2\lambda\sin s}
                   -1-\lambda-K_s(d),\\
 A(t)&=R\sqrt{\sec^2t+\lambda^2}-\sec t-K\tan t,\\
 K_s(d)&=\cos(d-s)+(-\sin(d-s))_+
                   +\lambda\{\cos d+(\sin d)_+\}.
 \end{split}
\tag{11}
\]
All half-shifts are included. For example the A force is
\((\sec t,\lambda)\); the B force is
\((\lambda\sin d+\cos u,\lambda\cos d-\sin u)\), whose
squared norm is \(1+\lambda^2+2\lambda\sin s\).

The whole-interval endpoint comparison in Section 3 of
[the signed hard-middle theorem](HAND_G5_SIGNED_INTERMEDIATE_ORDER_WITH_ALL_MIXED_OWNERS.md)
proves, for these same angles and lambda,
\[
                         K_s(d)\ge1+\lambda(\cos s+\sin s).
\tag{12}
\]
That comparison is a scalar identity and concavity argument;
it requires no hard-quarter witness or radial change.

The square-root tangent and (8) give
\[
 R\{\sqrt{1+\lambda^2+2\lambda\sin s}
                     -\sqrt{1+\lambda^2}\}\le\sin s.
\]
The zero-angle constant in (11) is precisely S_0. Hence
\[
 g+y_T-S_0\le A(t)-A(0)+J(t+r),
 \quad J(z)=(1-\lambda)\sin z+\lambda(1-\cos z).
\tag{13}
\]
On the entire interval in (6),
\[
 \begin{split}
 A'(t)
 &=e\tau\left(\frac{Re}{\sqrt{e^2+\lambda^2}}-1\right)-Ke^2\\
 &<(1.005)(.091)(.979)-K<-3/4.
 \end{split}
\tag{14}
\]
Also, on \([0,h]\),
\[
 J'(z)\le\sqrt{(1-\lambda)^2+\lambda^2}<3/4,
\tag{15}
\]
since \((.415)^2+(.586)^2<(3/4)^2\). With J(0)=0,
(13)--(15) imply (5), strictly when t>0.

## 4. A whole-angle norm comparison for the other AB owner

The following elementary comparison will control the negative
AB2 sector. If
\[
 .582\le\rho\le.586,\qquad 0\le z\le h,
 \quad n_0=\sqrt{1+\rho^2},
 \quad n=\sqrt{1+\rho^2-2\rho\sin z},
\]
then
\[
 \frac{1-\rho\sin z}{n}\le\frac1{n_0},
 \qquad
 R\frac{\cos z}{n}-\sin z\le\frac R{n_0}.
\tag{16}
\]

For the first inequality, positive squaring reduces it to
\((1+\rho^2)\sin z\le2\rho\). This follows already from
\(\sin z<.65\), \(2\rho\ge1.164\), and
\(1+\rho^2\le1.343396\).

For the second inequality let \(w=\sin z\). Rationalizing
the positive cosine difference reduces it, for w>0, to
\[
 R\{2\rho-(1+\rho^2)w\}
                  \le n n_0(n_0\cos z+n).
\tag{17}
\]
The brace is positive by the same bounds. The radical n is
concave in w. At w=0 and w=13/20 its values exceed 23/20
and 19/25 respectively; the endpoint square checks use
\(1+(.582)^2>(23/20)^2\) and
\(1+(.586)^2-2(.586)(13/20)>(19/25)^2\).
Thus
\[
                 n\ge23/20-(3/5)w,\quad n_0>23/20,
                 \qquad\cos z\ge1-w^2.
\]
The right side of (17), less the left side, consequently
exceeds
\[
 \begin{split}
 &\frac{23}{20}\left(\frac{23}{20}-\frac35w\right)
        \left\{\frac{23}{20}(1-w^2)
                      +\frac{23}{20}-\frac35w\right\}\\
 &\hspace{5mm}-1.979\{1.172-(1+.582^2)w\}\\
 &=\frac{361181}{500000}
   +\frac{67208699}{250000000}w
   -\frac{1771}{1600}w^2+\frac{1587}{2000}w^3\\
 &\ge\frac{361181}{500000}
                -\frac{1771}{1600}(13/20)^2
   =\frac{4075317}{16000000}>0.
 \end{split}
\tag{18}
\]
The comparison at z=0 is equality. This proves (16) on
one entire interval, without an angle partition.

## 5. AB2: move only the scalar comparison angle to zero

Write \(\beta=\theta_B\), so \(d=\beta+t\) and
\(u=\beta-r\). The same weights as in Section 3 give
\[
 \begin{split}
 g+y_T\le{}&R N_A(t,\beta)+R N_B(u)
 -\sec t-K\tan t-1-\cos u-(-\sin u)_+\\
 &\hspace{28mm}-\lambda\{1+\cos(\beta+t)
                                         +(\sin(\beta+t))_+\},\\
 N_A(t,\beta)^2&=\sec^2t+\lambda^2
                                      +2\lambda\sec t\sin(\beta+t),\\
 N_B(u)^2&=1+\lambda^2-2\lambda\sin u.
 \end{split}
\tag{19}
\]
The A force is \((\sec t+\lambda\sin d,\lambda\cos d)\),
and the B force is \((\cos u,\lambda-\sin u)\).

Fix the actual B and T frame values \(\beta,r\), and vary
only the scalar argument t in (19) down to zero. This is
an inequality between explicit dual expressions, not a claim
that a new A witness has been constructed. The reference
frame zero is the existing G frame, so every comparison
angle stays in the original frame interval.

The t-dependent part of (19) is
\[
 D(t)=R N_A(t,\beta)-\sec t-K\tan t
       -\lambda\{\cos(\beta+t)+(\sin(\beta+t))_+\}.
\tag{20}
\]
We prove \(D'(t)<-1/100\) on each differentiable piece.
Put \(d=\beta+t\), \(C=e+\lambda\sin d\),
\(S=\lambda\cos d\), and \(N=\sqrt{C^2+S^2}\). Then
\[
 D'=\frac{Re}{N}(\tau C+S)-e\tau-Ke^2
             +\lambda\sin d-\lambda\cos d\,\boldsymbol1_{d>0}.
\tag{21}
\]

If d<=0, set \(z=-d\) and \(\rho=\lambda/e\).
The bounds (7) give \(.582<\rho<.586\), so (16) applies.
Its two inequalities give
\[
 D'\le\frac{Re\lambda}{\sqrt{e^2+\lambda^2}}
       +e\tau\left(\frac{Re}{\sqrt{e^2+\lambda^2}}-1\right)
       -Ke^2.
\tag{22}
\]
By (8), the first term is at most e<1.005. The ratio in
the second term is less than 1.73, since
\[
 1.73(1.15)-1.979(1.005)=121/200000>0.
\]
Consequently
\[
 D'<1.005+(1.005)(.091)(.73)-K
                   =-694271/60000000<-1/100.
\tag{23}
\]

If d>=0, use \(C/N\le1\),
\(N\ge\sqrt{e^2+\lambda^2}\), and (8) in (21):
\[
 D'\le e\tau(R-1)+(e-\lambda)\cos d+\lambda\sin d-K.
\]
The first term is less than .09. The next two are at most
\(\sqrt{(.420)^2+(.586)^2}<.722\). Thus
\[
                           D'<.812-K<-1/4.
\tag{24}
\]
The two one-sided expressions meet continuously at d=0,
and both have negative derivative. Hence \(D(t)\le D(0)\).

At t=0 the right side of (19) is exactly the fixed-weight
hard-middle upper expression with GA0 error zero, AB2,
and the same B/T frames. Section 4 of the signed hard-middle
theorem bounds that scalar expression by \(S_0+(3/4)r\).
Its proof is a norm and width comparison with the same
weights \((1,\lambda,1)\); applying it here asserts no
feasibility of the reference state. Thus (19)--(24) prove
(5) also for actual AB2, including its weak ties.

## 6. The unchanged outer charges exclude reversed intermediate order

The signed TD zero-edge estimate is
\[
                y_T+b_D\ge1-p(\theta_D-\theta_T).
\tag{25}
\]
It holds for either actual T sign, using the retained
TD0 sign implication when needed, exactly as in Section 5
of the signed hard-middle theorem. Aligned HG gives
\(b_H+g\ge1\).

Suppose \(r=\theta_T-\theta_H\ge0\), and put
\(\alpha=\theta_H-\theta_D\). Adding (25), the aligned HG
inequality, and (5) gives
\[
 2\le b_H+b_D+S_0-p\alpha-(p-3/4)r
       \le b_H+b_D+S_0-p\alpha.
\tag{26}
\]
The whole all-mixed H/D/E estimate gives
\[
                         b_H+b_D+S_0-p\alpha<2.
\tag{27}
\]
It uses only the unchanged H,D,E states, their actual
circles, true core, signed tangents, frame interval and
the two actual mixed witnesses. There is no GA or T-sign
assumption in that estimate. Equations (26)--(27) contradict
each other and prove (4).

This is an original-data order theorem. No intermediate,
anchor, owner or frame was changed. The only extra local
input beyond the hard-order theorem is the actual short
negative-primary cut (6), and every new comparison is proved
on its whole interval by the displayed algebra and rational
reserves.
