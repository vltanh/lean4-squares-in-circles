# Whole-angle concentration for the TD2 extension of the secondary-owner chain

## 1. Scope and the resulting scalar obligation

Retain the original G0--G2 cycle and the hypotheses on the four
sorted outer states H, G, B and D from
HAND_G3_HIGH_GA_LOW_EH_SECONDARY_OWNER_FOUR_CIRCLE_EXCLUSION.md.
Their signed tangents are respectively positive, negative, negative
and negative. A, T and E may have either sign and either radial kind.
The original owners in the present note are

\[
 GA=2,\quad AB=0,\quad BT=2,\quad TD=2,\quad
 DE=2,\quad EH=0,\qquad HG\in\{0,2\}.
\tag{1}
\]

Use

\[
 \begin{gathered}
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad h=\frac7{10},\quad
 a_0=\sqrt{Q-\frac14}-\frac12,\quad
 c_0=\sqrt{Q/2}-\frac12,\\
 W(t)=\frac{1+\cos t+|\sin t|}{2},\qquad
 \phi(t)=\cos t+\sin t\quad(0\le t\le h),\\
 S(f,g)=\max_{0\le b\le c_0}
       \left\{f\left(\sqrt{Q-(b+\frac12)^2}-\frac12\right)+gb\right\},\\
 \overline S(f,g)=R\sqrt{f^2+g^2}-\frac{f+g}{2}.
 \end{gathered}
\tag{2}
\]

The complete G1 total-variation bound, proved in Section 2 of
HAND_G3_GLOBAL_BT0_DE2_PATH_EXCLUSION.md, is

\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+<h.
\tag{3}
\]

The first conclusion of this note is that the original TD error
must be **strictly positive**. This excludes the entire nonpositive
TD2 branch.

For the remaining branch put \(z=d_{TD}>0\) and fix

\[
 \eta=\frac{293}{1000},\qquad
 m=c(\cos z+\eta\sin z),\qquad
 \sigma=R\sqrt{1+\eta^2}-\frac{1+\eta}{2}.
\tag{4}
\]

The free positive weights \(k,l,c\) may depend on \(z\). The
concentration theorem requires exactly

\[
 \frac12\le k\le\frac{17}{20},\qquad
 k\le c\le2,\qquad k\le l\le2k,\qquad
 \frac12\le\frac lm\le2.
\tag{5}
\]

There are three unordered coefficient pairs:

\[
 (p_G,q_G)=(k,l),\qquad
 (p_H,q_H)=(k,1),\qquad
 (p_B,q_B)=(\min(l,m),\max(l,m)).
\tag{6}
\]

For any of these pairs write

\[
 \begin{split}
 N_i(s)&=\sqrt{p_i^2+q_i^2+2p_iq_i\sin s},\\
 U_i(t)&=p_i\{\phi(t)-1\}
                  -R\{N_i(t)-N_i(0)\},\\
 V_i(t)&=q_i(\cos t-1)
                  -R\{N_i(-t)-N_i(0)\},\\
 M_i(z)&=p_i\{\phi(h-z)-1\}+q_i(\cos h-1)
                  -R\{N_i(-z)-N_i(0)\}.
 \end{split}
\tag{7}
\]

The exact scalar baseline is

\[
 \begin{split}
 B(z)={}&k+2l+m+cW(z)+2-c\sigma\sin z\\
 &-\overline S(1,k)-\overline S(l,k)
        -\overline S(m,l)-S(1,c).
 \end{split}
\tag{8}
\]

In particular the actual sorted D support at zero is retained.
The B support in (8) is deliberately the complete-circle bound,
also when \(l>m\).

Define

\[
 \begin{split}
 {\cal E}(z)=\min\bigg\{&
       \min_{i\in\{G,H,B\}} V_i(z),\
       \min_{i\in\{G,H,B\}} M_i(z),\\
 &\min\left\{U_G(h-z),U_H(h-z),U_B(h-z),
                       -(c_0-\tfrac12)(h-z)\right\}
       +\min_{j\in\{G,H,B\}}V_j(h)\bigg\}.
 \end{split}
\tag{9}
\]

**Concentration conclusion.** Every feasible original cycle (1)
with \(0<z<h\) satisfies, for every choice (4)--(5),

\[
                         B(z)+{\cal E}(z)\le0.
\tag{10}
\]

This is a whole-angle reduction. The scalar alternatives in (9)
are the intrinsic cases with one negative angle \(-z\), or with
total positive variation \(h\) and one positive angle \(h-z\)
balanced by one negative angle \(-h\). No hypothesis that the
original angles have either form is used.

This note proves (10), and the nonpositive-TD exclusion. A separate
choice of continuous weights and a proof that (10) is impossible
on \(0<z<h\) are still required to exclude the full positive-TD2
subclass. No such scalar conclusion is asserted here.

## 2. Exact TD2 force and the nonpositive branch

Write the errors in cyclic order as

\[
 (v,u,a,x,z,d,r)
 =(d_{HG},d_{GA},d_{AB},d_{BT},d_{TD},d_{DE},d_{EH}).
\]

Give the original inequalities the weights

\[
                             (k,l,l,m,c,1,1).
\tag{11}
\]

The signed coordinates of A and E cancel. The four sorted outer
forces for HG0 are

\[
 \begin{split}
 F_H&=(\cos r,\ k+\sin r),\\
 F_G&=(l\cos u+k\sin v,\ l\sin u+k\cos v),\\
 F_B&=(m\cos x+l\sin a,\ l\cos a+m\sin x),\\
 F_D&=(\cos d,\ c+\sin d).
 \end{split}
\tag{12}
\]

For HG2 replace the first two forces by

\[
 F_H=(\cos r+k\sin v,\ k\cos v+\sin r),\qquad
 F_G=(l\cos u,\ l\sin u+k).
\tag{13}
\]

The remaining force on the signed T coordinates is exactly

\[
                 c\sin z\,a_T+(c\cos z-m)y_T.
\tag{14}
\]

First suppose \(z=-s\le0\). Choose

\[
                    k=\frac{31}{40},\quad
                    l=\frac{31}{20},\quad m=c=2.
\tag{15}
\]

Compare the stress (12)--(14) with the four-circle expression of
the cited secondary-owner note in which its TD variable is
algebraically set to zero. The four remaining force vectors are
then identical. This comparison is an identity of stress
expressions; it introduces no TD0 witness.

The other six original errors sum to \(s\). The charged bounds
of Sections 3--7 of that note therefore give a lower bound

\[
 .0627-.0576-.0044-\frac{21}{20}s
       =.0007-\frac{21}{20}s
\tag{16}
\]

for HG0, and the stronger
\(.0627-.0022-.0044-(21/20)s\) for HG2. Each of its two-error
hexagon bounds still applies by (3); its use does not require
the seven algebraic arguments to sum to zero.

Every original sorted boundary state has
\(a_T\ge |y_T|\) and \(a_T>447/800>1/2\), by the elementary
true-core/outer bounds in HAND_G3_FOUR_CUTS_AT_ONE_THIRTY_SECOND.md.
Consequently (14) is at most

\[
 \begin{split}
 2\{-a_T\sin s+y_T(\cos s-1)\}
 &\le-2a_T(\sin s+\cos s-1)\\
 &\le-(\phi(s)-1).
 \end{split}
\tag{17}
\]

The TD demand increases by \(2(W(s)-1)=\phi(s)-1\).
Thus the actual TD2 stress is at least the expression in (16)
plus \(2(\phi(s)-1)\).

The function \(\phi\) is concave on \([0,h]\), and
\(\phi(h)>1.409\). Hence

\[
 2(\phi(s)-1)-\frac{21}{20}s
 \ge\left(\frac{2(.409)}{.7}-\frac{21}{20}\right)s
 =\frac{83}{700}s\ge0.
\tag{18}
\]

The actual stress is therefore strictly positive. This contradicts
the original separating inequalities, proving \(z>0\).

For positive \(z\), (4) makes (14) equal to

\[
                        c\sin z(a_T-\eta y_T).
\tag{19}
\]

The actual corner \((a_T+\tfrac12,|y_T|+\tfrac12)\) lies in the
radius-\(R\) disk, for either radial kind. Therefore

\[
                         a_T-\eta y_T\le\sigma.
\tag{20}
\]

This proves the T term used in (8), with no sign restriction on T.

## 3. A uniform two-angle concavity lemma

Let \(0<p\le q\), \(p/q\ge1/2\), and set

\[
 A=p^2+q^2,\quad B=pq,\quad
 N(s)=\sqrt{A+2B\sin s},\quad C(s)=-RN''(s).
\]

On the entire interval \([-h,h]\), \(C\) is strictly increasing.
On \([0,h]\) it is concave. Indeed the derivative identities in
Section 3 of the secondary-owner note give

\[
 N'''(s)=-\frac{B\cos s}{N(s)^5}
 \{A^2-3B^2+AB\sin s+B^2\sin^2s\}.
\tag{21}
\]

Here \(2\le A/B\le5/2\) and \(\sin s>-.645\).
The braces divided by \(B^2\) are at least

\[
                  4-3-2(.645)+(.645)^2
                    =\frac{5041}{40000}>0.
\tag{22}
\]

The numerator of \(N''''(s)\), after removing its positive
factor \(B/N^7\), is

\[
 \begin{split}
 &B(4A^2-15B^2)+A(A^2-2B^2)t
       +B(10B^2-A^2)t^2\\
 &\hspace{35mm}+2AB^2t^3+B^3t^4,\qquad t=\sin s.
 \end{split}
\tag{23}
\]

Every coefficient is positive when \(2\le A/B\le5/2\).
This proves the claims about \(C\). In particular, with

\[
 C_0=\frac{RB^2}{A^{3/2}},\qquad
 C_1=\frac{RB(A^2-3B^2)}{A^{5/2}},
\]

one has

\[
 C(s)\le C_0\quad(s\le0),\qquad
 C(s)\le C_0+C_1s\quad(s\ge0).
\tag{24}
\]

Put \(r=p/q\in[1/2,1]\). The following uniform bounds suffice:

\[
 \frac{C_0}{p}<.762,\qquad
 \frac{C_1}{p}<.921,\qquad
 \frac{C_0}{q}<.7,\qquad
 \frac{C_0+hC_1}{q}<.945.
\tag{25}
\]

For the first bound, maximize
\(Rr/(1+r^2)^{3/2}\), whose maximum is
\(2R/(3\sqrt3)<.762\).
For the second,

\[
 \frac{C_1}{p}
 =R\frac{1-r^2+r^4}{(1+r^2)^{5/2}}.
\]

The sign of its derivative is the sign of
\(r(-7+7r^2-r^4)<0\); its maximum is therefore
\(26R/(25\sqrt5)<.921\).
The third bound follows from \(C_0/q\le R/(2\sqrt2)<.7\).

For the fourth, differentiate

\[
 \frac{r^2+r^4+h(r-r^3+r^5)}{(1+r^2)^{5/2}}.
\]

After a positive factor is removed, the derivative is

\[
 2r+r^3-r^5+h(1-7r^2+7r^4)
 \ge 1-\frac{3h}{4}=\frac{19}{40}>0.
\]

Its maximum is at \(r=1\), giving
\((C_0+hC_1)/q\le(2+h)R/(4\sqrt2)<.945\).
The four strict square reserves for (25), in order, are

\[
 \begin{split}
 .762^2\frac{27}{4}-Q&=\frac{3747}{10^6},\\
 .921^2(3125)-676Q&=\frac{152301}{40000},\\
 .7^2(8)-Q&=\frac{11}{2500},\\
 .945^2(32)-(2.7)^2Q&=\frac{8019}{250000}.
 \end{split}
\tag{26}
\]

Consider the canonical mixed-sign pair

\[
 \Psi_{p,q}(P,N)
 =p\{\phi(P)-1\}+q(\cos N-1)
                    -R\{N(P-N)-N(0)\},
 \qquad 0\le P,N\le h.
\tag{27}
\]

It is strictly concave in each variable separately.
For the positive variable, (24) gives

\[
 \Psi_{PP}\le-p\phi(P)+C_0+C_1P<0.
\tag{28}
\]

To see the final sign on the whole interval, the positive
counterpart \(p\phi(P)-C_0-C_1P\) is concave in \(P\).
At zero it is greater than \(.238p\); at \(h\) it is greater than

\[
                 p\{1.409-.762-.7(.921)\}
                         =\frac{23}{10000}p>0.
\tag{29}
\]

For the negative variable,

\[
                       \Psi_{NN}=-q\cos N+C(P-N).
\tag{30}
\]

If \(N\ge P\), use \(\cos h>.7648>.7>C_0/q\).
If \(N\le P\), the positive comparison

\[
                  q\cos N+C_1N-C_0-C_1P
\]

is concave in \(N\in[0,P]\). Its two endpoint values are
strictly positive by
\(C_0+hC_1<.945q\) and \(C_0<.7q<q\cos h\).
This proves (30).

## 4. The actual D support has a concave minorant

For \(s\in[0,h]\), let

\[
 V_k(s)=\cos s-1
       +R\{\sqrt{1+k^2}-\sqrt{1+k^2-2k\sin s}\}.
\tag{31}
\]

This is \(V_H(s)\) from (7), and it is strictly concave by
Section 3. Under (5), the exact D contribution obeys

\[
 \begin{split}
 W(-s)-1-S(\cos s,c-\sin s)+S(1,c)&\ge V_k(s),\\
 W(s)-1-S(\cos s,c+\sin s)+S(1,c)
                                      &\ge-(c_0-\tfrac12)s.
 \end{split}
\tag{32}
\]

For the second inequality, let \((a,b)\) be the maximizing sorted
outer state. At differentiability points the derivative of the
left side is

\[
              (\tfrac12-b)\cos s+(a-\tfrac12)\sin s
                         \ge-(c_0-\tfrac12).
\tag{33}
\]

The inequality integrates across both support transitions.

For the first inequality, there are three possible supports.
On the diagonal part its derivative is

\[
                (c_0-\tfrac12)\sin s+(c_0+\tfrac12)\cos s.
\tag{34}
\]

This is concave in \(s\), and its endpoint lower bounds are
\(1.3992\) and

\[
             (.3992)(.6442)+(1.3992)(.7648)
                      =\frac{1659091}{1250000}>1.327.
\tag{35}
\]

In contrast, concavity of \(V_k\) gives

\[
 V_k'(s)\le V_k'(0)
       =\frac{Rk}{\sqrt{1+k^2}}
       \le\frac{R(17/20)}{\sqrt{1+(17/20)^2}}<1.283.
\tag{36}
\]

The square reserve in (36) is
\(1.283^2(1+(17/20)^2)-Q(17/20)^2
 =2546921/400000000>0\).

On the interior-circle part, the derivative of the D increment is

\[
           -\sin s+\frac{Rc\cos s}{\sqrt{1+c^2-2c\sin s}}.
\tag{37}
\]

It is at least \(V_k'(s)\). After squaring the positive fractions,
the needed comparison reduces to

\[
                (c-k)(c+k-2ck\sin s)\ge0.
\tag{38}
\]

Here \(c\ge k\) and
\(1/c+1/k\ge1/2+20/17>2\sin h\).

The remaining support is the endpoint \(b=0\). It is never active
at \(s=0\), since \(c\ge1/2\). If it becomes active, its derivative
is

\[
                  \tfrac12\cos s+(a_0-\tfrac12)\sin s.
\tag{39}
\]

This derivative is strictly increasing up to \(h\), because

\[
 (a_0-\tfrac12)\cos s-\tfrac12\sin s
 >(.9145)(.7648)-\tfrac12(.6443)
 =\frac{943149}{2500000}>0.
\tag{40}
\]

At the transition it agrees with (37), already at least
\(V_k'\); afterwards (39) increases and \(V_k'\) decreases.
There cannot be a later exit from this endpoint: its support
condition implies
\[
 c\le\sin s+\frac{\cos s}{2(a_0+1/2)}<.645+.264<1,
\]
and then \((c-\sin s)/\cos s\) is strictly decreasing.
This proves derivative comparison in every support region.
Both sides of the first inequality in (32) vanish at zero,
so integration proves it.

All endpoint trigonometric bounds in (22), (29), (35) and (40)
follow directly from the alternating sine and cosine polynomials
at \(7/10\); no subdivision of the interval is involved.

## 5. Concentration of both signs

For a complete-circle two-angle term with coefficients \(p\le q\),
the normalized angular change is

\[
 p\{\cos a+\max(0,\sin a)-1\}
 +q\{\cos b+\max(0,\sin b)-1\}
             -R\{N(a+b)-N(0)\}.
\tag{41}
\]

If its two angles have the same sign, hold their sum fixed.
The two trigonometric terms are concave on that sign interval.
Their minimum is attained with one angle zero. For a positive
sum, the smaller coefficient \(p\) carries the resulting positive
angle; for a negative sum, the larger coefficient \(q\) carries
the resulting negative angle.

If the angles have opposite signs, interchange their roles when
necessary so that the positive angle has coefficient \(p\).
The norm is unchanged. The change of the angular part is
\[
 (q-p)\{\phi(P)-\cos N\}\ge0
\]
in the direction from this preferred ordering to the other one.
Thus the interchange can only decrease the lower stress bound.
Each block is now (27).

The HG0 expression has a two-angle G block and a one-angle H
block; HG2 has the reverse arrangement. A one-angle block is a
two-angle block with its other angle zero. Allowing that other
angle to vary is an enlargement of the scalar minimization
domain, not a change to the original geometry. It gives the
three common blocks (6) for either HG owner. The original sum,
positive variation and negative variation are retained during
the preceding normalization.

The D bounds (32) give a fourth scalar block

\[
                -(c_0-\tfrac12)P_D+V_H(N_D).
\tag{42}
\]

Originally at most one of \(P_D,N_D\) is nonzero. Allowing both
is another harmless enlargement. The actual support value
\(S(1,c)\) stays in the baseline (8).

Consequently the actual stress is bounded below by \(B(z)\)
plus the sum of these four blocks, subject to

\[
 P_i,N_i\ge0,\qquad
 P:=\sum_iP_i\le h-z,\qquad
 \sum_iN_i=z+P.
\tag{43}
\]

Fix all positive variables. By (30) and the concavity of \(V_H\),
the sum is concave on the negative-variable simplex. Its minimum
is attained with all negative variation in one block.
Next hold that negative variable fixed and use (28); the positive
variables likewise concentrate in one block. Thus at most one
block carries positive variation and at most one carries negative
variation.

Finally vary their common parameter \(P\in[0,h-z]\).
If the two occupied blocks differ, their sum has the form

\[
                         U_i(P)+V_j(z+P),
\tag{44}
\]

where the D positive alternative is linear and the D negative
alternative is \(V_H\). Both terms in (44) are concave.
If both signs occupy the same ordinary block, its sum is

\[
 p_i\{\phi(P)-1\}+q_i\{\cos(z+P)-1\}
                     -R\{N_i(-z)-N_i(0)\},
\tag{45}
\]

which is strictly concave. If both occupy the enlarged D block,
the sum is linear plus \(V_H(z+P)\), again concave.
The minimum is therefore at \(P=0\) or \(P=h-z\).

At \(P=0\) the possible increments are \(V_i(z)\).
At \(P=h-z\), an ordinary block carrying both signs gives
\(M_i(z)\), and distinct blocks give one positive increment and
one negative increment as in the last line of (9).
The enlargement permitting the same index in that last minimum
does not omit a possible lower value. In fact, with \(a=h-z\),
\[
                         M_i(z)\le U_i(a)+V_i(h).
\tag{46}
\]
To check (46), note that \(N_i'(s)\ge N_i'(0)\) for
\(-h\le s\le0\), since
\(\sin h<2p_iq_i/(p_i^2+q_i^2)\), while
\(N_i'(s)\le N_i'(0)\) for \(0\le s\le h\).
Integrating on \([-h,-z]\) and \([0,a]\) proves (46).
The both-signs D alternative is already included by its positive
term and the H negative term in (9).

This proves that the actual stress is at least
\(B(z)+{\cal E}(z)\). The actual separating inequalities require
that stress to be nonpositive, proving (10).

The proof has used the original whole-domain variation bound,
positive original witness weights, exact circle supports and
concavity on complete intervals. It has neither assumed a
concentrated original configuration nor replaced a numerical
minimum by a mathematical premise.
