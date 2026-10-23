# Splitting two positive intermediate errors at fixed total angle

## 1. Scope and the scalar reduction

This note extends the angle concentration mechanism of
HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md to two fixed
nonnegative intermediate errors. It does not by itself assert
that either new original-owner class is excluded.

Retain its original G0--G2 cycle, its four sorted outer states
H, G, B and D with signed tangents respectively positive,
negative, negative and negative, and its constants

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad h=\frac7{10},\quad
 a_0=\sqrt{Q-\frac14}-\frac12,\quad
 c_0=\sqrt{Q/2}-\frac12,\quad
 \eta=\frac{293}{1000},\quad
 \sigma=R\sqrt{1+\eta^2}-\frac{1+\eta}{2}.
\tag{1}
\]

The states A, T and E may have either original sign and either
radial kind. Consider either of these two owner patterns:

* GA2, AB2, BT2, TD2, DE2, EH0, with \(a=d_{AB}\ge0\);
* GA3, AB0, BT2, TD2, DE2, EH0, with \(a=d_{GA}\ge0\).

In both cases \(HG\in\{0,2\}\), and \(z=d_{TD}\ge0\).
Put

\[
 \theta=a+z,\qquad 0\le\theta<h.
\tag{2}
\]

The last bound follows from the original total-variation
inequality. No frame-order assumption is made.

Fix positive weights \(k,l,c\) as functions of \(\theta\).
They are held constant as \(a\) varies from zero to \(\theta\).
Set

\[
 z=\theta-a,\qquad m(z)=c(\cos z+\eta\sin z).
\tag{3}
\]

Assume throughout this entire split interval the admissibility
conditions (5) of the cited concentration note:

\[
 \frac12\le k\le\frac{17}{20},\qquad
 k\le c\le2,\qquad k\le l\le2k,\qquad
 \frac12\le\frac l{m(z)}\le2.
\tag{4}
\]

Use its exact sorted-circle support \(S\), full-circle support
\(\overline S\), and baseline

\[
 \begin{split}
 B(z)={}&k+2l+m+cW(z)+2-c\sigma\sin z\\
 &-\overline S(1,k)-\overline S(l,k)
          -\overline S(m,l)-S(1,c).
 \end{split}
\tag{5}
\]

For the pairs

\[
 (p_G,q_G)=(k,l),\qquad (p_H,q_H)=(k,1),\qquad
 (p_B,q_B)=(\min(l,m),\max(l,m)),
\tag{6}
\]

define \(N_i,U_i,V_i\) as in (7) of that note, and now define

\[
 M_i(\theta)=p_i\{\cos(h-\theta)+\sin(h-\theta)-1\}
       +q_i(\cos h-1)-R\{N_i(-\theta)-N_i(0)\}.
\tag{7}
\]

Let \({\cal E}_{m}(\theta)\) denote its envelope (9), with
\(\theta\) in place of the fixed TD angle and with the pairs
(6) formed using the actual \(m(z)\). Explicitly,

\[
 \begin{split}
 {\cal E}_{m}(\theta)=\min\bigg\{&
   \min_i V_i(\theta),\ \min_i M_i(\theta),\\
 &\min\{U_G(h-\theta),U_H(h-\theta),U_B(h-\theta),
                 -(c_0-\tfrac12)(h-\theta)\}
       +\min_j V_j(h)\bigg\}.
 \end{split}
\tag{8}
\]

Finally put

\[
 j(a)=W(a)-1-S(\sin a,1-\cos a).
\tag{9}
\]

The necessary inequality for either original owner pattern is

\[
                    B(z)+l j(a)+{\cal E}_{m}(\theta)\le0.
\tag{10}
\]

For the low-angle range, Section 4 proves that every scalar
alternative on the left of (10) is concave in the split
\(a\in[0,\theta]\), under the additional bounds

\[
 \theta\le\frac16,\qquad
       \frac c l\le\frac32,\qquad
       \frac{m(z)}l\le\frac32.
\tag{11}
\]

For the high-angle range, Sections 5--6 reduce (10) to its three
single-negative alternatives and prove their split concavity
under the balanced-pair conditions stated there and

\[
                       \frac9{10}\le\frac c l\le\frac{11}{10}.
\tag{12}
\]

Consequently, in either range it suffices to prove the relevant
scalar inequalities at the two endpoints

\[
                  (a,z)=(0,\theta),\qquad(\theta,0).
\tag{13}
\]

Those endpoint inequalities are separate scalar obligations.
In particular no claim about negative \(a\), negative \(z\),
an arbitrary original TD0 error, or other owner choices is made
by this note.

## 2. Exact force collection and the unchanged concentration

Use the original inequality weights
\((k,l,l,m,c,1,1)\) in cyclic order.
For AB2 the A force is exactly

\[
                l\{a_A\sin a+y_A(\cos a-1)\},
\tag{14}
\]

while B has force \((m\cos d_{BT},\,l+m\sin d_{BT})\).
Thus B's force is the old AB0 force with its AB angular
argument algebraically set to zero.

For GA3 the A force is instead

\[
                l\{a_A\sin a+y_A(1-\cos a)\},
\tag{15}
\]

while G's force is the old GA2 force with its GA angular
argument algebraically set to zero. The remaining G contribution
from HG is unchanged.

Since A's original corner is
\((a_A+\tfrac12,\,|y_A|+\tfrac12)\), either (14) or (15) is at most

\[
                         lS(\sin a,1-\cos a).
\tag{16}
\]

This uses its actual shifted-circle constraint and sorting;
it permits either sign of \(y_A\).
The corresponding demand differs from its zero-angle demand by
\(l(W(a)-1)\), giving exactly (9).

The T force and its support remain those of (14) and (19) of the
TD2 concentration note. All other force formulas are unchanged.
The other original errors sum to \(-\theta\). Their total
positive variation is at most \(h-\theta\), and their total
negative variation is that positive variation plus \(\theta\).

The lost rotation is therefore a virtual zero angle in the
same three norm blocks. Enlarge that zero angle exactly as in
the virtual singleton argument of the cited note. Its separate
concavity, the D support minorant, the two simplex concentrations,
and the final variation concentration all apply with
\(\theta\) replacing the fixed TD angle. They give (8)--(10).
This is an algebraic relaxation of the original force sum;
it does not introduce a new original separating witness.

## 3. The exact A support and its curvature

Write

\[
 b_0=\sqrt{Q-\frac14},\qquad
 \alpha_0=2\arctan\frac1{2b_0}.
\tag{17}
\]

For \(0\le a\le h\), the ratio of the two nonnegative force
components in (9) is \(\tan(a/2)<1\). Thus no diagonal support
branch occurs. The only branches are the tangent-zero support
and the full-circle support:

\[
 j(a)=
 \begin{cases}
 \displaystyle\frac{\cos a-1}{2}
                  +(\frac12-a_0)\sin a,&0\le a\le\alpha_0,\\[4pt]
 \displaystyle\sin a-2R\sin(a/2),&\alpha_0\le a\le h.
 \end{cases}
\tag{18}
\]

The values and first derivatives agree at \(\alpha_0\).
The elementary bounds used below are

\[
 R<1.98,\qquad a_0-\tfrac12<.915,\qquad
 \sigma<1.416,\qquad
 \cos h>.7648,\qquad \sin h<.645.
\tag{19}
\]

The radical comparisons are obtained by squaring positive
quantities. The trigonometric bounds follow from \(C_6(h)\)
and \(S_5(h)\).

Also \(\alpha_0>1/2\): indeed
\(1/(2b_0)>13/50\), while
\(\tan(1/4)\le8/31<13/50\).
On the first branch,

\[
                j''(a)=-\tfrac12\cos a+(a_0-\tfrac12)\sin a.
\tag{20}
\]

On the second branch,

\[
                j''(a)=\sin(a/2)\{R/2-2\cos(a/2)\}<0.
\tag{21}
\]

For \(a\ge1/2\) the function
\(-\tfrac12\cos a+.92\sin a\) is positive and increasing:
its value at \(1/2\) is positive already using \(S_3(1/2)\)
and \(C_4(1/2)\). Thus (20)--(21) give the useful global bound

\[
                   j''(a)\le-\tfrac12\cos a+.92\sin a
\tag{22}
\]

on each smooth branch. On \(0\le a\le1/6\) the stronger
bound (20), with coefficient \(.915\), applies throughout.

## 4. Low-angle split concavity

Fix \(0\le\theta\le1/6\), and put

\[
 b=h-\theta,\qquad
 g=\cos b+\sin b-1\ge0,\qquad e=\cos h-1<0.
\]

The separated alternative \(U_B(b)+V_B(h)\) is redundant:
it is at least \(M_B(\theta)\), by (46) of the TD2
concentration note. Omit that one alternative from (8).

After collecting the B norm, every remaining alternative of
\(B(z)+l j(a)+{\cal E}_{m}(\theta)\) has the form

\[
        H(m(z))+cW(z)-c\sigma\sin z+l j(a)+C,
\tag{23}
\]

where \(C\) is constant in the split and \(H\) is one of these
five functions:

\[
 \begin{split}
 H_0(m)&=\tfrac32m-R\sqrt{l^2+m^2},\\
 H_\theta(m)&=\tfrac32m+\max(l,m)(\cos\theta-1)
                 -R\sqrt{l^2+m^2-2lm\sin\theta},\\
 H_M(m)&=\tfrac32m+\min(l,m)g+\max(l,m)e
                 -R\sqrt{l^2+m^2-2lm\sin\theta},\\
 H_U(m)&=\tfrac32m+\min(l,m)g
                 -R\sqrt{l^2+m^2+2lm\sin b},\\
 H_h(m)&=\tfrac32m+\max(l,m)e
                 -R\sqrt{l^2+m^2-2lm\sin h}.
 \end{split}
\tag{24}
\]

Each \(H\) is concave in \(m\). Away from \(m=l\), the second
derivative of its norm term is

\[
             -\frac{Rl^2\cos^2 s}
                     {(l^2+m^2+2lm\sin s)^{3/2}}\le0.
\tag{25}
\]

At \(m=l\), every coefficient change has a nonpositive
derivative jump: it is \(-g\), \(e\), or \(e-g\).

Under \(m/l\le3/2\), all five functions also satisfy

\[
                              H'(m)>-\frac{12}{25}.
\tag{26}
\]

For \(H_0\) and \(H_U\), this follows directly from
\(3/2-R>-12/25\), since the additional derivative of
\(\min(l,m)g\) is nonnegative.
For the other three functions set \(r=m/l\).
For \(0\le s\le h\),

\[
 \frac{r-\sin s}{\sqrt{1+r^2-2r\sin s}}
       \le\frac r{\sqrt{1+r^2}}\le\frac3{\sqrt{13}}.
\tag{27}
\]

The first inequality follows by differentiating in
\(\sin s\), since \(r\sin h<1\).
Their smallest additional coefficient derivative is \(e\).
Thus

\[
 H'(m)\ge\tfrac12+\cos h-\frac{3R}{\sqrt{13}}
       >\tfrac12+.7648-1.65>-\frac{12}{25}.
\tag{28}
\]

The middle radical bound is certified by
\(13(33/20)^2-9Q>0\).

Along the split \(z=\theta-a\), \(m''=-m\). Equations
(25)--(26) give

\[
             \frac{d^2}{da^2}H(m(z))\le\frac{12}{25}m.
\tag{29}
\]

Moreover

\[
 m\le(1+\eta/6)c,\qquad
 \begin{split}
 \frac{d^2}{da^2}\{cW(z)-c\sigma\sin z\}
   &\le\left(-\frac{71}{144}+\frac{229}{1500}\right)c,\\
 l j''(a)&\le
                  \left(-\frac{71}{144}+\frac{61}{400}\right)l.
 \end{split}
\tag{30}
\]

Using \(c/l\le3/2\), their sum is at most

\[
 \begin{split}
 &\left[
 \frac32\left\{\frac{12}{25}(1+\eta/6)
                       -\frac{71}{144}+\frac{229}{1500}\right\}
             -\frac{71}{144}+\frac{61}{400}\right]l\\
 &\hspace{35mm}=-\frac{86381}{900000}l<-\frac9{100}l.
 \end{split}
\tag{31}
\]

The exact reserve in the last comparison is \(5381/900000\).
The derivative jumps at \(m=l\) remain nonpositive after
composition; this holds for either direction of crossing.
Consequently every alternative (23) is strictly concave on
the complete split interval. Its minimum is at (13).

## 5. Balanced envelopes without a lower bound \(q_{\min}\ge1\)

For a fixed split assume all three pairs (6) satisfy

\[
 \frac{p_i}{q_i}\ge\frac23,\qquad
 \frac{q_{\max}}{q_{\min}}\le\frac65,
\quad
 q_{\min}=\min_iq_i,\quad q_{\max}=\max_iq_i.
\tag{32}
\]

The scalar-envelope lemmas give

\[
 M_i(\theta)\ge V_i(\theta),\qquad
 U_i(b)\ge-\frac{109}{200}q_i b,\qquad
 V_i(h)\ge V_i(\theta)+\frac23q_i b.
\tag{33}
\]

Here \(q_H=1\), so \(q_{\max}\ge1\). Therefore the positive
D alternative is also at least
\(-\frac{109}{200}q_{\max}b\), since \(c_0-\tfrac12<.4\).
Every separated alternative in (8) is at least

\[
 \begin{split}
 \min_i V_i(\theta)
       +\left(\frac23q_{\min}
                    -\frac{109}{200}q_{\max}\right)b
 &\ge\min_i V_i(\theta)+\frac{19}{1500}q_{\min}b.
 \end{split}
\tag{34}
\]

Thus the balanced reduction is exactly

\[
                         {\cal E}_m(\theta)=\min_iV_i(\theta).
\tag{35}
\]

This argument uses \(q_{\max}\ge1\), which is automatic here.
It does not require \(q_{\min}\ge1\).

## 6. High-angle split concavity

Suppose (32) holds throughout the split and
\(9/10\le c/l\le11/10\).
Then

\[
       \frac ml\le\frac{11}{10}\sqrt{1+\eta^2}<\frac{23}{20}.
\tag{36}
\]

The G and H single-negative alternatives (35) have
\(H_0(m)\) as their B-dependent part. The B alternative has
\(H_\theta(m)\). Both are concave and increasing in \(m\)
on the range (36).

For \(H_0\), positivity of its derivative follows by
squaring; at \(r=m/l=23/20\) the reserve is

\[
       \frac94-(Q-\tfrac94)r^2=\frac{11811}{250000}>0.
\tag{37}
\]

For \(H_\theta\), if \(r\le1\), (27) with \(r\le1\)
gives \(H_\theta'(m)\ge3/2-R/\sqrt2>0\).
If \(1\le r\le23/20\), write
\(s=\sin\theta\) and \(C=\cos\theta\). The required inequality is

\[
       C+\frac12>
          R\frac{r-s}{\sqrt{1+r^2-2rs}}.
\tag{38}
\]

The right side increases with \(r\); take \(r=23/20\).
Using \(C\ge1-s^2\), the squared reserve in (38) is at least

\[
 P(s)=\frac{11811}{250000}
       +\frac{23943}{6250}s
       -\frac{42803}{5000}s^2+\frac{23}{5}s^3.
\tag{39}
\]

On \(0\le s\le129/200\), \(P'\) is strictly convex and

\[
 P(0)=\frac{11811}{250000}>0,\qquad
 P(129/200)=\frac{298569}{1562500}>0,\qquad
 P'(129/200)=-\frac{1471149}{1000000}<0.
\tag{40}
\]

Once \(P'\) is nonpositive, convexity and its negative right
endpoint keep it nonpositive for the rest of the interval.
Hence \(P\) increases and then decreases, or decreases throughout;
its minimum is at an endpoint. This proves (38).
The kink of \(H_\theta\) at \(m=l\) is downward.

The composition of either concave increasing \(H\) with
the concave function \(m(z)\) is concave. The remaining
second derivative in each single-negative scalar is at most

\[
 c\{-\tfrac12\cos z+.916\sin z\}
          +l\{-\tfrac12\cos a+.92\sin a\}.
\tag{41}
\]

Since \(a+z\le.7\),
\(\sin a+\sin z\le.7\), and each cosine exceeds \(.7648\).
Equation (12) therefore bounds (41) by

\[
 \left\{-\frac12(.7648)\frac{19}{10}
             +(.7)\frac{11}{10}(.916)\right\}l
       =-\frac{531}{25000}l<-\frac1{50}l.
\tag{42}
\]

The last strict reserve is \(31/25000\).
Equations (22) and (42), together with the nonpositive
derivative jumps, prove strict split concavity on the whole
interval. Again only (13) remains.

## 7. A single polynomial-compatible A endpoint bound

For \(1/6\le\theta\le h\), the exact support (18) also satisfies

\[
 j(\theta)\ge
     \frac{\cos\theta-1}{2}
          +(\tfrac12-a_0)\sin\theta
          -\frac{43}{500}(\theta-\tfrac16)^4.
\tag{43}
\]

Below \(\alpha_0>1/2\), the subtracted term is unnecessary.
Above \(\alpha_0\), the difference between full-circle and
tangent-zero support is exactly

\[
       2R\sin(\theta/2)
            \left\{1-\cos\frac{\theta-\alpha_0}{2}\right\}
       \le\frac{R\theta(\theta-\frac12)^2}{8}.
\tag{44}
\]

The ratio
\(\theta(\theta-\frac12)^2/(\theta-\frac16)^4\)
is increasing on \([1/2,.7]\): after positive factors its
derivative is \(-\theta^2+\theta+1/12>0\).
At \(\theta=.7\), multiplication by \(R/8<1.98/8\)
gives a number strictly below \(43/500=.086\).
This proves (43) without a further support partition in
an endpoint polynomial certificate.

## 8. What this lemma leaves to check

For weights satisfying the low hypotheses (4), (11), all
alternatives of (10) need only be checked at (13).
For weights satisfying (4), (12), (32), the three alternatives
from (35) need only be checked there.
The weights may vary with \(\theta\); they are fixed only
during each split comparison.

All comparisons above are whole-interval inequalities,
intrinsic support transitions, or one-variable endpoint
arguments. The remaining endpoint scalar positivity must
be supplied before (10) can be used as an exclusion theorem.
