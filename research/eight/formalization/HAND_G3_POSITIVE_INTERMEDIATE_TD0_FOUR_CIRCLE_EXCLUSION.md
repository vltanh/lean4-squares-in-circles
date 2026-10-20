# A positive intermediate error with an arbitrary original TD0 error

## 1. Original scope

Work on the original G0--G2 cycle, with

\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad h=\frac7{10},
 \qquad
 a_0=\sqrt{Q-\frac14}-\frac12,\qquad
 c_0=\sqrt{Q/2}-\frac12.
\tag{1}
\]

The four original sorted outer states H, G, B and D have signed
tangents respectively positive, negative, negative and negative.
A, T and E may have either sign and either radial kind. This
note excludes both original-owner patterns

* GA2, AB2, BT2, TD0, DE2, EH0, with \(a=d_{AB}\ge0\);
* GA3, AB0, BT2, TD0, DE2, EH0, with \(a=d_{GA}\ge0\).

In both patterns \(HG\in\{0,2\}\). The original TD0 error
has either sign. There is no frame-order assumption.

The complete G1 total-variation consequence gives

\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+<h.
\tag{2}
\]

In particular \(0\le a<h\). The proof uses two ranges for
this single total intermediate angle. On \(a\le1/6\), one
fixed stress has a uniform positive reserve. On \(a\ge1/6\),
four-circle concentration reduces to the already certified
pure-A endpoint of
[the two-positive-error scalar theorem](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_COMPLETE_SCALAR_EXCLUSION.md).
The second part does not assume an original TD2 witness.

All decimals below are exact rationals. Use

\[
\begin{split}
 W(t)&=\frac{1+\cos t+|\sin t|}{2},\\
 S(f,g)&=\max_{0\le b\le c_0}
   \left\{f\left(\sqrt{Q-(b+\tfrac12)^2}-\tfrac12\right)+gb\right\},\\
 \overline S(f,g)&=R\sqrt{f^2+g^2}-\frac{f+g}{2},\\
 j(a)&=W(a)-1-S(\sin a,1-\cos a).
\end{split}
\tag{3}
\]

The exact support \(S\) concerns the sorted shifted circle;
\(\overline S\) is its full-circle upper bound.

## 2. Exact original force reduction

Write the original errors in cyclic order as
\((v,u,w,x,z,d,r)\), for HG, GA, AB, BT, TD, DE and EH.
Give their actual inequalities the positive weights

\[
                         (k,l,l,c,c,1,1).
\tag{4}
\]

The original T and E coordinates cancel exactly. The
A contribution is, in the first owner pattern,

\[
                  l\{a_A\sin a+y_A(\cos a-1)\},
\tag{5}
\]

and, in the second,

\[
                  l\{a_A\sin a+y_A(1-\cos a)\}.
\tag{6}
\]

Here \(y_A\) is signed. Since A's actual corner is
\((a_A+\tfrac12,|y_A|+\tfrac12)\), either contribution is
at most \(lS(\sin a,1-\cos a)\). This uses only A's
actual circle constraint and sorting.

The four other force vectors are exactly those of
[the secondary-owner four-circle theorem](HAND_G3_HIGH_GA_LOW_EH_SECONDARY_OWNER_FOUR_CIRCLE_EXCLUSION.md),
with its coefficient 2 replaced by c, and with the lost
AB argument or GA argument algebraically set to zero:

\[
\begin{split}
 F_H&=(\cos r,\ k+\sin r),\\
 F_G&=(l\cos u+k\sin v,\ l\sin u+k\cos v),\\
 F_B&=(c\cos x+l\sin w,\ l\cos w+c\sin x),\\
 F_D&=(\cos d+c\sin z,\ c\cos z+\sin d)
\end{split}
\qquad(HG0).
\tag{7}
\]

For HG2 replace only the first two by

\[
 F_H=(\cos r+k\sin v,\ k\cos v+\sin r),\qquad
 F_G=(l\cos u,\ l\sin u+k).
\tag{8}
\]

Thus the actual stress is bounded below by the four-circle
expression at those algebraic arguments, plus \(lj(a)\).
No original owner is changed. The other original errors sum
to \(-a\); their positive variation is at most \(h-a\), and
their negative variation equals their positive variation plus a.

## 3. A fixed stress for \(0\le a\le1/6\)

Choose

\[
 k=\frac{39}{50},\qquad l=\frac{63}{50},\qquad
 c=\frac95,\qquad \lambda=\frac{103}{100}.
\tag{9}
\]

Use the full-circle bound for H, G and B, and the exact
sorted-circle support for D. The resulting zero-angle baseline is

\[
\begin{split}
 B_0={}&k+2l+2c+2
   -\overline S(1,k)-\overline S(l,k)
   -\overline S(c,l)-(1+c)c_0\\
 &>\frac{13}{400}=.0325.
\end{split}
\tag{10}
\]

Here the D maximizer is diagonal because \(c>1\).
We will prove that every circle's change from this baseline,
after adding \(\lambda\) times that circle's algebraic errors,
is nonnegative.

### 3.1 Three full-circle blocks

For \(0<p\le q\), set

\[
\begin{split}
 N_{p,q}(s)&=\sqrt{p^2+q^2+2pq\sin s},\\
 \Psi_{p,q}(P,N)&=
 p(\cos P+\sin P-1)+q(\cos N-1)\\
 &\hspace{18mm}
 -R\{N_{p,q}(P-N)-N_{p,q}(0)\}
 +\lambda(P-N).
\end{split}
\tag{11}
\]

Use the three coefficient pairs

\[
                  (p,q)=(k,l),\quad(k,1),\quad(l,c).
\tag{12}
\]

Each has \(p/q>1/2\). Section 3 of
[the TD2 concentration lemma](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md)
proves that the expression in (11) is concave in each
variable separately on \(0\le P,N\le h\). The added linear
charge has no effect on that proof.

For clarity, this applies to every original two-error block.
For errors of the same sign, hold their sum fixed and use
concavity of the two trigonometric terms to put the sum in
one error. For errors of opposite signs, put the positive
error on p and the negative error on q; this can only
decrease the lower stress bound. The sum of the two errors,
and hence its linear charge, is unchanged. A one-error
block is obtained by setting one argument to zero.

Separate concavity reduces the lower bound on (11) to its
four rectangle corners. The value at \((0,0)\) is zero.
For each pair (12), the other three corners satisfy

\[
\begin{split}
 p(\cos h+\sin h-1)
     -R\{N_{p,q}(h)-N_{p,q}(0)\}+\lambda h&>.075,\\
 q(\cos h-1)
     +R\{N_{p,q}(0)-N_{p,q}(-h)\}-\lambda h&>.007,\\
 p(\cos h+\sin h-1)+q(\cos h-1)&>.022.
\end{split}
\tag{13}
\]

These are substitutions at the intrinsic corners just proved
sufficient, not sampled angular bounds. Here are explicit
rational enclosures that verify all of them. In the order
\((k,l),(k,1),(l,c)\),

\[
\begin{array}{c|ccc}
 & (k,l)&(k,1)&(l,c)\\ \hline
 N_{p,q}(0)>&1.481890&1.268227&2.197180\\
 N_{p,q}(0)<&1.481891&1.268228&2.197181\\
 N_{p,q}(h)<&1.860719&1.616596&2.783842\\
 N_{p,q}(-h)<&.964223&.776802&1.380373
\end{array}
\tag{14}
\]

Positive squaring, with \(S_9(h)\) and \(S_7(h)\), verifies
these norm bounds. Use \(C_6(h)\) for cosine and \(S_7(h)\)
for every positive sine coefficient, together with

\[
 1.978787<R<1.978788,\quad
 .8992<c_0<.899215,\quad a_0-\tfrac12<.915.
\tag{15}
\]

For example the smallest negative-corner lower bound is

\[
 l\{C_6(h)-1\}
 +1.978787(1.481890-.964223)-\lambda h
       >.007052>.007.
\tag{16}
\]

The smallest positive-corner lower bound is greater than
.075533, and the smallest opposite-corner bound exceeds
.022764. The same enclosures give the lower value
.0325401276 in (10); its reserve above \(13/400\) is
\(100319/2500000000\).

Thus every charged H, G or B block is nonnegative for
either original HG owner.

### 3.2 The actual D block is minimized at zero

Define

\[
 T(z,d)=cW(z)+W(d)
  -S(\cos d+c\sin z,\ c\cos z+\sin d)+\lambda(z+d).
\tag{17}
\]

Its domain is the intrinsic hexagon

\[
 z_++d_+\le h,\qquad (-z)_++(-d)_+\le h.
\tag{18}
\]

We prove

\[
                     T(z,d)\ge T(0,0)=(1+c)(1-c_0).
\tag{19}
\]

The second force component is greater than
\(c(.7648)-.645=.73164\); the first is less than
\(1+c(.645)=2.161\). Since
\(\sqrt{Q-1/4}>1.9\),

\[
                       .73164-\frac{2.161}{3.8}>0.
\tag{20}
\]

When the first force is positive, (20) makes the support
objective's derivative at \(b=0\) positive. When it is
nonpositive, the objective increases throughout the sorted
arc. Thus the only support branches are the diagonal and
the interior full-circle point.

For \(d\ge0\), the envelope derivative satisfies

\[
 \partial_dT
 =\lambda-\{(b-\tfrac12)\cos d-(a-\tfrac12)\sin d\}
 >\lambda-(c_0-\tfrac12)>0.
\tag{21}
\]

For \(d=-w<0\), it is

\[
 \partial_dT
 =\lambda-\{(b+\tfrac12)\cos w+(a-\tfrac12)\sin w\}.
\tag{22}
\]

At the diagonal, the brace is a positive concave
trigonometric function of \(w\in[0,h]\). Its endpoint
lower bounds are \(1.3992\) and

\[
                 (1.3992)(.7648)+(.3992)(.6442)>\lambda.
\tag{23}
\]

At the interior point write \(s=z-w\), and put

\[
 A=1+c^2=\frac{106}{25},\qquad B=c=\frac95,\qquad
 V(s)=\frac{cR\cos s}{\sqrt{A+2c\sin s}}.
\tag{24}
\]

The brace in (22) is \(V(s)-\sin w\).
If \(s\le0\), positive squaring gives \(V(s)\ge V(0)\):
the exact difference has the sign of
\(-\sin s(A\sin s+2c)\), which is nonnegative because
\(2c>A(.645)\). Furthermore

\[
                 V(0)-\sin h>
                 \frac{(9/5)(1.978787)}{2.06}-.645
                 >\lambda.
\tag{25}
\]

If \(s\ge0\), (18) implies \(w\le h-s\). Consider

\[
                       J(s)=V(s)-\sin(h-s),\qquad 0\le s\le h.
\tag{26}
\]

This function is strictly concave. Indeed, for
\(N(s)=\sqrt{A+2B\sin s}\), one has \(V=RN'\) and

\[
 -RN'''(s)=
 \frac{RB\cos s
       \{A^2-3B^2+AB\sin s+B^2\sin^2s\}}
      {(A+2B\sin s)^{5/2}}.
\tag{27}
\]

The tangent bound for the square root gives
\(\sqrt{A+2Bs}<103/50+(7/8)s\), since
\(\sqrt A<103/50\) and \(B/\sqrt A<7/8\).
Using \(R>197/100\), \(\cos s\ge1-s^2/2\),
\(\sin s\ge s-s^3/6\), and discarding the positive
\(B^2\sin^2s\) term, the exact polynomial identity

\[
\begin{split}
 &\frac{197}{100}B(1-s^2/2)
          \{A^2-3B^2+AB(s-s^3/6)\}\\
 &\quad-\left(\frac{103}{50}+\frac78s\right)
                      (A+2Bs)^2(h-s)\\
 &=\frac{1049297}{312500}
  +\frac{566517}{62500}s
  +\frac{16619147}{625000}s^2
  +\frac{1714347}{62500}s^3
  +\frac{567}{50}s^4
  +\frac{281907}{125000}s^5>0
\end{split}
\tag{28}
\]

proves \(-RN'''(s)>h-s\ge\sin(h-s)\).
Consequently \(J''<0\) on the whole interval.
Its left endpoint exceeds \(\lambda\) by (25), and its
right endpoint satisfies

\[
                 J(h)>
                 \frac{(9/5)(1.978787)(.7648)}{2.562}
                 >\lambda.
\tag{29}
\]

The denominator bound follows from
\(A+2c\sin h<A+2c(.645)=6.562<2.562^2\).
Thus the derivative (22) is negative throughout \(d<0\).
Together with (21), this proves that moving d toward zero
does not increase T. The conclusion persists across the
diagonal/interior support transition, where the first
derivatives agree.

It remains to minimize \(T(z,0)\). For \(z\le0\), the
second force component exceeds the first, so the support
is diagonal. The derivative is
\(\lambda-c\{(c_0+\tfrac12)\cos(-z)
 +(c_0-\tfrac12)\sin(-z)\}<0\) by (23).
For \(z\ge0\) in the diagonal branch, the derivative is

\[
           \lambda-c(c_0-\tfrac12)(\cos z-\sin z)
                         >\lambda-c(.4)>0.
\tag{30}
\]

In the interior branch, \(1+c\sin z>c\cos z\).
This forces \(\sin z>.35\): otherwise
\(\cos z>\sqrt{1-.35^2}>.93\), whereas
\(1+c(.35)<c(.93)\).
Hence \(A+2c\sin z>5.5\) and
\(R/\sqrt{A+2c\sin z}<.85\). The derivative is therefore

\[
\begin{split}
 \partial_z T
 &=\lambda+c(\cos z-\sin z)
       -\frac{cR\cos z}{\sqrt{A+2c\sin z}}\\
 &>\lambda+c\{.15(.7648)-.645\}
       =.075496>0.
\end{split}
\tag{31}
\]

This proves (19).

### 3.3 The low-angle contradiction

The charges of the three full-circle blocks and the D
block sum to \(-\lambda a\). Their nonnegativity, (10),
and the exact force reduction give an actual stress
strictly larger than

\[
                         \frac{13}{400}+\lambda a+lj(a).
\tag{32}
\]

On \(0\le a\le1/6\), the support in (3) is the
tangent-zero branch:

\[
 j(a)=\frac{\cos a-1}{2}
             +(\tfrac12-a_0)\sin a
       \ge-\frac{a^2}{4}-.915a.
\tag{33}
\]

This exact support formula and the transition angle
greater than \(1/2\) are proved in Section 3 of
[the split-concavity lemma](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_SPLIT_CONCAVITY.md).
The resulting quadratic lower bound in (32) decreases
throughout \([0,1/6]\). At the right endpoint its value is

\[
 \frac{13}{400}+\frac{\lambda}{6}
       -l\left(\frac1{144}+\frac{.915}{6}\right)
          =\frac{49}{15000}>0.
\tag{34}
\]

This contradicts the actual separating inequalities and
excludes the entire low-angle range.

## 4. Four full-circle blocks for \(1/6\le a<h\)

Put \(t=a-1/6\), and use the cubic family

\[
\begin{split}
 k&=.6692+.5218t-.5956t^2+.4216t^3,\\
 l&=1+.0175t-1.0932t^2+1.278t^3,\\
 c&=1.0163-.0209t-1.1486t^2+1.4069t^3.
\end{split}
\tag{35}
\]

All its whole-interval ranges are proved in Section 2
of the complete two-positive-error scalar theorem.
In particular

\[
 \frac23<k<\min(l,c),\quad
 .89<l<1.0002,\quad .89<c\le1.0163,\quad
 l<\frac32k,\quad .9l<c<1.1l.
\tag{36}
\]

Use the full-circle upper bound for D as well. The zero
baseline is now

\[
 B_{\rm full}=k+2l+2c+2
 -\overline S(1,k)-\overline S(l,k)
 -\overline S(c,l)-\overline S(1,c).
\tag{37}
\]

There are four unordered coefficient pairs:

\[
 (p_G,q_G)=(k,l),\quad (p_H,q_H)=(k,1),\quad
 (p_B,q_B)=(\min(l,c),\max(l,c)),\quad
 (p_D,q_D)=(\min(1,c),\max(1,c)).
\tag{38}
\]

For each pair let \(N_i\) have the meaning in (11), and define

\[
\begin{split}
 U_i(b)&=p_i(\cos b+\sin b-1)
           -R\{N_i(b)-N_i(0)\},\\
 V_i(b)&=q_i(\cos b-1)
           -R\{N_i(-b)-N_i(0)\},\\
 M_i(a)&=p_i(\cos(h-a)+\sin(h-a)-1)
           +q_i(\cos h-1)
           -R\{N_i(-a)-N_i(0)\}.
\end{split}
\tag{39}
\]

Every pair has \(p_i/q_i\ge2/3\), and the four q-coefficients
satisfy \(q_{\max}/q_{\min}<6/5\).
Indeed the first three pairs have those ranges in the
cited theorem at its pure-A endpoint. Adding
\(q_D=\max(1,c)\) does not change their maximum or minimum.
Also \(\min(1,c)/\max(1,c)>.89>2/3\).

The two simplex concentrations of Section 5 of the TD2
concentration lemma now apply to four ordinary circle
blocks. Its proof uses separate concavity of each block
and the simplex constraints; the number of blocks is
irrelevant. Any one-angle block, including the algebraic
zero created by (5) or (6), is enlarged by allowing its
other argument to vary. This relaxes the scalar bound and
does not change an original witness.

Explicitly, normalized positive and negative variables
satisfy

\[
 P_i,N_i\ge0,\qquad
 P=\sum_iP_i\le h-a,\qquad \sum_iN_i=P+a.
\tag{40}
\]

First concentrate the negative variables, then the positive
variables, and finally minimize their concave dependence on
\(P\in[0,h-a]\). The resulting lower envelope consists of
\(V_i(a)\), \(M_i(a)\), or \(U_i(h-a)+V_j(h)\).

The balanced scalar inequalities proved in
[the concentration envelopes](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md)
give

\[
\begin{split}
 M_i(a)&\ge V_i(a),\\
 U_i(b)&\ge-\frac{109}{200}q_i b,\\
 V_i(h)&\ge V_i(a)+\frac23q_i(h-a).
\end{split}
\tag{41}
\]

Thus every separated alternative is at least

\[
 \min_iV_i(a)+
  \left(\frac23q_{\min}-\frac{109}{200}q_{\max}\right)(h-a)
 \ge\min_iV_i(a)+\frac{19}{1500}q_{\min}(h-a).
\tag{42}
\]

Consequently the actual stress is at least

\[
                    B_{\rm full}+lj(a)+
                       \min_{i\in\{G,H,B,D\}}V_i(a).
\tag{43}
\]

## 5. The D negative curve is redundant

For \(0<p\le q\), write

\[
 V_{p,q}(b)=q(\cos b-1)
 +R\left\{\sqrt{p^2+q^2}
       -\sqrt{p^2+q^2-2pq\sin b}\right\}.
\tag{44}
\]

We prove \(V_D(b)\ge V_H(b)\) for all \(0\le b\le h\).

First \(V_{p,q}(b)\) increases with p when
\(2/3\le p/q\le1\). For \(b>0\), differentiation and
positive squaring reduce this to

\[
                  \sin b<\frac{2pq}{p^2+q^2}.
\tag{45}
\]

The right side is at least \(12/13\), whereas
\(\sin h<129/200\). If the subtracted derivative term
has negative numerator, monotonicity is immediate and
no squaring is needed. At \(b=0\) all these functions
vanish.

If \(c\le1\), (36) and this monotonicity yield
\(V_D=V_{c,1}\ge V_{k,1}=V_H\).

For \(c\ge1\), we also need monotonicity in q on
\(5/6\le p/q\le1\). Put \(r=p/q\), \(s=\sin b\), and
\(C=\cos b\). The exact derivative is

\[
\begin{split}
 \partial_qV_{p,q}(b)&=C-1+R g_r(s),\\
 g_r(s)&=\frac1{\sqrt{1+r^2}}
           -\frac{1-rs}{\sqrt{1+r^2-2rs}},\\
 g_r'(s)&=\frac{r^2(r-s)}
                    {(1+r^2-2rs)^{3/2}}.
\end{split}
\tag{46}
\]

On \(5/6\le r\le1\), \(0\le s\le129/200\),

\[
                              g_r'(s)>\frac14.
\tag{47}
\]

Here is an exact whole-rectangle proof. For fixed r, the
derivative of \(g_r'\) has the sign of
\(2r^2-1-rs\), which decreases in s. Hence \(g_r'\)
has its minimum at an s-endpoint.
At zero it is \(r^3/(1+r^2)^{3/2}\), increasing in r.
At \(r=5/6\), comparison with \(1/4\) has the squared
reserve \(16\cdot125^2-61^3=23019>0\).

At \(s=129/200\), the derivative of \(g_r'\) in r has
the sign of

\[
                       r(3+s^2)-2s(1+r^2).
\tag{48}
\]

This is a concave quadratic in r with positive endpoint
values \(31721/48000\) and \(33441/40000\).
Thus again take \(r=5/6\).
After positive squaring, (47) has reserve

\[
 16r^4(r-s)^2-(1+r^2-2rs)^3
                  =\frac{559811}{15552000}>0
 \quad\left(r=\frac56,\ s=\frac{129}{200}\right).
\tag{49}
\]

This proves (47). Since \(g_r(0)=0\), it follows that
\(g_r(s)\ge s/4\). Therefore, for \(b>0\),

\[
\begin{split}
 \partial_qV_{p,q}(b)
 &\ge s\left\{\frac R4-\frac{s}{1+C}\right\}\\
 &>s\left\{\frac{1.97}{4}
                   -\frac{.645}{1+.7648}\right\}
   =\frac{56041}{441200}s>0.
\end{split}
\tag{50}
\]

Because \(1\le c<6/5\), this q-monotonicity gives

\[
                    V_D=V_{1,c}\ge V_{1,1}\ge V_{k,1}=V_H.
\tag{51}
\]

Equations (45) and (51) cover both c-ranges.
The minimum in (43) thus reduces to the three original
curves G, H and B.

## 6. The high-angle contradiction and conclusion

The remaining three expressions are exactly

\[
                B_{\rm full}+lj(a)+V_i(a),
                       \qquad i\in\{G,H,B\}.
\tag{52}
\]

They are the pure-A endpoint expressions of Sections 5--7
of the complete two-positive-error scalar theorem, with
\(\theta=a\) and its algebraic TD2 angle zero. That theorem
uses the full D-circle support at this endpoint, exactly
as in (37). Its explicitly defined polynomial numerators
\(N_{AG},N_{AH},N_{AB}\) certify strict positivity on
\([1/6,h]\).

The invocation concerns identical scalar formulas. It
does not turn the arbitrary original TD0 error into an
aligned TD2 witness: that error has already been included
in the four-block concentration (38)--(43).

Thus (43) is positive, contradicting the original weighted
separating inequalities. Together with (34), this excludes
both owner patterns in Section 1 for every \(0\le a<h\)
and every original TD0 error.

The proof keeps the original four outer circles, permits
either sign and either radial kind for A, T and E, and
uses no ordering of their frames. Its scalar reductions
are whole-interval concavity and intrinsic endpoint
comparisons; no angular sampling is a premise.
