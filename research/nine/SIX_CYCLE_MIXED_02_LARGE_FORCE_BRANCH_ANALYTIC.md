# Mixed two-share C6: the complementary force ordering is impossible

Date: October 25, 2026.

**Status: complete analytic branch proof accepted after independent full
saved-source and physical-scope review.** See
`REVIEW_C6_MIXED_02_LARGE_FORCE_AND_JOIN_2026_10_26.md` and the root
join audit in `REVIEW_C6_CONTACT_TYPE_CLOSURES_ROOT_2026_10_25.md`.
This proves the complementary
force ordering in the mixed corner pattern 110 with genuine shares at
loaded units 0 and 2. Together with
`SIX_CYCLE_MIXED_02_SMALL_FORCE_BRANCH_ANALYTIC.md`, its reviewed join
excludes that entire contact type. The other two-share types and the
remaining one-share completion problem are separate obligations.

Retain all nine original physical squares, the common selected
certificate, all original positive forces, shared means and physical
circle masks, and

\[
                  79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

All three alternating loaded squares have exactly one physical circle
corner each. The other three cycle bodies are the original unloaded
side-normal transmitters, with their true degree-two equations. The
three additional squares and all actual transmitter positions remain
present. Every genuine shared-mean endpoint is retained.

## 1. The exact complementary ordering and closure equations

Use the complete physical cover in
`SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md`. Normalize only
the common positive force scale, writing

\[
 (\mu_0,\mu_1,\mu_2)=(1,p,q),\qquad p,q>0,
 \qquad (\chi_0,\chi_1,\chi_2)=(1,1,0).
\]

The two genuine shares are the outgoing interface at unit 0 and the
incoming interface at unit 2. For all three true force turns put

\[
 s_i=\sin\theta_i,\quad c_i=-\cos\theta_i,\quad
 t_i=s_i-c_i,\quad h_i=s_i+c_i,
 \quad r=1/\sqrt2.
\tag{2}
\]

The original domain is

\[
 \pi/2<\theta_i\le3\pi/4,\quad\sum_i\theta_i=2\pi,
 \quad r\le s_i<1,
 \quad 0<c_i\le r,
 \quad t_i\ge0.
\tag{3}
\]

Rotate the actual normals to
\(n_0=(1,0)\), \(n_1=(-c_1,s_1)\),
\(n_2=(-c_0,-s_0)\). The middle nonshared unit has

\[
 L=\sqrt{2+p^2+2p h_1},\qquad
 u_1=(X,Y)=\left(\frac{1+p s_1}{L},
                        \frac{1+p c_1}{L}\right).
\tag{4}
\]

In particular the constant term of \(L^2\) is 2. The original
shared chords are

\[
 \ell_0=1-q t_0>0,\quad u_0=-Jn_0,
 \qquad \ell_2=1-(q/p)t_2>0,\quad u_2=Jn_1.
\tag{5}
\]

All upper endpoints \(\ell_i=1\) remain permitted. The original
closure \(\sum(n_i+\ell_i u_i)=0\) gives exactly

\[
 X=h_1+c_0-1-(q/p)t_2s_1,
\tag{6}
\]
\[
 (q-1)t_0=2(1-s_1)+t_1\left(\frac pL+\frac qp t_2\right).
\tag{7}
\]

For an independent derivation of (7), take the vertical closure
component and eliminate the horizontal component with (6). Use
\(Y-c_1X/s_1=t_1/(Ls_1)\) and the angle identities

\[
 c_2=s_0s_1-c_0c_1,\qquad
 t_2=h_1c_0-t_1s_0,\qquad
 c_0-s_1t_2=t_1c_2.
\tag{8}
\]

Alternatively (7) is the unchanged identity (7) of the small-force
branch source. Its right side is strictly positive, since
\(s_1<1\). Because \(t_0\ge0\), every actual configuration
therefore has

\[
                         q>1,\qquad t_0>0.
\tag{9}
\]

The complementary ordering considered here is \(q<p\). The
nonshared bit-one corner bound (11) in the complete-domain source is
an inequality for this actual unit 1; it gives

\[
                          1<q<p<27/10.
\tag{10}
\]

This bound uses the unit's unique physical circle corner, not an
assumption that a merely loaded corner is its only boundary corner.

## 2. One scalar gap for the middle side direction

Define

\[
 U=h_1-1+r t_1=(1+r)s_1+(1-r)c_1-1.
\tag{11}
\]

We need only two elementary uniform bounds:

\[
 \begin{array}{ll}
 X-U>1/12,&p\ge1,\\[2pt]
 X-U>27/200,&p\ge21/10.
 \end{array}
\tag{12}
\]

Here is a whole-angle proof of both. Regard \(s=s_1,c=c_1\)
as fixed. Differentiating (4) with respect to \(p\) gives

\[
 \frac{\partial X}{\partial p}
       =\frac{(s-c)(1+pc)}{(2+p^2+2p(s+c))^{3/2}}\ge0.
\tag{13}
\]

Thus for any fixed \(p_0\le p\), since \(s+c\le\sqrt2\),

\[
 X\ge X(p_0)
       \ge\frac{1+p_0s}{p_0+\sqrt2}.
\tag{14}
\]

Put \(v=1/(p_0+\sqrt2)\). Subtract (11) from (14) and apply
Cauchy to \((s,c)\), whose squared norm is one:

\[
\begin{aligned}
 X-U
 &\ge 1+v-r(1+2v)s-(1-r)c\\
 &\ge 1+v-
       \sqrt{2-\sqrt2+2v+2v^2}.
\end{aligned}
\tag{15}
\]

For a proposed positive gap \(\epsilon<1\), the last expression
is greater than \(\epsilon\) whenever

\[
 \sqrt2-1-2\epsilon+\epsilon^2
                   -2\epsilon v-v^2>0.
\tag{16}
\]

Indeed \(1+v-\epsilon>0\), and (16) is exactly the difference
of the squares of this number and the radical in (15). There is no
sign ambiguity when taking the square root.

Use \(\sqrt2>140/99\), whose squared reserve is
\(2-(140/99)^2=2/9801>0\), and hence
\(v<1/(p_0+140/99)\). The expression in (16) increases with
the first occurrence of \(\sqrt2\) and decreases with positive
\(v\). Substitution gives the following exact positive lower bounds:

| \(p_0\) | \(\epsilon\) | Upper bound on \(v\) | Rational lower bound in (16) |
| --- | --- | --- | --- |
| \(1\) | \(1/12\) | \(99/239\) | \(1248475/90479664\) |
| \(21/10\) | \(27/200\) | \(990/3479\) | \(218416231211/47929626360000\) |

This proves (12) for all actual angles, including
\(\theta_1=3\pi/4\). The table consists of the two displayed
fixed substitutions in one quadratic; it is not an angle or force
interval certificate.

## 3. Closure turns the scalar gap into an impossible force ratio

Subtract the hypothetical value \(q=p\) from (6), using (8):

\[
 (p-q)t_2
       =\frac p{s_1}\,[X-h_1+1-t_1c_2]
       \ge\frac p{s_1}(X-U).
\tag{17}
\]

The inequality follows from \(c_2\le r\) and \(t_1\ge0\).
If either bound \(X-U>\epsilon\) in (12) is used, then

\[
                  (p-q)t_2>p\epsilon,
\tag{18}
\]

since \(s_1\le1\). In particular \(t_2>0\); a genuine share
with \(t_2=0\), equivalently its endpoint mean \(\ell_2=1\),
is already excluded by (17), not dropped from the argument.

Set

\[
 a=q-1>0,
 \quad b=p-q>0,
 \quad z=1-s_1>0.
\]

Equation (7) and (18) give

\[
                    a t_0\ge2z,\qquad b t_2>p\epsilon.
\tag{19}
\]

There is also a uniform bound on the sum of the two actual angular
parameters. Put \(\beta_i=\theta_i-\pi/2\); then
\(t_i=\cos\beta_i-\sin\beta_i\), and
\(\beta_0+\beta_2=\pi-\theta_1\). The sum-to-product identity
therefore gives

\[
\begin{aligned}
 t_0+t_2
 &=2\cos\frac{\beta_0-\beta_2}{2}
       \left(\sin\frac{\theta_1}{2}
                    -\cos\frac{\theta_1}{2}\right)\\
 &\le2\sqrt{1-\sin\theta_1}=2\sqrt z.
\end{aligned}
\tag{20}
\]

The bracket is positive because \(\theta_1>\pi/2\). Cauchy,
(19), and \(a+b=p-1\) now imply

\[
\begin{aligned}
 2(p-1)\sqrt z
 &\ge(p-1)(t_0+t_2)\\
 &\ge\bigl(\sqrt{a t_0}+\sqrt{b t_2}\bigr)^2\\
 &>\bigl(\sqrt{2z}+\sqrt{p\epsilon}\bigr)^2.
\end{aligned}
\tag{21}
\]

Divide by \(2\sqrt z>0\). Applying the arithmetic-geometric
mean inequality to \(\sqrt z+p\epsilon/(2\sqrt z)\) gives

\[
 p-1>\sqrt z+\sqrt{2p\epsilon}
                     +\frac{p\epsilon}{2\sqrt z}
       \ge2\sqrt{2p\epsilon}.
\]

Consequently every actual complementary-ordering configuration would
have to satisfy

\[
                         \frac{(p-1)^2}{p}>8\epsilon.
\tag{22}
\]

The function on the left is strictly increasing for \(p>1\).
For \(1<p\le21/10\), use the first bound in (12):

\[
 \frac{(p-1)^2}{p}\le\frac{121}{210}
       <\frac23=8\left(\frac1{12}\right),
 \qquad \frac23-\frac{121}{210}=\frac{19}{210}>0.
\tag{23}
\]

For \(21/10\le p<27/10\), use the second bound in (12):

\[
 \frac{(p-1)^2}{p}<\frac{289}{270}
       <\frac{27}{25}=8\left(\frac{27}{200}\right),
 \qquad \frac{27}{25}-\frac{289}{270}=\frac{13}{1350}>0.
\tag{24}
\]

Both contradict (22). The displayed split chooses which of two
uniform scalar constants to use; neither interval is checked by a
mesh or a computational sign table. Thus the entire \(q<p\)
branch is impossible.

## 4. Original physical join and remaining scope

The positive force normalization covers every original force triple.
The two orderings \(q\ge p\) and \(q<p\) are exhaustive and
include the equality boundary in the first branch. The small-force
source gives a strict radius contradiction on the first branch;
Sections 1--3 give a strict closure contradiction on the second.
Independent full review of both sources passed; their join excludes
the complete mixed 110, shares 0/2 contact type.

The crucial upper bound \(p<27/10\) concerns the actual nonshared
unit 1 and follows from its physical unique-corner mask. All other
physical circle masks were already fixed by this all-unique branch;
none is inferred from a selected nonzero corner weight. The true
loaded and transmitter degrees, original force normals and actual
means remain unchanged. The two strict contradictions do not require
moving a transmitter, replacing a shared side by a singleton, or
constraining the three extra squares.

The constant-bit and mixed 110 shares 0/1 two-share types require
their own complete proofs. The remaining one-share completion problem,
strictly obtuse one-radial family, global sharp inequality, all
original equality packings and earlier prerequisite-chain audit are
not closed by this source. No original roadmap ID is newly checked
by this branch alone. No Lean compilation, CI, workflow dispatch,
numerical proof premise or coefficient packet is used.
