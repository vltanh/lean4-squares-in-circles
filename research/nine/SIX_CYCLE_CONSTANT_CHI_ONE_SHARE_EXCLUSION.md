# Whole-domain exclusion of the constant-corner one-share alternating C6

Date: October 26, 2026.

**Status: accepted complete hand proof after independent saved-source and
physical-scope reviews in REVIEW_C6_CONSTANT_CHI_ONE_SHARE_2026_10_26.md
and REVIEW_C6_ONE_SHARE_COVER_ROOT_2026_10_26.md.** This excludes the entire constant-corner,
exactly-one-share all-unique alternating C6 orbit. Its finite positivity
work is six explicitly displayed rational three-by-three matrices.
There is no force-ratio mesh, recursively subdivided angle domain,
numerical proof premise, or separate coefficient packet. The six
matrix checks are stated openly; this manuscript does not call them
table-free.

Retain the original nine physical squares, selected positive
certificate, all original positive forces, actual application means,
physical unique-corner masks, and the full radius interval

\[
                     79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

The contradiction uses necessary equations of the six actual cycle
bodies. All three extra squares and every actual transmitter position
remain arbitrary and present. This source does not exclude a mixed
corner-bit one-share orbit or close the entire one-share completion
problem.

## 1. Original one-share equations

Use `SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md`,
`SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md`, and the original corner
inequalities in `SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md`.
The reflection-plus-reversal formula for corner bits is independent
of the number of shares. It takes the constant-zero pattern to the
constant-one pattern while carrying all original means. Cyclic
relabeling therefore puts the sole genuine outgoing share at unit 0:

\[
 \chi=(1,1,1),\qquad S_0W_0\text{ genuinely shared},
\]
\[
 f_i=\mu_i n_i,\quad \mu_i>0,\quad |n_i|=1,\quad
 F_i=f_{i-1}-f_i,\quad D_i=|F_i|,
\]
\[
 \pi/2<\theta_i\le3\pi/4,\qquad \sum_i\theta_i=2\pi.
\tag{2}
\]

Set \(s_i=\sin\theta_i\), \(c_i=-\cos\theta_i\),
\(A_i=s_i-c_i\), \(h_i=s_i+c_i\), and
\(\sigma=1/\sqrt2\). The true mean-preserving share equation is

\[
 u_0=-Jn_0,\qquad
 \ell_0=1-(\mu_2/\mu_0)A_0,\qquad 0<\ell_0\le1.
\tag{3}
\]

The other two loaded units have their actual two side vertices as
ports, so \(\ell_1=\ell_2=1\). Their actual support vectors are
\(g_i=f_{i-1}+JF_i\), with \(u_i=g_i/|g_i|\), for
\(i=1,2\). Thus the exact support magnitudes, closure, and virial
identity are

\[
 E_0=\mu_0+h_0\mu_2,
\]
\[
 E_1=\sqrt{2\mu_0^2+\mu_1^2+2h_1\mu_0\mu_1},\quad
 E_2=\sqrt{2\mu_1^2+\mu_2^2+2h_2\mu_1\mu_2},
\]
\[
 \sum_i(n_i+\ell_i u_i)=0,
 \qquad R\sum_iD_i=N:=\sum_i\mu_i+E_0+E_1+E_2.
\tag{4}
\]

These formulas retain the actual shared mean, including a genuine
share whose mean is an endpoint and whose chord is one.

## 2. Two projections give a single triangular angle enlargement

For this section only normalize \(\mu_0=1\), and write
\(\mu_1=p\), \(\mu_2=q\). Put
\(\beta_i=\theta_i-\pi/2\), so
\(0<\beta_i\le\pi/4\) and \(\sum_i\beta_i=\pi/2\).
Choose axes with

\[
 n_0=(1,0),\quad n_1=(-c_1,s_1),\quad n_2=(-c_0,-s_0).
\]

The two nonshared unit directions are

\[
 u_1=(X_1,Y_1)=\frac{(1+ps_1,1+pc_1)}{L},
 \qquad L=\sqrt{2+p^2+2ph_1},
\]
\[
 u_2=(-X_2,Y_2)
 =\frac{p(-h_1,A_1)+q(-s_0,c_0)}{E_2}.
\tag{5}
\]

The positive-vector cone for \(u_1\) lies between directions
\(\beta_1\) and \(\pi/4\), hence \(X_1\le s_1\).
The two summands defining \(u_2\) have directions
\(\pi-(\pi/4-\beta_1)\) and \(\pi-\beta_0\).
Because \(\beta_2\le\pi/4\), one has
\(\pi/4-\beta_1\le\beta_0\). Therefore

\[
                  X_2\ge s_0,\qquad Y_2\ge\sigma A_1.
\tag{6}
\]

The horizontal closure equation is
\(X_2=1-c_0-c_1+X_1\). Using (6) and \(X_1\le s_1\)
gives the first whole-domain angular restriction

\[
                            A_1\ge h_0-1.
\tag{7}
\]

Section 3 of `SIX_CYCLE_CONSTANT_CHI_TWO_SHARE_EXCLUSION.md` proves
the following scalar implication on the complete angle interval:

\[
 \cos y-\sin y\ge\sin x+\cos x-1
 \quad\Longrightarrow\quad y+3x/8\le\pi/4.
\]

Applying that already displayed analytic inequality to
\(x=\beta_0\), \(y=\beta_1\), equation (7) gives

\[
                          y\le\pi/4-3x/8.
\tag{8}
\]

The physical unique-corner inequality for the actual nonshared unit 1
also gives \(p<27/10\), by Section 5 of the complete-domain
source. That source explicitly proves the bound for every unique
nonshared bit-one unit, independently of the number of shares on
other bodies. It applies here with the original force ratio
\(p=\mu_1/\mu_0\).

Since \(L\le p+\sqrt2\), and since
\((1+pc_1)/(p+\sqrt2)\) decreases with \(p\), it follows that

\[
 Y_1\ge\frac{1+(27/10)c_1}{27/10+\sqrt2}
       >\frac{35}{144}+\frac{21}{32}c_1.
\tag{9}
\]

The last comparison uses \(\sqrt2<99/70\), so
\(27/10+\sqrt2<144/35\). The vertical closure equation,
with the actual chord (3), is

\[
 Y_1+Y_2=1+s_0-s_1-qA_0\le1+s_0-s_1.
\]

Equations (6) and (9) consequently give the necessary inequality

\[
 F(x,y):=\frac{109}{144}+\cos x
        -(1+\sigma)\cos y+(\sigma-21/32)\sin y\ge0.
\tag{10}
\]

We next prove the simple global consequence

\[
                             y\ge x-7\pi/80.
\tag{11}
\]

Put \(d=7\pi/80\). Since \(x+y\ge\pi/4\), (11)
already holds when \(x\le27\pi/160\). For the remaining
interval, \(F\) increases with \(y\), because
\(\sigma>21/32\). Define
\(f(x)=F(x,x-d)\), for \(27\pi/160\le x\le\pi/4\).
The second derivative satisfies

\[
 \begin{split}
 f''(x)&=-\cos x+(1+\sigma)\cos(x-d)
                   -(\sigma-21/32)\sin(x-d)\\
       &\ge-1+(53/32)\sigma>0.
 \end{split}
\tag{12}
\]

Here \(0\le x-d\le\pi/4\), and \(\sigma>7/10\).
Thus it suffices to check that both endpoint values of \(f\)
are negative. This is a small fixed Taylor comparison, made explicit
as follows. On \([0,1]\), define

\[
 C_-(t)=1-t^2/2+t^4/24-t^6/720,\quad
 C_+(t)=1-t^2/2+t^4/24,
\]
\[
 S_+(t)=t-t^3/6+t^5/120.
\]

The alternating Taylor remainders give
\(C_-\le\cos\le C_+\) and \(\sin\le S_+\).
Both cosine polynomials decrease and the sine polynomial increases
on this interval. Use
\(3<\pi<22/7\), \(70/99<\sigma<99/140\).
At the left endpoint, the upper estimate is

\[
 \begin{split}
 f(27\pi/160)
 &<\frac{109}{144}+C_+(81/160)
  -(1+70/99)C_-(143/560)\\
 &\hspace{25mm}+(99/140-21/32)S_+(143/560)\\
 &=-\frac{2012570178689899309}{274793126952960000000}<0.
 \end{split}
\tag{13}
\]

At the right endpoint, \(\cos x=\sigma\), and

\[
 \begin{split}
 f(\pi/4)
 &<\frac{109}{144}+\frac{99}{140}
 -(1+70/99)C_-(143/280)\\
 &\hspace{25mm}+(99/140-21/32)S_+(143/280)\\
 &=-\frac{19023159189132991}{68698281738240000000}<0.
 \end{split}
\tag{14}
\]

Convexity gives \(f<0\) on the complete interval. If
\(y<x-d\), monotonicity in \(y\) then gives
\(F(x,y)<f(x)<0\), contradicting (10). This proves (11).

Combining (8), (11), and \(x+y\ge\pi/4\) puts every
original angle triple in the **single** closed triangle with vertices

\[
 \begin{array}{c|ccc}
 &\theta_0&\theta_1&\theta_2\\ \hline
 A&\pi/2&3\pi/4&3\pi/4\\
 B&107\pi/160&93\pi/160&3\pi/4\\
 C&41\pi/55&579\pi/880&105\pi/176.
 \end{array}
\tag{15}
\]

The triangle is an enlargement of the physical domain, not a
subdivision. In particular its largest \(\theta_0\) is strictly
less than \(3\pi/4\); a genuine share with chord one has been
contradicted by closure and the unique-corner inequality, not omitted.

## 3. A homogeneous quadratic controls every positive force ratio

Now normalize \(\mu_0+\mu_1+\mu_2=1\). Put
\(K=79/40\), \(b_i=\sin(\theta_i/2)\), and

\[
 C_0=C_1=2+\sqrt2,\qquad C_2=2+h_0,
 \qquad a_i=1-h_i/\sqrt2\quad(i=1,2).
\tag{16}
\]

The square-root chord inequality, with each adjacent normalized
force sum at most one, gives

\[
 D_i\ge b_i(\mu_{i-1}+\mu_i)
                +(1-b_i)(\mu_{i-1}-\mu_i)^2.
\tag{17}
\]

For each of the two nonshared supports, the square-root tangent
inequality gives

\[
 E_i\le\sqrt2\mu_{i-1}+\mu_i-a_i\mu_{i-1}\mu_i,
                 \qquad i=1,2.
\tag{18}
\]

Indeed its squared norm is
\((\sqrt2\mu_{i-1}+\mu_i)^2
   -2(\sqrt2-h_i)\mu_{i-1}\mu_i\), and its linear leading
term is at most \(\sqrt2\). These are exactly the two general
inequalities derived in Section 4 of the constant-two-share source;
here both nonshared couplings are retained.

It follows that \(K\sum_iD_i-N\ge\mu^{\mathsf T}M\mu\),
where the symmetric matrix is

\[
 M_{ii}=2K-C_i,
\]
\[
 M_{i-1,i}=\frac12\left[
 K\left(\sum_jb_j+3b_i-2\right)-C_{i-1}-C_i
                      +{\bf1}_{i\in\{1,2\}}a_i\right].
\tag{19}
\]

To verify the homogenization directly, the quadratic before
collection is

\[
 (\sum_i\mu_i)\sum_i[K(b_i+b_{i+1})-C_i]\mu_i
 +K\sum_i(1-b_i)(\mu_{i-1}-\mu_i)^2
 +a_1\mu_0\mu_1+a_2\mu_1\mu_2.
\]

Thus no force ratio is selected, bounded by a numerical search, or
partitioned into interval certificates.

## 4. Global quadratic trigonometric bounds

For \(\pi/2\le\theta\le3\pi/4\), the half-angle Taylor
lower bound from the constant-two-share source is

\[
 \sin(\theta/2)\ge
 \frac{\sqrt3}{2}+\frac{\theta-2\pi/3}{4}
                     -\frac{37}{320}(\theta-2\pi/3)^2.
\tag{20}
\]

We use the following stronger global quadratic upper bound for all
three \(h_i\):

\[
 \sin\theta-\cos\theta
       \le\sqrt2-\frac{67}{100}(\theta-3\pi/4)^2.
\tag{21}
\]

For an elementary proof, let \(t=3\pi/4-\theta\in[0,\pi/4]\).
The cosine Taylor upper bound gives

\[
 \sqrt2\cos t
 \le\sqrt2-\sqrt2(1/2-\pi^2/384)t^2.
\]

The coefficient is greater than \(67/100\), because

\[
 \frac{140}{99}\left(\frac12-
                    \frac{(22/7)^2}{384}\right)-\frac{67}{100}
                       =\frac{289}{415800}>0.
\tag{22}
\]

This is a whole-interval upper bound, including equality at
\(\theta=3\pi/4\); it is not a Taylor truncation with an
unstated remainder sign.

Replacing each \(b_i\) by (20) and each \(h_i\) by (21)
in (19) gives an entrywise lower matrix \(\widehat M\).
Every coefficient of \(b_i\) in (19) is positive and every
coefficient of \(h_i\) is negative. Therefore, for the actual
positive force vector,

\[
             \mu^{\mathsf T}M\mu
                     \ge\mu^{\mathsf T}\widehat M\mu.
\tag{23}
\]

No ordering of quadratic forms on signed vectors is inferred from
this entrywise comparison.

## 5. Six exact quadratic controls on the single triangle

Let \(z_A,z_B,z_C\) denote the three rational rows of (15)
after removing the factor \(\pi\). For
\(U,V\in\{A,B,C\}\), including \(U=V\), set

\[
 b_i^{UV}=\frac{\sqrt3}{2}
 +\frac\pi8(z_{U,i}+z_{V,i}-4/3)
 -\frac{37\pi^2}{320}(z_{U,i}-2/3)(z_{V,i}-2/3),
\]
\[
 Q_i^{UV}=\pi^2(z_{U,i}-3/4)(z_{V,i}-3/4),
 \qquad h_i^{UV}=\sqrt2-\frac{67}{100}Q_i^{UV},
\]
\[
 C^{UV}=(2+\sqrt2,\ 2+\sqrt2,\ 2+h_0^{UV}),
 \qquad a_i^{UV}=\frac{67\sqrt2}{200}Q_i^{UV}
                       \quad(i=1,2).
\tag{24}
\]

The expression for \(a_i^{UV}\) uses \((\sqrt2)^2=2\)
exactly; it equals \(1-h_i^{UV}/\sqrt2\). Define the six
symmetric control matrices \(B_{UV}\) by

\[
 (B_{UV})_{ii}=2K-C_i^{UV},
\]
\[
 (B_{UV})_{i-1,i}=\frac12\left[
 K\left(\sum_jb_j^{UV}+3b_i^{UV}-2\right)
 -C_{i-1}^{UV}-C_i^{UV}
                +{\bf1}_{i\in\{1,2\}}a_i^{UV}\right].
\tag{25}
\]

For barycentric coordinates \(\lambda_A,\lambda_B,\lambda_C\)
on the triangle, polarization of each quadratic in (20)--(21) gives
the exact identity

\[
 \widehat M=\sum_U\lambda_U^2B_{UU}
                  +2\sum_{U<V}\lambda_U\lambda_VB_{UV}.
\tag{26}
\]

All six weights are nonnegative and sum to one. There is no recursive
subdivision and no omitted mixed quadratic control.

### 5.1. Explicit rational lower matrices

Use the exact constant bounds already proved by squared reserves and
Machin's formula in Section 6.1 of the constant-two-share source:

\[
 141421/100000<\sqrt2<141422/100000,
\]
\[
 173205/100000<\sqrt3<173206/100000,
\]
\[
 314159/100000<\pi<314160/100000.
\tag{27}
\]

Substitution into the explicit formulas (24)--(25), with rational
interval arithmetic, gives \(B_{UV}>N_{UV}/10000\) entrywise,
where

\[
 N_{AA}=\begin{pmatrix}
 5357&-1346&-5801\\-1346&5357&0\\-5801&0&9490
 \end{pmatrix},\quad
 N_{BB}=\begin{pmatrix}
 5357&-4310&-2475\\-4310&5357&-819\\-2475&-819&5794
 \end{pmatrix},
\]
\[
 N_{CC}=\begin{pmatrix}
 5357&-2714&-1083\\-2714&5357&-3952\\-1083&-3952&5359
 \end{pmatrix},\quad
 N_{AB}=\begin{pmatrix}
 5357&-2358&-3806\\-2358&5357&-199\\-3806&-199&6700
 \end{pmatrix},
\]
\[
 N_{AC}=\begin{pmatrix}
 5357&-1466&-2900\\-1466&5357&-1970\\-2900&-1970&5432
 \end{pmatrix},\quad
 N_{BC}=\begin{pmatrix}
 5357&-3282&-1578\\-3282&5357&-2161\\-1578&-2161&5382
 \end{pmatrix}.
\tag{28}
\]

For reproducibility, evaluate each displayed sum and product in
(24)--(25) by rational interval arithmetic, using the minimum and
maximum of the four endpoint products for multiplication. The minimum
lower-endpoint reserve over all nine entries is:

| Control | Minimum entrywise reserve over \(N_{UV}/10000\) |
| --- | --- |
| \(AA\) | \(77990999/1920000000000\) |
| \(BB\) | \(861418452763/25600000000000000\) |
| \(CC\) | \(96882465720597229/37171200000000000000000\) |
| \(AB\) | \(3872613890129/737280000000000000\) |
| \(AC\) | \(111318954535853/2703360000000000000\) |
| \(BC\) | \(222213135184519/10137600000000000000\) |

All six reserves exceed \(1/500000\). These formulas and explicit
lower matrices are the complete finite entry calculation; no
floating-point sign or external coefficient packet is needed.

### 5.2. Six positive weighted-row identities

Every off-diagonal entry of the matrices (28) is nonpositive. The
following exact integer products prove their positivity:

| Matrix | Positive vector \(w\) | \(Nw\) |
| --- | --- | --- |
| \(AA\) | \((3,1,2)\) | \((3123,1319,1577)\) |
| \(BB\) | \((21,19,12)\) | \((907,1445,1992)\) |
| \(CC\) | \((35,51,45)\) | \((346,377,1698)\) |
| \(AB\) | \((3,2,2)\) | \((3743,3242,1584)\) |
| \(AC\) | \((1,1,1)\) | \((991,1921,562)\) |
| \(BC\) | \((4,4,3)\) | \((3566,1817,1190)\) |

Each coordinate of \(Nw\) exceeds the corresponding coordinate
of \(7w\). For every real vector \(v\), expanding the identity

\[
 v^{\mathsf T}Nv
 =\sum_i\frac{(Nw)_i}{w_i}v_i^2
  +\sum_{i<j}(-N_{ij})w_iw_j
       \left(\frac{v_i}{w_i}-\frac{v_j}{w_j}\right)^2
\tag{29}
\]

therefore proves

\[
            v^{\mathsf T}(N/10000)v
                    \ge\frac7{10000}\sum_i v_i^2.
\tag{30}
\]

This gives all six positivity certificates by explicit positive row
identities, without an eigenvalue calculation.

## 6. Joined whole-domain physical contradiction

For the actual positive force vector, combine the entrywise strict
bounds (28), the six weighted-row identities, and the convex control
decomposition (26):

\[
 \mu^{\mathsf T}\widehat M\mu
      >\frac7{10000}\sum_i\mu_i^2\ge\frac7{30000}.
\]

Equations (19) and (23), followed by removal of the force
normalization, give

\[
 \boxed{\quad
 \frac{79}{40}\sum_iD_i-N
            >\frac7{30000}\sum_i\mu_i>0.
 \quad}
\tag{31}
\]

This holds for every positive force triple and every angle triple in
the one triangle (15), hence for every original constant-corner
one-share configuration. Substitute the true virial identity from
(4). Because \(\sum_iD_i>0\), equation (31) forces
\(R<79/40\), contradicting (1).

The reflection and cyclic operations in Section 1 cover both constant
corner-bit patterns and every placement of the sole genuine share.
The actual mean and its endpoints were retained in the closure input;
the force bound used the actual unique-corner mask; no physical force,
transmitter, or completion square was replaced or optimized away.

The conclusion excludes this entire constant-corner one-share orbit,
with all force ratios and both original radius endpoints. Mixed
corner-bit one-share orbits, the strictly obtuse one-radial family,
the unrestricted sharp inequality, equality classification, and the
earlier prerequisite-chain audit remain separate obligations. No
Lean compilation, CI, workflow dispatch, or numerical proof premise
was used.
