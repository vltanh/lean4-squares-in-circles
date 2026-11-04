# An oriented endpoint toll with coefficient 55/64

November 4, 2026. Complete scalar complement cover and independent
64-bit directed-integer replay. No Lean, Lake or CI. This is a physical
pair inequality; it grants no original-cell or mask closure by itself.

## 1. Original physical theorem

Put

\[
 Q=1105/256,\quad a=46,\quad b=27/2,\quad k=207/16,
 \quad K=211/4.
\]

Let M and B be two original physical unit squares with disjoint open
interiors in the disk of squared radius `R^2<=Q`. Their frames and
centers are independent. In the fixed horizontal direction, suppose M
has canonical angle `theta in [0,pi/4]`. Set
`alpha=cos(theta)`, `beta=sin(theta)`.

Suppose a genuine original owned separating normal from M toward B has
strictly negative vertical component. Then

\[
\begin{split}
 a[-x_M-h_M]+b[-x_B-h_B]
 &+\frac{1265}{32}\beta
 -\frac{119}{2}(1-\alpha)\le K.                 \tag{1}
\end{split}
\]

It is strict if `R^2<Q`. Equivalently, the normalized main-endpoint toll is

\[
 T_{\rm good}(\theta)=\frac{55}{64}\beta
                         -\frac{119}{92}(1-\alpha).     \tag{2}
\]

The normal retains its actual original owner. The theorem does not
replace physical square separation by incircle separation. Its
hypothesis is supplied by the endpoint corollary of
`SHORT_ROW_COMMON_SIDE_HAND_PROOF.md` in the four-row application.

A reflection in the horizontal axis sends the separator's vertical
component positive and M's angle to `-theta`. Work in that reflected
frame below, without changing either physical square or the load.

## 2. Circle support and the actual separator

Write the signed unit separator as `n=(c,s)`, where
`-1<=c<=1` and `s=sqrt(1-c^2)>=0`. The strict vertical condition may be
closed to include `s=0`; proving the larger scalar domain is safe.
Define

\[
 L_w(c)=\sqrt{w^2+k^2+2wkc},\quad
 H(c)=\sqrt Q\,[L_a(c)+L_b(-c)].
\]

The physical separation inequality, multiplied by `k`, and circle
support in directions `-ae-kn` and `-be+kn`, give

\[
 a[-x_M-h_M(e)]+b[-x_B-h_B(e)]\le H(c)-P_M-P_B,            \tag{3}
\]

where `e=(1,0)` and

\[
\begin{split}
 P_M&=a h_M(e)+h_M(ae+kn)+k h_M(n),\\
 P_B&=b h_B(e)+h_B(be-kn)+k h_B(n).
\end{split}
\]

This is the same original support reduction as the accepted unrestricted
pair cap. Replacing `R` by `sqrt(Q)` is strict for `R^2<Q`, because the
sum of vector lengths in `H` is positive.

In the reflected frame, M has axes `(alpha,-beta),(beta,alpha)`.
Both coordinates of `ae+kn` in these axes are nonnegative: the first
is at least `a alpha-k>0`, and the second is
`(a+kc)beta+ks alpha>=0`. Therefore its support resolves exactly to

\[
 P_M=a(\alpha+\beta)
       +k\{(c\alpha-s\beta)_+ +(c\beta+s\alpha)_+\}.       \tag{4}
\]

Here `t_+=max(t,0)`; neither sign in the support of the actual normal is
assumed in (4).

## 3. Complete ownership and free-frame union

If B owns the normal, its support contribution is exactly

\[
 N_b(-c)=\frac{b|c|+2bs+|k-bc|+k}{2}.                    \tag{5}
\]

Thus the B-owned scalar row is

\[
 G(c,z)=K-H(c)+P_M+N_b(-c)-\tau,                         \tag{6}
\]

where

\[
 \tau=(a-k/2)\beta-(a+b)(1-\alpha),\qquad
 z=\tan(\theta/2),\quad
 \alpha=\frac{1-z^2}{1+z^2},\quad\beta=\frac{2z}{1+z^2}.
\]

If M owns the normal, the two possible axes with strictly positive
vertical component, together with their limiting faces, are

\[
 n=(\beta,\alpha)\quad\text{or}\quad n=(-\alpha,\beta).
\]

Their main contributions in (4) are respectively
`a(alpha+beta)+k` and `a(alpha+beta)`. No owned axis is dropped.

For the free B frame, its support sum is the sum of the two widths of
the triangle with edge vectors `be`, `be-kn`, `kn`. Between projection
sign changes it is a positive sine/cosine expression with second
derivative equal to its negative. Its minimum is therefore at a frame
parallel to one of the three triangle edges. The resulting complete
candidate list, for a general argument t and `v=sqrt(1-t^2)`, is

\[
\begin{split}
 E_b(t)&=b+k[v+\max(t,0)],\\
 N_b(t)&=(b|t|+2bv+|bt+k|+k)/2,\\
 D_b(t)&=\frac{L_b(t)^2+b^2+bkt+2bkv+k|bt+k|}{2L_b(t)}.
\end{split}                                                     \tag{7}
\]

Use `t=-c`. It suffices to verify the scalar row with each candidate
in (7), for each of the two actual M-owned axes. This is the full
owner/frame union, retaining both original frames.

## 4. Exact sharp tangent and the zero neighborhood

Direct rational identities give

\[
 a^2+k^2=23^2Q,\quad b^2+k^2=9^2Q,
\]

\[
 H(0)=32Q=a+b+2k+K,\qquad H'(0)=k/2.
\]

Concavity of both square roots implies the global tangent bound

\[
 H(c)\le H(0)+(k/2)c.                                   \tag{8}
\]

It is strict for `c!=0`.

### M-owned positive shallow component

For `n=(beta,alpha)`, the N candidate is `b alpha+k`, because
`beta<=1/sqrt(2)<k/b=23/24`. Its scalar row is nonnegative directly by
(8), with all remaining terms canceling to zero. The E candidate is
`b+k alpha`, larger by `(b-k)(1-alpha)>=0`. These two full-angle rows
therefore need no interval subdivision. Their equality forces `beta=0`
by strict concavity in (8).

The D candidate and all three rows for `n=(-alpha,beta)` have positive
finite interval covers in Section 5.

### B-owned zero neighborhood

Consider the closed region `|c|<=1/4`, `0<=z<=1/20`. Then

\[
 \alpha\ge99/100,\quad 0\le\beta\le1/10,\quad
 s\ge121/125,\quad c\beta+s\alpha>0.
\]

In this region (5) becomes `b s+k+b(-c)_+`. After using (8), the
lower bound for (6), divided by k, is

\[
 Z=(c\alpha-s\beta)_+ +(c\beta+s\alpha)_+-1
       +r(s-\alpha)+r(-c)_+-(c-\beta)/2,
 \quad r=b/k=24/23.                                    \tag{9}
\]

At `c=beta`, one has `s=alpha` and `Z=0` exactly. The first positive
part changes branch exactly there; the second is strictly positive.

For `-1/4<=c<=0`, differentiation of its fixed branch gives

\[
 Z'=-\frac c s(\alpha+r)+\beta-\frac12-r
 \le\frac{125}{484}(1+r)+\frac1{10}-\frac12-r
 =-\frac{50969}{55660}<0.
\]

For `0<=c<=beta`, the derivative is at most `beta-1/2<=-2/5`.
Hence `Z>=Z(beta)=0` throughout `c<=beta`.

For `beta<=c<=1/4`,

\[
 Z=c(\alpha+\beta-1/2)
       +s(\alpha-\beta+r)-1-r\alpha+\beta/2.
\]

This is concave in c, since `alpha-beta+r>0`. Its minimum occurs at
an endpoint. One endpoint is `Z(beta)=0`. At `c=1/4`, write

\[
 Z=\alpha(c+s-r)+\beta(c-s+1/2)+rs-1-c/2.
\]

Here `c+s-r>0` and `c-s+1/2>=-1/4`. Consequently

\[
 Z(1/4)\ge
 \frac{99}{100}\left(\frac14+\frac{121}{125}-r\right)
 -\frac1{40}+r\frac{121}{125}-1-\frac18
 =\frac{37793}{1150000}>0.
\]

This proves the entire closed zero neighborhood. Its scalar equality
requires `c=beta=0`, again using the strict tangent inequality when
`c!=0`.

## 5. Complete finite complement

The physical half-angle range has `z<=sqrt(2)-1<5/12`. The rational
upper comparison follows from `(17/12)^2-2=1/144>0`. The finite
certificate covers the larger rational range `0<=z<=5/12`; all
denominators stay positive there.

`ORIENTED_GOOD_ENDPOINT_TOLL_COVER.json` contains the three closed
B-owned complement roots

- `c in [-1,-1/4]`, `z in [0,5/12]`;
- `c in [1/4,1]`, `z in [0,5/12]`;
- `c in [-1/4,1/4]`, `z in [1/20,5/12]`.

Together with Section 4 these cover every B-owned scalar case,
including all shared boundaries. The other four roots are the
M-owned `Mv_D`, `Mu_E`, `Mu_N`, `Mu_D` rows on `[0,5/12]`.

Every split retains both closed halves. Every terminal has a strictly
positive exact interval lower bound. There are 6,170 leaves, maximum
depth 20, and no frontier. A separate checker using outward integer
arithmetic at denominator `2^64` reconstructs and verifies every leaf;
it imports no producer or numerical code. Its least positive reserve is

\[
 2041502494679/72057594037927936>0.
\]

The checker also verifies thirteen exact rational identities and
comparisons in the analytic proof. `ORIENTED_GOOD_ENDPOINT_TOLL_EXACT_REPLAY.json`
records the complete result and source hashes. The scalar union plus
(3) proves (1) for the genuine original physical pair.

## 6. Equality

Every scalar equality requires `beta=0`, `c=0`, and the free B frame
aligned with the horizontal/vertical directions; the positive-table
rows have no equality. The circle-support equalities in the reflected
frame then give centers `M=(-3/2,-1/16)` and `B=(-1,15/16)`.
Reflecting back gives `M=(-3/2,1/16)`, `B=(-1,-15/16)`.
The equality statement is only for the normalized fixed direction and
centered disk of the theorem. No equality is asserted at nonzero tilt.
