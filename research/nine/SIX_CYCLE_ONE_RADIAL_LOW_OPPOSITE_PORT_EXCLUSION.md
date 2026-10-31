# A single opposite-port curve excludes the complete low-turn opposite family

Date: October 26, 2026.

**Status: accepted complete analytic physical-family proof**, after
REVIEW_C6_RADIAL_LOW_OPPOSITE_PORT_CERTIFICATE_REDUCTION_2026_10_26.md and
REVIEW_C6_RADIAL_LOW_REMAINING_ROOT_2026_10_26.md. All strict partner types are compared by the same connected
opposite-port curve. No force-ratio box, sampled pose or computational
certificate is used.

Retain the original alternating all-side C6, the one physically radial
loaded square S with both individual circle weights positive, the two
physically unique loaded squares L,T, the three true unloaded degree-two
side transmitters, every original positive force, normal and application
mean, all mean endpoints and transmitter sliders, and all nine actual
physical squares. The individual zero-weight endpoints retain their
separate accepted exclusion.

Assume L has turn at most \(\pi/2\), neither original interface
at L is genuinely owned, and its actual S-incident application is
its opposite-to-circle vertex. An originally owned mean whose
endpoint happens to be that vertex retains its owner row and is not
included by this premise. The complete low-turn
cover in `SIX_CYCLE_ONE_RADIAL_LOW_TURN_FEATURE_COVER.md` makes
both L interfaces nonowned and its actual return application the
adjacent vertex on the same inner side. The two reflected versions
are retained. T has strict unique turn and the complete A/M/O/T
feature cover.

**Theorem.** No nine-square completion of this entire original family
exists in the target radius window.

For a completion, the global measure theorem supplies \(R>2\).
It suffices to work on
\[
 2\le R\le\sqrt{1105}/16,
 \qquad d=\sqrt{R^2-1/4}-1,
 \qquad d_0=\sqrt{15}/2-1\le d<61/60.
\tag{1}
\]
Let alpha and beta be the two actual radial-port angles, at L and T.
The original force-polygon turns give
\[
 \theta_S=\pi-\alpha-\beta,
 \qquad \theta_L+\theta_T=\pi+\alpha+\beta,
 \qquad0<\alpha,\beta,\quad\alpha+\beta\le\pi/4.
\tag{2}
\]

## 1. The exact opposite-port scalar equation

At any actual opposite S port choose the matching reflected own
chart so its actual circle corner and port are
\[
 z=(a,b),\qquad Q=(a-1,b-1),\qquad a>b>1/2,
                  a^2+b^2=R^2.
\]
Let \(q=(1-t)z\), \(0\le t<1\), be its unchanged proper
concurrence. Its strict opposite-vertex normal has
\[
 X=1-ta>0,\quad Y=1-tb>0,\quad
 G=(x,y)=\frac{(X,Y)}{\sqrt{X^2+Y^2}},
 \qquad0<x\le y.
\tag{3}
\]
Write
\[
 x=\cos\eta,\quad y=\sin\eta,\quad
 \pi/4\le\eta<\pi/2,\qquad
 m=x+y,\quad n=y-x.
\tag{4}
\]
The positive original moment fixes \(a>b\); the case \(t=0\)
and all genuine means at that endpoint remain in the comparison.

In the actual radial-port frame, with its complete reflection if
needed, write the radial angle as gamma:
\[
 P=(d,1/2),\qquad G=(-\cos\gamma,\sin\gamma),
                  P=Q-G.
\]
Define
\[
 k=d\cos\gamma-\tfrac12\sin\gamma,
 \qquad w=1-k,
 \qquad h=d\sin\gamma+\tfrac12\cos\gamma.
\tag{5}
\]
Then \(P\cdot G=w-1\). In the actual own coordinates,
\[
 \det(P,G)=\frac{(1-t)(a-b)}{\sqrt{X^2+Y^2}}>0,
\]
so its sign selects h, not -h. Consequently
\[
                   a=1+wx+hy,\qquad b=1+wy-hx.
\tag{6}
\]
Squaring and using \(|P|^2=d^2+1/4\) gives the exact original
circle equation
\[
        \boxed{f(n,\gamma,d):=w(m+1)+hn-d=0,}
            \qquad m=\sqrt{2-n^2}.
\tag{7}
\]
The proper concurrence further gives
\[
 t=\frac n{h+n},\qquad
 \ell:=\sqrt{X^2+Y^2}=\frac{hm-wn}{h+n},\qquad
 X=\ell x,\quad Y=\ell y.
\tag{8}
\]
These formulas apply to both opposite-port partner types O and T;
they do not assume that its return is nonowned. The actual return
choice will enter only in Section 3.

## 2. A complete connected comparison curve, with its endpoint signs

Fix d in \([d_0,61/60]\). We now define (7) on the closed scalar
domain
\[
                   0\le n\le1,\qquad0\le\gamma\le\pi/4.
\tag{9}
\]
Every original opposite port in (2) belongs to this domain. Scalar
comparison endpoints may have an axis normal; no actual nonowned
interface is relabeled by using such a continuous endpoint.

On (9), k and h are positive. Also
\[
 \begin{split}
 h-w
 &=(d+1/2)\cos\gamma+(d-1/2)\sin\gamma-1\\
 &>\frac{287}{200}\frac7{10}-1=\frac9{2000}>0.
 \end{split}
\tag{10}
\]
Here \(d>187/200\), \(\cos\gamma\ge1/\sqrt2>7/10\)
and \(d>1/2\). Thus
\[
 f_n=h-w\frac n m>0,
 \qquad f_\gamma=h(m+1)+kn>0,
\]
\[
 f_d=-(m+1)\cos\gamma+n\sin\gamma-1<0.
\tag{11}
\]
For the first sign, if w is negative it is immediate; otherwise
use \(n/m\le1\) and (10). For the last sign, use
\(\cos\gamma\ge\sin\gamma\) and \(m\ge n\).

At gamma zero, the first sign shows
\[
 f(n,0,d)\le f(1,0,d)=5/2-3d<-61/200<0.
\]
At gamma \(\pi/4\), the minimum over n is at zero. Since
\(1/\sqrt2<5/7\), its w exceeds \(53/84\), and
\[
 f(0,\pi/4,d)
 >\frac{53}{84}\frac{12}{5}-\frac{61}{60}
 =\frac{209}{420}>0.
\tag{12}
\]
Therefore for every n, equivalently every
\(\eta\in[\pi/4,\pi/2]\), there is exactly one root
\(\gamma=\gamma_d(\eta)\) strictly between zero and \(\pi/4\).
It is continuous on the closed interval and differentiable in its
interior, with a positive implicit denominator. No numerical root
choice or disconnected interpolation is used.

Along this complete curve, (6),(8) have the following useful signs.
First \(w\ge1-d\ge-1/60\), so \(a>59/60\). Since h increases
with gamma and gamma is at most \(\pi/4\),
\[
 h\le(d+1/2)/\sqrt2,\qquad x\le1/\sqrt2,\qquad
 b\ge1-1/60-91/120=9/40>0.
\tag{13}
\]
Also \(a-b=hm-wn>0\) by (10), and \(\ell>0\).
Thus \(0\le t<1\), \(1-ta=\ell x\ge0\), and
\(1-tb=\ell y>0\). In the open eta interval, \(ta<1\).
The functions in (6) satisfy \(a^2+b^2=d^2+2d+5/4\) identically.
The actual strict inequalities a,b>1/2 are not needed at artificial
comparison points; the stronger signs used in the calculus have
just been proved directly on the entire curve.

## 3. Two angle monotonicities compare both return types at once

A prime in this section differentiates along the curve with respect
to eta, while d remains fixed. Since \(m'=-n,n'=m\), (7) gives
\[
 \gamma'=-\frac{hm-wn}{h(m+1)+kn}
          =-\frac{\ell}{1+\ell}.
\tag{14}
\]
For the second equality, \(k+w=1\) gives the exact denominator
identity
\[
 h(m+1)+kn=(hm-wn)+(h+n)=(1+\ell)(h+n).
\]
In particular
\[
                         (\gamma+\eta)'=\frac1{1+\ell}>0.
\tag{15}
\]

For an O return, the actual adjacent vertex is \((a-1,b)\).
The proper vector from concurrence to that vertex is
\[
 N=t(a,b)-(1,0)=(-\ell x,tb).
\tag{16}
\]
Define its continuous comparison turn by
\[
                      \theta(\eta)=\arg N-\eta.
\tag{17}
\]
For interior eta, N has strictly negative first and positive second
coordinate, so its argument is the unambiguous value between
\(\pi/2\) and \(\pi\). Formula (17) is exactly the original
force turn when the return is the actual nonowned adjacent feature.
It is only a comparison function when the actual return is owned.

Put \(\tau=1-t\). Differentiating (6) and using (8),(14) gives
\[
               a'=-\frac{\tau b}{1+\ell},
               \qquad b'=\frac{\tau a}{1+\ell}.
\tag{18}
\]
Moreover
\[
        t'=\frac{hm-nk\gamma'}{(h+n)^2}>0.
\tag{19}
\]
All factors in these identities have their whole-curve signs from
Section 2. Let \(\rho=|N|>0\). From (16),(18),
\[
 \det(N,N')
   =\frac{t^2\tau R^2-t\tau a}{1+\ell}-t'b,
 \qquad \rho^2=1-2ta+t^2R^2.
\]
Combining this with (14),(17), the exact derivative numerator is
\[
 (1+\ell)\rho^2(\theta-\gamma)'
  =-1+ta(1+t)-t^3R^2-(1+\ell)t'b.
\tag{20}
\]
Write \(u=ta<1\). Since \(R^2\ge a^2\), the right side is at
most
\[
           -(1-u)(1-tu)-(1+\ell)t'b<0.
\tag{21}
\]
Thus
\[
                  \boxed{(\theta-\gamma)'<0.}
\tag{22}
\]
In particular \(\theta'<0\), since \(\gamma'<0\) as well.
This sign is proved on the whole continuous interval, not merely
at actual selected contact parameters.

At eta \(\pi/4\), n=t=0, \(\ell=\sqrt2\), and N=(-1,0),
so \(\theta=3\pi/4\). At eta \(\pi/2\), x=0 and
\[
             0<\ell=(h-w)/(h+1)<1,
\]
so N is vertical positive and \(\theta=0\). All expressions
remain continuous at these endpoints. Therefore there is exactly
one eta with \(\theta=\pi/2\). Define
\[
 \gamma_{\max}=\gamma_d(\pi/4),
 \qquad
 \gamma_{\rm right}=\gamma_d(\eta_{\rm right}).
\tag{23}
\]
The monotonicities prove the complete comparison table:

| Actual endpoint/return | Whole-curve consequence |
| --- | --- |
| Opposite port, nonowned return, \(\theta\le\pi/2\) | \(\theta-\gamma\le\pi/2-\gamma_{\rm right}\) |
| Any opposite port with nonowned adjacent return | \(\theta-\gamma\le3\pi/4-\gamma_{\max}\) |
| Opposite port with genuine owned return | \(\gamma+\eta\ge\pi/4+\gamma_{\max}\) |

For the last row, the actual owned return direction is (-1,0),
so its actual turn is \(\pi-\eta\). Its full original mean is
already in (3),(8); no mean value is chosen in the comparison.

## 4. Two broad uniform endpoint bounds

We prove, throughout the entire radius interval,
\[
             \boxed{\gamma_{\max}>23/50,
                    \qquad \gamma_{\rm right}>33/100.}
\tag{24}
\]
Only elementary Taylor inequalities and two monotone polynomial
bounds are needed. The displayed fixed rational reserves can be
checked directly; there is no parameter subdivision.

### 4.1 The maximal gamma endpoint exceeds 23/50

Let \(v=23/50\), \(\delta=187/200<d\). For the fixed endpoint
n=0, use the decreasing d sign in (11),
\(1+\sqrt2<17/7\), and the signed Taylor bounds
\[
 S_5(v)=v-v^3/6+v^5/120,
 \qquad C_6(v)=1-v^2/2+v^4/24-v^6/720.
\]
The comparison w is positive because \(\delta<1\). Thus
\[
 \begin{split}
 f(0,v,d)
 &<\{1-\delta C_6(v)+S_5(v)/2\}\frac{17}{7}-\delta\\
 &=-\frac{31921699403869}{15750000000000000}<0.
 \end{split}
\tag{25}
\]
Since f increases strictly with gamma, its root at n=0 exceeds v.

### 4.2 Every gamma at most 33/100 has turn below a right angle

Suppose \(\gamma\le v:=33/100\). Put
\[
 \delta_*=18729/20000<d_0,
 \qquad n_*=9/25,\qquad m_*=171/125.
\]
The exact positive-square reserves are
\[
 15/4-(1+\delta_*)^2=64559/400000000,
 \qquad m_*^2-(2-n_*^2)=16/15625.
\tag{26}
\]
The gamma-increasing and d-decreasing signs in (11) reduce
\(f(n_*,\gamma,d)\) to \(f(n_*,v,\delta_*)\).
Its comparison w is positive. Using
\[
 C_2(v)=1-v^2/2,\quad C_4(v)=1-v^2/2+v^4/24,\quad
 S_5(v)=v-v^3/6+v^5/120,
\]
and \(\sqrt{2-n_*^2}<m_*\), we obtain
\[
 \begin{split}
 f(n_*,\gamma,d)
 &<\{1-\delta_*C_2(v)+S_5(v)/2\}(m_*+1)\\
 &\quad+\{\delta_*S_5(v)+C_4(v)/2\}n_*-\delta_*\\
 &=-\frac{404586506921509}{200000000000000000}<0.
 \end{split}
\tag{27}
\]
Since f increases with n and the actual comparison point has f=0,
\[
                               n>9/25.
\tag{28}
\]

On this entire small-gamma interval,
\[
 h<\frac{61}{60}\gamma+
       \frac12(1-\gamma^2/2+\gamma^4/24)
 \le\frac{1293635307}{1600000000}<\frac{81}{100}.
\tag{29}
\]
The upper polynomial increases there, and the last reserve is
\(2364693/1600000000>0\).

It remains to prove the actual turn is below \(\pi/2\), not merely
to bound the auxiliary normal angle. Put
\[
                           E=n(w+y)-hx.
\]
From (8),
\[
                     y-\ell=\frac E{h+n}.
\tag{30}
\]
The circle equation gives \(w=(d-hn)/(m+1)\). Substituting this
in E and using \(d>187/200\), \(h<81/100\), with all signed
coefficients explicit, gives
\[
        2(m+1)E>P(n)+A(n)(m-1),
\tag{31}
\]
where
\[
 A(n)=n^2+\frac{181}{100}n-\frac{81}{100},
\]
\[
 P(n)=-n^3+\frac{119}{100}n^2
                       +\frac{649}{100}n-\frac{243}{100}.
\tag{32}
\]
For clarity, before substitution the coefficient of d is 2n>0,
and the coefficient of h is
\(-2\{n^2+x(m+1)\}<0\); hence both replacements in (31) are
valid lower bounds.

On \(9/25\le n\le1\), A increases and
\(P'>349/100>0\). Their exact endpoint values are
\[
                A(9/25)=-18/625,
                \qquad P(9/25)=873/62500.
\]
Since \(0\le m-1<3/7\), whether A is positive or negative,
\[
 P(n)+A(n)(m-1)
 >\frac{873}{62500}-\frac{18}{625}\frac37
 =\frac{711}{437500}>0.
\tag{33}
\]
Therefore E>0. Formula (30) makes the scalar product of G with
the return vector positive, because that product is
\(y-\ell\). The comparison turn is strictly below \(\pi/2\).
In particular its unique right-turn point cannot have
\(\gamma\le33/100\), proving the second part of (24).

## 5. The actual turn sum excludes every strict partner

For the actual low endpoint L, its actual opposite/nonowned chart
lies on the curve above. Sections 3--4 give the uniform strict bound
\[
                      \theta_L-\alpha<\pi/2-33/100.
\tag{34}
\]
The strict partner T has precisely one of the four original types.

### 5.1 Partner A or M

An actual adjacent A port has \(\beta>1/2>23/50\), by the accepted
high-radius near-corner lemma. For an actual strict shared M port,
the unchanged local chart gives
\[
 a_M=2-d\cos\beta+\tfrac12\sin\beta>R/\sqrt2.
\]
If \(\beta\le23/50\), the whole elementary comparison yields
\[
 a_M<2-\frac{187}{200}\left(1-\frac{(23/50)^2}{2}\right)
                +\frac{23}{100}
    =\frac{1393923}{1000000}<\frac75<\sqrt2,
\]
a contradiction. This is also the weaker local consequence in
`SIX_CYCLE_RADIAL_SHARED_PORT_ANGLE_BOUND.md`. Thus either partner
has \(\beta>23/50\). Its complete unique turn bound and (2) give
\[
 \theta_L-\alpha=\pi+\beta-\theta_T
                       \ge\pi/4+\beta>\pi/4+23/50.
\tag{35}
\]
But
\[
 (\pi/4+23/50)-(\pi/2-33/100)
       =79/100-\pi/4>79/100-11/14=3/700>0,
\tag{36}
\]
contradicting (34).

### 5.2 Partner O

The original O partner has its own point on the very same opposite
curve, at the same d and actual radius. Its actual return is its
nonowned adjacent vertex. The second row of the comparison table gives
\[
                      \theta_T-\beta<3\pi/4-23/50.
\]
Combining this with (34),
\[
 (\theta_L-\alpha)+(\theta_T-\beta)
       <5\pi/4-79/100<\pi.
\tag{37}
\]
Equation (2) requires this sum to equal pi. The last strict gap is
again (36), so the entire O partner is excluded.

### 5.3 Partner T with its full genuine return mean

At the actual genuine return owner, the actual turn is
\(\theta_T=\pi-\eta_T\). The third comparison row gives
\[
                     \beta+\eta_T>\pi/4+23/50.
\]
The original turn sum now requires
\[
                         \theta_L-\alpha=\beta+\eta_T,
\tag{38}
\]
contradicting (34),(36). The entire actual T mean, including t=0
when compatible with its original physical endpoint, is retained.
The O return-turn function was not substituted for T's actual turn.

These four types exhaust every strict partner. The whole low-turn
opposite-port family is therefore excluded without using a new
return-span or completion allocation split.

## 6. Exact scope retained at the final join

The actual low endpoint is precisely either reflected same-inner-side
non-owner row whose S port is its opposite vertex. The other actual
port is the adjacent vertex; no owned mean is silently made a vertex.
The low actual right-turn endpoint \(\theta_L=\pi/2\) is included
through the first comparison row and its strict uniform gamma bound.
The scalar endpoint \(t=0\) is retained for every comparison, and
actual strict-owner endpoint means retain their genuine labels.

All nine physical squares enter the global \(R>2\) premise. The
proof does not claim a lower-radius six-body core is impossible
without its three extras. The separate low adjacent and single-mean
families, and the separate both-inner-axis owner family, have their
own full original joins. This manuscript alone does not tick the
unrestricted one-radial parent.

Every scalar comparison covers a complete connected interval with
explicit endpoint signs. The only fixed arithmetic consists of the
displayed rational Taylor and polynomial reserves. No parameter
grid, computer-generated coefficient packet, numerical root, Lean
compilation or CI is used.
