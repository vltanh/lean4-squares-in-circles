# An analytic enclosure for every feasible five-corner chain

## Theorem and scope

Write $q=R^2$. Every five-corner chain of
[FIVE_CORNER_REDUCTION.md](FIVE_CORNER_REDUCTION.md) with

$$
q\le \frac{9789}{2500}
$$

satisfies

$$
\boxed{\quad R>\frac{79}{40},\qquad
0\le \tan t<\frac15.\quad}                                      \tag{1}
$$

This is a whole-domain support argument. Five choices of rational weights
give five concave functions of the tilt. Their signs follow from ten
explicit endpoint comparisons. No position is sampled, no continuous
interval cover is used, and no stationarity assumption is needed.

The coarse enclosure is deliberately wider than a root-isolating box. It
is sufficient to check the extra squares in the exact construction and
to simplify further analysis of the conditional family. It does not
assert that an arbitrary eight-square packing gives the five-corner chain.

## 1. A support inequality and its concavity test

For positive weights $(a,b,d,e,1)$ on the five chain inequalities, summing
them and collecting the coefficients of the five disk points gives

$$
B(t)\le R D(t),                                               \tag{2}
$$

where, with $s=\sin t$ and $c=\cos t$,

$$
\begin{aligned}
B(t)&=2a+3b+2d+e+2+es+c,\\
D(t)&=K+g_1(t)+g_4(t),\\
K&=\sqrt{a^2+b^2}+\sqrt{b^2+d^2}+\sqrt{e^2+1},\\
g_1(t)&=\sqrt{a^2+1-2as},\\
g_4(t)&=\sqrt{d^2+e^2-2de c}.
\end{aligned}                                                \tag{3}
$$

Indeed the five coefficient vectors, in point order, are

$$
(c,s-a),\quad (b,a),\quad(-b,d),\quad(-es,ec-d),
\quad(-c+es,-s-ec).
$$

Their norms sum to $D$. Each scalar product with a point in the radius-$R$
disk is at most $R$ times the coefficient norm, proving (2).

Fix a number $0<\rho<2$ and put

$$
E_\rho(t)=B(t)-\rho D(t).
$$

If $e\ge3/4$ and $g_1+g_4<2$ on an interval in $[0,\pi/4]$, then
$E_\rho$ is strictly concave on that interval. To see this, for

$$
g(t)=\sqrt{A^2+B^2-2AB\cos(t-t_0)}
$$

direct differentiation wherever $g>0$ gives

$$
g''+\frac g4=\frac{(A^2-B^2)^2}{4g^3}\ge0.                    \tag{4}
$$

Both variable norms in (3) have this form. The only zero that occurs in
our applications is $g_4(0)=0$ when $d=e$, in which case
$g_4(t)=2d\sin(t/2)$ on the interval and the same differential identity
holds in its interior. Continuity includes the endpoint.

The positive concave sinusoid $es+c$ has minimum at an endpoint of
$[0,\pi/4]$. As $e\ge3/4>\sqrt2-1$, that minimum is $1$. Consequently

$$
E_\rho''
\le -(es+c)+\frac{\rho}{4}(g_1+g_4)
<-1+\frac{\rho}{2}<0.                                      \tag{5}
$$

In particular, positive endpoint values imply $E_\rho>0$ throughout the
closed interval between them. By (2), this proves $R>\rho$ there.

## 2. The five weight choices

All terminating decimals in this note are exact rationals. Set

$$
\rho_+=\frac{4947}{2500}=1.9788,\qquad
\rho_-=\frac{79}{40}=1.975.
$$

Use the following weights and intervals. An interval in the $h$ column
means the tilt interval whose endpoints are the arctangents of those
numbers; $h=\tan t$ is increasing.

| Name | $(a,b,d,e,1)$ | $h$ interval | $\rho$ |
| --- | --- | --- | --- |
| A | $(0.69,0.98,1.01,0.97,1)$ | $[1/5,1/3]$ | $\rho_+$ |
| B | $(0.7,1,1,0.95,1)$ | $[1/3,2/5]$ | $\rho_+$ |
| C | $(0.8,0.95,0.8,0.75,1)$ | $[2/5,1]$ | $\rho_+$ |
| D | $(0.6,1,1.2,1.2,1)$ | $[0,1/10]$ | $\rho_-$ |
| E | $(0.65,1,1.05,1.025,1)$ | $[1/10,1/5]$ | $\rho_-$ |

Here $e\ge3/4$ in every row. The following simple bounds verify the other
concavity hypothesis:

| Name | Upper bound for $g_1$ | Upper bound for $g_4$ | Where valid |
| --- | --- | --- | --- |
| A | $1.22$ | $0.77$ | $[0,\pi/4]$ |
| B | $1.23$ | $0.76$ | $[0,\pi/4]$ |
| C | $1.29$ | $0.61$ | $[0,\pi/4]$ |
| D | $1.2$ | $0.12$ | $0\le h\le1/10$ |
| E | $1.2$ | $0.25$ | $0\le h\le1/5$ |

For the first three rows use

$$
g_1^2\le a^2+1,\qquad
g_4^2\le d^2+e^2-\sqrt2\,de
<d^2+e^2-\frac75de.
$$

The squares of the displayed upper bounds exceed these rational right-hand
sides. For row D, $g_4=2.4\sin(t/2)<1.2t\le0.12$, with the value zero
at $t=0$ included. For row E, the triangle inequality for the two vectors
whose difference defines $g_4$ gives

$$
g_4\le |d-e|+2\min(d,e)\sin(t/2)
\le0.025+1.025t<0.23<0.25.
$$

Here $t\le\arctan(1/5)<1/5$. In all five rows the sum of the two
displayed upper bounds is less than $2$. Thus (5) applies.

## 3. Explicit endpoint arithmetic

For completeness, the following tables give short rational checks of every
endpoint sign. They are fixed-number square comparisons, not a verification
program or a cover of a variable domain.

All integer entries in the tables of this section are to be divided by
$N=10^6$. If $h=\tan t$, then

$$
c=\frac1{\sqrt{1+h^2}},\qquad s=hc.
$$

The following integers $C_h$ give lower bounds $c\ge C_h/N$:

| $h$ | $0$ | $1/10$ | $1/5$ | $1/3$ | $2/5$ | $1$ |
| --- | --- | --- | --- | --- | --- | --- |
| $C_h$ | 1000000 | 995037 | 980580 | 948683 | 928476 | 707106 |

Each assertion is just
$C_h^2(1+h^2)\le N^2$, with equality when $h=0$.

Here are upper bounds for the three constant norms in $K$ and their sum:

| Name | $N\sqrt{a^2+b^2}\le$ | $N\sqrt{b^2+d^2}\le$ | $N\sqrt{e^2+1}\le$ | $NK\le K_N$ |
| --- | ---: | ---: | ---: | ---: |
| A | 1198541 | 1407303 | 1393162 | 3999006 |
| B | 1220656 | 1414214 | 1379312 | 4014182 |
| C | 1241975 | 1241975 | 1250000 | 3733950 |
| D | 1166191 | 1562050 | 1562050 | 4290291 |
| E | 1192687 | 1450000 | 1432001 | 4074688 |

Squaring each nonnegative norm bound proves it. For the two variable norms
and $B$, define integers $B_N,G_{1,N},G_{4,N},D_N$ by the next table.
They satisfy

$$
B\ge\frac{B_N}{N},\qquad
g_1\le\frac{G_{1,N}}{N},\qquad
g_4\le\frac{G_{4,N}}{N},\qquad
D\le\frac{D_N}{N},                                         \tag{6}
$$

where $D_N=K_N+G_{1,N}+G_{4,N}$.

| Name | $h$ | $B_N$ | $G_{1,N}$ | $G_{4,N}$ | $D_N$ |
| --- | --- | ---: | ---: | ---: | ---: |
| A | $1/5$ | 10480812 | 1097935 | 199127 | 5296068 |
| A | $1/3$ | 10565423 | 1019660 | 319610 | 5338276 |
| B | $1/3$ | 10599099 | 1023368 | 316232 | 5353782 |
| B | $2/5$ | 10631296 | 984913 | 372016 | 5371111 |
| C | $2/5$ | 10007018 | 1022632 | 297202 | 5053784 |
| C | $1$ | 10037435 | 713184 | 594957 | 5042091 |
| D | $0$ | 10800000 | 1166191 | 0 | 5456482 |
| D | $1/10$ | 10914441 | 1113821 | 119556 | 5523668 |
| E | $1/10$ | 10522028 | 1137166 | 106339 | 5318193 |
| E | $1/5$ | 10606598 | 1080532 | 205978 | 5361198 |

In detail, the integer checks establishing this table are

$$
\begin{aligned}
B_N&\le N(2a+3b+2d+e+2)+(eh+1)C_h,\\
G_{1,N}^2&\ge N^2(a^2+1)-2ahC_hN,\\
G_{4,N}^2&\ge N^2(d^2+e^2)-2deC_hN.
\end{aligned}                                               \tag{7}
$$

All coefficients here are the displayed rationals. Thus (7), with the
preceding constant-norm comparisons, gives a way to check (6) using only
integer multiplication and addition after clearing denominators.
For example, the first row gives

$$
E_{\rho_+}(\arctan(1/5))
\ge \frac{10480812}{10^6}
   -\frac{4947}{2500}\frac{5296068}{10^6}
=\frac{595401}{625000000}>\frac1{2000}.
$$

For every row of the table, the same substitution gives

$$
\frac{B_N-\rho D_N}{N}>\frac1{2000}.                         \tag{8}
$$

This last assertion is ten linear rational comparisons, using $\rho_+$
for A--C and $\rho_-$ for D--E. Equations (5) and (8) prove $E_\rho>0$
throughout each of the five indicated intervals.

## 4. Completion of the enclosure proof

The three intervals A--C cover $1/5\le\tan t\le1$ and imply
$R>\rho_+$ there. But

$$
\rho_+^2-\frac{9789}{2500}=\frac{309}{6250000}>0.
$$

Thus a chain with the squared-radius ceiling in the theorem has
$\tan t<1/5$. The intervals D--E cover the remaining tilts and imply
$R>\rho_-=79/40$. This proves both parts of (1).

In particular these bounds apply to every minimizer of the five-corner
family. Its least squared radius is strictly below $9789/2500$, because
the five distinguished points of
[ANALYTIC_RATIONAL_CONSTRUCTION.md](ANALYTIC_RATIONAL_CONSTRUCTION.md)
all have strictly smaller norm and satisfy every projected inequality.

