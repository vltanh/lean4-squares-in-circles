# A coupled three-square angle bound closes two whole cycle signatures

**Status:** complete geometric argument with a fully explicit finite rational
arithmetic certificate, checked in this session by two implementations.
No independent agent review or Lean verification is claimed. Both whole-case
consequences below retain every contact ownership and continuous parameter.

Let three interior-disjoint unit squares lie in the origin-centered disk
of radius `79/40<=R<=3/sqrt(2)`, each with a vertex on the containing circle.
List their center rays on an angular interval, with the middle ray between
the other two. Let the two positive intervening angles be delta_1,delta_2.

**Theorem.**

```text
delta_1+delta_2 > Gamma := pi/2-atan(1/45).           (1)
```

In particular this exceeds the separate pair bounds. Combined with the
D-path cap estimate, it excludes the whole signatures `LLLLDLD` and
`LLLDLLD`, closing two existing entries of the frozen master ledger.

The proof is a geometric reduction followed by a finite table of rational
inequalities. Every leaf inequality is supplied in
[loaded_joint_angle_leaves.tsv](loaded_joint_angle_leaves.tsv); the 332-row
summary appears below. No numerical optimizer or floating-point output is
a premise. The two exact verifiers are
[check_loaded_joint_angle_bound.py](check_loaded_joint_angle_bound.py) and
[independent_loaded_joint_angle_check.py](independent_loaded_joint_angle_check.py).

## 1. Radial inflation reduces the radius variable to its upper endpoint

Fix one square's frame and center ray. If its center radius is r, its
farthest squared vertex norm is `r^2+w*r+1/2`, where 1<=w<=sqrt(2) is
constant during radial motion. The radius r(R) of a circle-loaded square
therefore satisfies

```text
r^2+w*r+1/2=R^2,
r'=R/sqrt(R^2-1/2+w^2/4).
```

Throughout the radius window, the existing universal loaded-center bounds
and this derivative give

```text
5/4<r<25/16,       1<=r'<9/8,
16/25<g:=r'/r<9/10.                                (2)
```

For the derivative upper bound, `r'^2<=R^2/(R^2-1/4)<81/64` follows
already from `R^2>81/68`, which holds in the stated window.

For an original separating unit axis n of two squares i,j, orient it so
that `d=n dot(c_j-c_i)>=h_i+h_j>=1`. The directional halfwidths h_i,h_j
remain fixed. Using the smaller of g_i,g_j as a common coefficient leaves
only one correction term, and hence, whenever d>=1,

```text
d' >= (16/25)*d-(9/10-16/25)*(25/16)
    >=187/800>0.                                   (3)
```

If a separating gap first returned to its original threshold after an
increase, its derivative at that return would be nonpositive, contradicting
(3). Starting at equality is harmless since (3) initially increases it.
Thus every original pair separator remains valid as R increases.

Inflate the three squares independently along their rays to R=3/sqrt(2).
Their frames and center angles are unchanged, and they remain pairwise
interior-disjoint. It suffices to prove (1) at this upper radius.

## 2. Radius and curvature bounds used in the finite certificate

At the upper radius, a frame making unsigned angle theta with its center
ray has

```text
w=cos(theta)+sin(theta),
r(theta)=(sqrt(w^2+16)-w)/2,
sqrt(2)<=r(theta)<25/16.                            (4)
```

Primes in this section denote angle derivatives. On each smooth signed-frame
branch write d_0=w', L=2r+w. Differentiation gives

```text
r'=-r*d_0/L,       |r'|<1/2,
r''=r*w/L+2r*d_0^2*(L-r)/L^3>0.
```

There is also the uniform strict bound r''<1/2. Indeed

```text
r''=(1/2)*(w-(w^4+32w^2-32)/(w^2+16)^(3/2)).
```

The numerator w^4+32w^2-32 is positive for w>=1. Squaring the positive
quantities in the desired comparison with w-1 gives, with z=w-1,

```text
(w^4+32w^2-32)^2-(w-1)^2*(w^2+16)^3
 =2z^7+29z^6+228z^5+919z^4+3442z^3-213z^2+136z+1>0.
```

Here 0<=z<=sqrt(2)-1<1/2. All terms are nonnegative except -213z^2,
and `136z-213z^2=z*(136-213z)>=0`; the constant is positive. Therefore

```text
0<r''<1/2.                                         (5)
```

These formulas apply also to the even frame extension r(|theta|), on
intervals not crossing zero.

Define the increasing cap function, now as an angle parameter,

```text
B(gamma)=r(gamma)*sin(gamma)-1/2,       0<=gamma<=pi/2.
```

Its derivative is positive:

```text
B'=r*(2r*cos(gamma)+1)/(2r+sin(gamma)+cos(gamma))>0.
```

Equations (4)--(5) also give

```text
|B''| <= |r''|+2|r'|+r <49/16<4.                   (6)
```

The extended cap theorem from
[LOADED_PAIR_ANGLE_BOUND.md](LOADED_PAIR_ANGLE_BOUND.md), Section 1,
is used below for every cap offset greater than -1/2.

## 3. A necessary one-sided separator inequality covers all offset signs

Put the middle center on the positive horizontal axis, with signed frame
angle alpha. Consider another loaded center at angle -delta and suppose

```text
0<delta<=Delta<=2atan(1/2).
```

The existing pair bound gives
`delta>=delta_*=2atan(1/(sqrt(14)-1))>acos(7/9)`.
The vector from this neighboring center toward the middle one is

```text
D=(r_0-r_1*cos(delta),r_1*sin(delta)).
```

Its first coordinate satisfies 0<D_x<1: the lower estimate follows from
`sqrt(2)-(25/16)*(7/9)>0`, and the upper from
`25/16-(3/5)*sqrt(2)<1`, since cos(delta)>=3/5.
Its second coordinate is positive. A separating unit normal n pointing
toward the middle square satisfies n dot D>=1. Consequently n_y>0;
otherwise n dot D<=D_x<1. Write

```text
n=(sin(beta),cos(beta)),       -pi/2<beta<pi/2.
```

The middle square's least projection is

```text
A(alpha,beta)=r(|alpha|)*sin(beta)
 -(abs(sin(beta+alpha))+abs(cos(beta+alpha)))/2.       (7)
```

The neighbor's greatest projection is at least -25/16+1/2=-17/16, so
A>-17/16. If beta<=-pi/6, (4) and the halfwidth bound would give
`A<=-sqrt(2)/2-1/2<-17/16`, a contradiction. Thus beta>-pi/6. In half-angle
coordinates its full feasible range is contained in

```text
t=tan(beta/2) in [-2/7,1].                           (8)
```

For example `2atan(2/7)>pi/6` because its sine is 28/53>1/2.

We claim that a pair with delta<=Delta must have some beta in (8) with

```text
F(alpha,beta;Delta)>=0,

F = A(alpha,beta)+B(Delta-beta),                 beta<=Delta;
F = A(alpha,beta)-sqrt(2)*sin(beta-Delta)-1/2,    beta>=Delta. (9)
```

Here is the full offset coverage.

* If beta<=delta, the neighbor has nonpositive projection on n. It lies
  in the cap along -n beginning at -A. If A<1/2, the extended cap theorem
  applies and gives `A+B(delta-beta)>=0`. If A>=1/2 this inequality holds
  automatically since B>=-1/2. Increasing delta to Delta preserves it
  by monotonicity of B.
* If delta<=beta<=Delta, the neighbor has nonnegative projection on n.
  Its halfwidth is at least 1/2, so A>=1/2 and the first line of (9)
  again holds automatically.
* If beta>=Delta, the neighbor's center radius is at least sqrt(2).
  Therefore `A>=sqrt(2)*sin(beta-delta)+1/2`, implying the second line
  of (9) since 0<=beta-Delta<=beta-delta<pi/2.

No small-separator-offset assumption remains. In the first line of (9),
0<=Delta-beta<pi/2 throughout the certificate domain: its largest allowed
half-angle tangent is `(1/2+2/7)/(1-(1/2)*(2/7))=11/12<1`.

## 4. Finite frame reduction, including every side-normal kink

Choose the middle frame modulo pi/2 and reflect the triple if needed so
that 0<=alpha<=pi/4. Its half-angle tangent is in [0,sqrt(2)-1]. Cover it
by the 332 closed rational intervals

```text
[i/800,(i+1)/800],       i=0,...,331.                (10)
```

Their upper endpoint is 83/200>sqrt(2)-1, as `(283/200)^2>2`.
For the lower neighboring ray use the positive frame interval (side B).
For the upper ray reflect that pair vertically, using the corresponding
negative frame interval (side G).

For fixed beta, A is strictly convex in alpha on every smooth branch:

```text
partial_alpha^2 A=r''(|alpha|)*sin(beta)+h>0,
h=(abs(sin(beta+alpha))+abs(cos(beta+alpha)))/2>=1/2.
```

This follows from (5), even for negative beta. Thus its maximum over one
signed frame interval occurs at an endpoint or a side-normal kink.
The only possible internal kinks are

```text
alpha=-beta,       alpha=pi/2-beta.
```

There is no interior zero-frame kink because each signed frame interval
is on one side of zero. The padded ranges cause no extra angular kink:
`2atan(83/200)+2atan(2/7)=2atan(981/1234)<pi/2`, so
`-pi/2<beta+alpha<pi` throughout.

At either side-normal kink the halfwidth is 1/2 and the radius is r(|beta|),
using the quarter-turn symmetry. Its contribution to (7) is therefore

```text
A_kink(beta)=r(|beta|)*sin(beta)-1/2.
```

For beta>=0 this is B(beta); for beta<=0 it is -B(-beta)-1.
The certificate checks both frame endpoints on the full beta domain and
each kink on exactly the beta subinterval where it lies inside that
frame interval. Endpoint kinks are already included in the endpoint checks.

## 5. Every one-dimensional table leaf has a rigorous curvature bound

For a fixed frame endpoint, on a smooth beta branch `A''=-A`, and
`|A|<25/16+3/4<3`. At a moving side-normal kink, (6) gives
`|A_kink''|<4`. Combined with (6), every smooth version of F in (9)
satisfies

```text
F''>-8.                                             (11)
```

For the second line of (9), the additional sine contributes at most
sqrt(2)<3/2 in absolute second derivative, which also fits this bound.
Split the beta domain at beta=0, beta=Delta, and all frame-side kinks
before applying (11).

If f''>=-8 on an interval [b_0,b_1], convexity of f(b)+4b^2 gives

```text
f(b)<=max(f(b_0),f(b_1))+(b_1-b_0)^2.
```

In half-angle coordinates t, `b=2atan(t)` has derivative at most two.
Hence a closed rational t interval [l,u] has the rigorous upper bound

```text
F <= max(F(2atan l),F(2atan u))+4(u-l)^2.            (12)
```

Each leaf of the supplied TSV certificate states that the right side,
with rational upper enclosures for both endpoint values, is at most
`-margin/10^9<0`. This proves F<0 on the entire leaf, rather than only
at sampled points.

## 6. Exact arithmetic, leaf coverage, and the fixed angle table

For each frame row, the summary supplies two positive rational numbers
u_G,u_B<=1/2. They are half-angle tangents for thresholds

```text
Delta_G=2atan(u_G),       Delta_B=2atan(u_B).
```

The leaf certificate covers all endpoint and kink tasks from Section 4.
Each smooth task interval is specified in half-angle coordinates, split
at the explicit rational knots above, and then bisected by midpoint.
A binary path in the TSV identifies the exact closed subinterval. The
primary verifier requires every internal node to have both children,
rejecting missing intervals and prefix-overlapping paths. Closed children
retain every shared boundary. There are 28000 leaf inequalities in total.

All endpoint trigonometric coordinates are rational:
`sin(2atan t)=2t/(1+t^2)` and `cos(2atan t)=(1-t^2)/(1+t^2)`.
The primary verifier brackets sqrt(v) by k/10^10 and (k+1)/10^10, with
`k^2<=10^20*v<(k+1)^2`. It uses the correct radius bound for the sign
of sin(beta), the exact rational support halfwidth, and a lower sqrt(2)
bound in the negative sine term in (9). Thus every endpoint value used
in (12) is an upper bound.

The independent verifier instead brackets r directly by dyadic rationals,
bisecting the integer inequality for `r^2+w*r<=4` at denominator 2^48.
It reconstructs every leaf by its path, checks its claimed negative upper
bound, and checks coverage separately by prefix-free paths and exact
Kraft sums. Both implementations verify all 28000 inequalities and all
332 coupled sums. The smallest claimed leaf margin is 323/10^9>0.

Finally every frame row verifies the exact rational inequality

```text
T_G+T_B > 45*(1-T_G*T_B),
T_G=2u_G/(1-u_G^2),       T_B=2u_B/(1-u_B^2).         (13)
```

Because both Delta values are in (0,pi/2), (13) says
`cot(Delta_G+Delta_B)<1/45`, equivalently
`Delta_G+Delta_B>Gamma`. It includes sums at least pi/2 without a tangent
branch error.

The endpoint/kink certificates exclude a neighboring minor angle at most
its corresponding Delta. Therefore both actual adjacent gaps exceed their
row thresholds, proving (1). If a lifted gap is at least pi the theorem
is immediate; otherwise the pair minor-angle argument applies whenever
needed. No stress or contact ownership is used in the triple theorem.

The full leaf table and the metadata containing all rational thresholds
are committed separately. The following summary reproduces every frame
row; each count and minimum margin is checked against the complete table.

| Frame row | Good half-angle tangent | Bad half-angle tangent | Leaves | Minimum margin / 10^9 |
| ---: | --- | --- | ---: | ---: |
| 0 | 8193/20000 | 8201/20000 | 105 | 55972 |
| 1 | 40923/100000 | 8213/20000 | 107 | 35623 |
| 2 | 40879/100000 | 10281/25000 | 109 | 40660 |
| 3 | 8167/20000 | 41183/100000 | 108 | 25802 |
| 4 | 40789/100000 | 41241/100000 | 108 | 10194 |
| 5 | 40741/100000 | 41299/100000 | 109 | 19817 |
| 6 | 40693/100000 | 41357/100000 | 109 | 29259 |
| 7 | 40643/100000 | 20707/50000 | 108 | 21155 |
| 8 | 40591/100000 | 41471/100000 | 106 | 10361 |
| 9 | 20269/50000 | 41527/100000 | 107 | 42792 |
| 10 | 40483/100000 | 41583/100000 | 105 | 564 |
| 11 | 40427/100000 | 41639/100000 | 105 | 57835 |
| 12 | 40369/100000 | 8339/20000 | 105 | 5714 |
| 13 | 40309/100000 | 167/400 | 105 | 9801 |
| 14 | 5031/12500 | 10451/25000 | 105 | 1016 |
| 15 | 5023/12500 | 41859/100000 | 105 | 33946 |
| 16 | 40119/100000 | 5239/12500 | 104 | 33192 |
| 17 | 10013/25000 | 20983/50000 | 105 | 48853 |
| 18 | 7997/20000 | 42019/100000 | 102 | 2050 |
| 19 | 499/1250 | 5259/12500 | 101 | 8203 |
| 20 | 7971/20000 | 10531/25000 | 99 | 16920 |
| 21 | 39791/100000 | 1318/3125 | 97 | 21475 |
| 22 | 39727/100000 | 10557/25000 | 95 | 31024 |
| 23 | 7933/20000 | 42279/100000 | 95 | 9579 |
| 24 | 39603/100000 | 4233/10000 | 96 | 45563 |
| 25 | 19771/50000 | 2119/5000 | 96 | 50615 |
| 26 | 19741/50000 | 4243/10000 | 96 | 50904 |
| 27 | 19711/50000 | 531/1250 | 96 | 64836 |
| 28 | 39363/100000 | 42529/100000 | 95 | 7451 |
| 29 | 7861/20000 | 21289/50000 | 94 | 27752 |
| 30 | 2453/6250 | 21313/50000 | 94 | 63056 |
| 31 | 39191/100000 | 21337/50000 | 94 | 78853 |
| 32 | 7827/20000 | 21361/50000 | 94 | 20450 |
| 33 | 977/2500 | 42769/100000 | 94 | 18826 |
| 34 | 1561/4000 | 1338/3125 | 93 | 101122 |
| 35 | 38971/100000 | 21431/50000 | 91 | 6817 |
| 36 | 19459/50000 | 10727/25000 | 91 | 46680 |
| 37 | 19433/50000 | 21477/50000 | 91 | 9460 |
| 38 | 19407/50000 | 42999/100000 | 92 | 128629 |
| 39 | 38763/100000 | 10761/25000 | 90 | 9122 |
| 40 | 4839/12500 | 2693/6250 | 90 | 42206 |
| 41 | 19331/50000 | 10783/25000 | 90 | 70122 |
| 42 | 38613/100000 | 5397/12500 | 90 | 66591 |
| 43 | 7713/20000 | 43219/100000 | 90 | 39822 |
| 44 | 38517/100000 | 43261/100000 | 89 | 27906 |
| 45 | 3847/10000 | 5413/12500 | 90 | 172117 |
| 46 | 38423/100000 | 21673/50000 | 90 | 187540 |
| 47 | 19189/50000 | 43387/100000 | 89 | 116867 |
| 48 | 9583/25000 | 10857/25000 | 88 | 4717 |
| 49 | 2393/6250 | 43469/100000 | 88 | 85530 |
| 50 | 9561/25000 | 43509/100000 | 88 | 13878 |
| 51 | 38201/100000 | 43549/100000 | 87 | 7612 |
| 52 | 19079/50000 | 43589/100000 | 86 | 53335 |
| 53 | 9529/25000 | 10907/25000 | 86 | 83500 |
| 54 | 19037/50000 | 21833/50000 | 86 | 64718 |
| 55 | 38033/100000 | 5463/12500 | 87 | 40120 |
| 56 | 37993/100000 | 21871/50000 | 87 | 9700 |
| 57 | 18977/50000 | 2189/5000 | 88 | 113491 |
| 58 | 7583/20000 | 5477/12500 | 87 | 58561 |
| 59 | 9469/25000 | 43853/100000 | 86 | 14719 |
| 60 | 18919/50000 | 43889/100000 | 86 | 54589 |
| 61 | 37801/100000 | 1757/4000 | 86 | 167291 |
| 62 | 9441/25000 | 1099/2500 | 85 | 16040 |
| 63 | 1179/3125 | 8799/20000 | 85 | 39808 |
| 64 | 37693/100000 | 44029/100000 | 85 | 78292 |
| 65 | 18829/50000 | 1377/3125 | 85 | 87516 |
| 66 | 37623/100000 | 44097/100000 | 85 | 68789 |
| 67 | 37589/100000 | 4413/10000 | 85 | 44053 |
| 68 | 9389/25000 | 44163/100000 | 85 | 13304 |
| 69 | 37523/100000 | 11049/25000 | 86 | 149257 |
| 70 | 37491/100000 | 44227/100000 | 86 | 133491 |
| 71 | 1873/5000 | 44259/100000 | 86 | 108336 |
| 72 | 37429/100000 | 4429/10000 | 86 | 94182 |
| 73 | 18699/50000 | 44321/100000 | 85 | 1713 |
| 74 | 4671/12500 | 44351/100000 | 85 | 7269 |
| 75 | 37339/100000 | 44381/100000 | 87 | 3170 |
| 76 | 3731/10000 | 44411/100000 | 85 | 10029 |
| 77 | 37281/100000 | 1111/2500 | 84 | 27842 |
| 78 | 18627/50000 | 11117/25000 | 84 | 11860 |
| 79 | 18613/50000 | 2781/6250 | 85 | 11829 |
| 80 | 93/250 | 11131/25000 | 86 | 21643 |
| 81 | 37173/100000 | 5569/12500 | 86 | 323 |
| 82 | 9287/25000 | 44579/100000 | 87 | 29517 |
| 83 | 18561/50000 | 8921/20000 | 86 | 30544 |
| 84 | 18549/50000 | 44631/100000 | 85 | 3859 |
| 85 | 37073/100000 | 44657/100000 | 85 | 58351 |
| 86 | 741/2000 | 22341/50000 | 85 | 46957 |
| 87 | 18513/50000 | 44707/100000 | 83 | 6506 |
| 88 | 9251/25000 | 11183/25000 | 83 | 30276 |
| 89 | 36981/100000 | 11189/25000 | 83 | 60907 |
| 90 | 231/625 | 2239/5000 | 83 | 63402 |
| 91 | 36939/100000 | 44803/100000 | 83 | 61574 |
| 92 | 18459/50000 | 22413/50000 | 83 | 70036 |
| 93 | 18449/50000 | 2803/6250 | 83 | 59027 |
| 94 | 18439/50000 | 44871/100000 | 83 | 12516 |
| 95 | 18429/50000 | 11223/25000 | 83 | 2286 |
| 96 | 921/2500 | 44913/100000 | 84 | 77709 |
| 97 | 36821/100000 | 22467/50000 | 84 | 94258 |
| 98 | 36803/100000 | 8991/20000 | 84 | 99350 |
| 99 | 18393/50000 | 1799/4000 | 84 | 66832 |
| 100 | 36769/100000 | 22497/50000 | 83 | 3483 |
| 101 | 2297/6250 | 22507/50000 | 83 | 11776 |
| 102 | 1148/3125 | 45033/100000 | 85 | 32485 |
| 103 | 36721/100000 | 45051/100000 | 87 | 73721 |
| 104 | 18353/50000 | 45069/100000 | 86 | 5361 |
| 105 | 36691/100000 | 45087/100000 | 86 | 93910 |
| 106 | 36677/100000 | 2819/6250 | 85 | 88447 |
| 107 | 36663/100000 | 45121/100000 | 85 | 56086 |
| 108 | 733/2000 | 45137/100000 | 86 | 39039 |
| 109 | 36637/100000 | 45153/100000 | 86 | 15862 |
| 110 | 2289/6250 | 45169/100000 | 87 | 127318 |
| 111 | 9153/25000 | 1412/3125 | 87 | 128831 |
| 112 | 36601/100000 | 45199/100000 | 87 | 117804 |
| 113 | 3659/10000 | 22607/50000 | 87 | 116223 |
| 114 | 36579/100000 | 11307/25000 | 87 | 124080 |
| 115 | 36569/100000 | 22621/50000 | 86 | 5217 |
| 116 | 36559/100000 | 9051/20000 | 86 | 38037 |
| 117 | 36549/100000 | 11317/25000 | 86 | 64898 |
| 118 | 1827/5000 | 283/625 | 86 | 107244 |
| 119 | 9133/25000 | 45293/100000 | 86 | 122210 |
| 120 | 9131/25000 | 5663/12500 | 86 | 123301 |
| 121 | 9129/25000 | 11329/25000 | 86 | 85672 |
| 122 | 36509/100000 | 45327/100000 | 86 | 57640 |
| 123 | 18251/50000 | 45337/100000 | 86 | 45306 |
| 124 | 7299/20000 | 11337/25000 | 86 | 5232 |
| 125 | 36489/100000 | 22679/50000 | 86 | 5124 |
| 126 | 36483/100000 | 45367/100000 | 86 | 20680 |
| 127 | 18239/50000 | 1418/3125 | 86 | 22627 |
| 128 | 36473/100000 | 9077/20000 | 86 | 33484 |
| 129 | 9117/25000 | 45393/100000 | 85 | 6285 |
| 130 | 2279/6250 | 45401/100000 | 85 | 29834 |
| 131 | 36461/100000 | 45409/100000 | 85 | 47535 |
| 132 | 36457/100000 | 5677/12500 | 85 | 51851 |
| 133 | 18227/50000 | 45423/100000 | 85 | 39713 |
| 134 | 9113/25000 | 4543/10000 | 86 | 19054 |
| 135 | 36449/100000 | 11359/25000 | 85 | 19772 |
| 136 | 1139/3125 | 22721/50000 | 84 | 12010 |
| 137 | 18223/50000 | 45447/100000 | 83 | 20357 |
| 138 | 7289/20000 | 11363/25000 | 83 | 22932 |
| 139 | 9111/25000 | 45457/100000 | 83 | 19742 |
| 140 | 9111/25000 | 45461/100000 | 83 | 15850 |
| 141 | 9111/25000 | 9093/20000 | 84 | 40034 |
| 142 | 9111/25000 | 45469/100000 | 84 | 23920 |
| 143 | 7289/20000 | 1421/3125 | 84 | 7813 |
| 144 | 7289/20000 | 1819/4000 | 86 | 71649 |
| 145 | 36447/100000 | 45477/100000 | 85 | 27632 |
| 146 | 1139/3125 | 1137/2500 | 85 | 34127 |
| 147 | 729/2000 | 22741/50000 | 85 | 57004 |
| 148 | 9113/25000 | 45483/100000 | 85 | 96311 |
| 149 | 7291/20000 | 11371/25000 | 85 | 130035 |
| 150 | 18229/50000 | 9097/20000 | 85 | 146386 |
| 151 | 36461/100000 | 9097/20000 | 85 | 146803 |
| 152 | 7293/20000 | 9097/20000 | 85 | 112622 |
| 153 | 36469/100000 | 9097/20000 | 85 | 72867 |
| 154 | 36473/100000 | 11371/25000 | 85 | 49858 |
| 155 | 18239/50000 | 45483/100000 | 85 | 21326 |
| 156 | 36483/100000 | 45481/100000 | 85 | 9623 |
| 157 | 4561/12500 | 45479/100000 | 86 | 54304 |
| 158 | 18247/50000 | 45477/100000 | 84 | 11149 |
| 159 | 73/200 | 22737/50000 | 84 | 5819 |
| 160 | 36507/100000 | 45471/100000 | 85 | 28510 |
| 161 | 36513/100000 | 11367/25000 | 85 | 20236 |
| 162 | 913/2500 | 5683/12500 | 85 | 26209 |
| 163 | 2283/6250 | 2273/5000 | 85 | 26829 |
| 164 | 4567/12500 | 2841/6250 | 85 | 22107 |
| 165 | 1142/3125 | 11363/25000 | 85 | 12053 |
| 166 | 4569/12500 | 45447/100000 | 85 | 19166 |
| 167 | 36561/100000 | 22721/50000 | 83 | 20417 |
| 168 | 3657/10000 | 11359/25000 | 84 | 23751 |
| 169 | 36579/100000 | 4543/10000 | 84 | 25377 |
| 170 | 36589/100000 | 2839/6250 | 85 | 10807 |
| 171 | 36599/100000 | 45417/100000 | 85 | 3763 |
| 172 | 36609/100000 | 45411/100000 | 85 | 4230 |
| 173 | 1831/5000 | 45403/100000 | 86 | 34288 |
| 174 | 36631/100000 | 11349/25000 | 86 | 6055 |
| 175 | 18321/50000 | 11347/25000 | 86 | 5804 |
| 176 | 18327/50000 | 2269/5000 | 86 | 23658 |
| 177 | 18333/50000 | 11343/25000 | 84 | 20651 |
| 178 | 18339/50000 | 45363/100000 | 85 | 66935 |
| 179 | 3669/10000 | 22677/50000 | 85 | 43459 |
| 180 | 36703/100000 | 9069/20000 | 86 | 112920 |
| 181 | 9179/25000 | 9067/20000 | 86 | 151216 |
| 182 | 3673/10000 | 1813/4000 | 86 | 167657 |
| 183 | 36743/100000 | 9063/20000 | 86 | 167712 |
| 184 | 36757/100000 | 9061/20000 | 86 | 162856 |
| 185 | 9193/25000 | 22647/50000 | 86 | 172526 |
| 186 | 18393/50000 | 45283/100000 | 86 | 142369 |
| 187 | 36801/100000 | 45271/100000 | 84 | 2576 |
| 188 | 2301/6250 | 2263/5000 | 83 | 33715 |
| 189 | 1151/3125 | 1414/3125 | 83 | 47270 |
| 190 | 2303/6250 | 11309/25000 | 83 | 42667 |
| 191 | 1152/3125 | 45223/100000 | 83 | 34635 |
| 192 | 461/1250 | 4521/10000 | 81 | 15311 |
| 193 | 36897/100000 | 45197/100000 | 80 | 4551 |
| 194 | 18457/50000 | 1412/3125 | 81 | 42503 |
| 195 | 36931/100000 | 4517/10000 | 81 | 72198 |
| 196 | 9237/25000 | 11289/25000 | 81 | 97299 |
| 197 | 18483/50000 | 22571/50000 | 80 | 28334 |
| 198 | 4623/12500 | 45127/100000 | 80 | 140146 |
| 199 | 18501/50000 | 45113/100000 | 80 | 168316 |
| 200 | 37021/100000 | 22549/50000 | 79 | 78337 |
| 201 | 463/1250 | 22541/50000 | 79 | 194894 |
| 202 | 37059/100000 | 45067/100000 | 79 | 209834 |
| 203 | 18539/50000 | 45051/100000 | 79 | 118942 |
| 204 | 18549/50000 | 9007/20000 | 79 | 23710 |
| 205 | 18559/50000 | 22509/50000 | 80 | 145881 |
| 206 | 18569/50000 | 22501/50000 | 80 | 106433 |
| 207 | 37159/100000 | 8997/20000 | 80 | 85987 |
| 208 | 37179/100000 | 5621/12500 | 80 | 61260 |
| 209 | 93/250 | 899/2000 | 78 | 14946 |
| 210 | 18611/50000 | 11233/25000 | 78 | 20912 |
| 211 | 37243/100000 | 22457/50000 | 78 | 15975 |
| 212 | 7453/20000 | 1403/3125 | 78 | 13610 |
| 213 | 37287/100000 | 22439/50000 | 80 | 40064 |
| 214 | 37309/100000 | 44859/100000 | 80 | 61448 |
| 215 | 9333/25000 | 1121/2500 | 80 | 64017 |
| 216 | 18677/50000 | 44821/100000 | 81 | 97777 |
| 217 | 18689/50000 | 44801/100000 | 82 | 87586 |
| 218 | 37401/100000 | 22391/50000 | 82 | 108557 |
| 219 | 2339/6250 | 22381/50000 | 82 | 135630 |
| 220 | 4681/12500 | 44741/100000 | 82 | 143666 |
| 221 | 1171/3125 | 44721/100000 | 82 | 157734 |
| 222 | 4687/12500 | 447/1000 | 82 | 172846 |
| 223 | 37521/100000 | 44679/100000 | 82 | 157301 |
| 224 | 18773/50000 | 22329/50000 | 82 | 147761 |
| 225 | 37571/100000 | 44637/100000 | 82 | 117973 |
| 226 | 9399/25000 | 8923/20000 | 80 | 16457 |
| 227 | 37621/100000 | 44593/100000 | 80 | 32969 |
| 228 | 37647/100000 | 44571/100000 | 79 | 45703 |
| 229 | 37673/100000 | 44549/100000 | 76 | 2061 |
| 230 | 37699/100000 | 22263/50000 | 76 | 42195 |
| 231 | 18863/50000 | 44503/100000 | 76 | 34980 |
| 232 | 4719/12500 | 278/625 | 76 | 24124 |
| 233 | 37779/100000 | 44457/100000 | 76 | 9644 |
| 234 | 18903/50000 | 44433/100000 | 75 | 15466 |
| 235 | 18917/50000 | 4441/10000 | 77 | 98530 |
| 236 | 37861/100000 | 22193/50000 | 77 | 115546 |
| 237 | 37889/100000 | 22181/50000 | 77 | 106198 |
| 238 | 37917/100000 | 44337/100000 | 75 | 3414 |
| 239 | 18973/50000 | 44313/100000 | 77 | 79065 |
| 240 | 18987/50000 | 1384/3125 | 75 | 445 |
| 241 | 38003/100000 | 44263/100000 | 74 | 1441 |
| 242 | 2377/6250 | 22119/50000 | 74 | 7832 |
| 243 | 38061/100000 | 11053/25000 | 74 | 30569 |
| 244 | 3809/10000 | 44187/100000 | 75 | 25837 |
| 245 | 953/2500 | 44161/100000 | 75 | 41924 |
| 246 | 763/2000 | 8827/20000 | 75 | 45109 |
| 247 | 1909/5000 | 44109/100000 | 75 | 40383 |
| 248 | 3821/10000 | 22041/50000 | 75 | 41086 |
| 249 | 239/625 | 8811/20000 | 75 | 47202 |
| 250 | 38271/100000 | 44029/100000 | 75 | 33101 |
| 251 | 19151/50000 | 44001/100000 | 75 | 24345 |
| 252 | 38333/100000 | 21987/50000 | 77 | 20917 |
| 253 | 9591/25000 | 43947/100000 | 77 | 2243 |
| 254 | 9599/25000 | 43919/100000 | 78 | 4303 |
| 255 | 38427/100000 | 43891/100000 | 78 | 16748 |
| 256 | 38459/100000 | 43863/100000 | 78 | 8741 |
| 257 | 9623/25000 | 8767/20000 | 79 | 23212 |
| 258 | 9631/25000 | 43807/100000 | 78 | 15090 |
| 259 | 9639/25000 | 21889/50000 | 78 | 28485 |
| 260 | 38589/100000 | 43749/100000 | 77 | 38991 |
| 261 | 19311/50000 | 1093/2500 | 77 | 46623 |
| 262 | 7731/20000 | 43691/100000 | 79 | 51395 |
| 263 | 38689/100000 | 21831/50000 | 79 | 53324 |
| 264 | 19361/50000 | 2727/6250 | 80 | 77021 |
| 265 | 9689/25000 | 21801/50000 | 80 | 97955 |
| 266 | 3879/10000 | 43573/100000 | 79 | 17515 |
| 267 | 4853/12500 | 43543/100000 | 79 | 46479 |
| 268 | 19429/50000 | 5439/12500 | 79 | 80067 |
| 269 | 38893/100000 | 21741/50000 | 79 | 83439 |
| 270 | 38927/100000 | 43451/100000 | 78 | 5129 |
| 271 | 19481/50000 | 43421/100000 | 78 | 56722 |
| 272 | 38997/100000 | 4339/10000 | 78 | 51851 |
| 273 | 39033/100000 | 21679/50000 | 78 | 69200 |
| 274 | 9767/25000 | 43327/100000 | 78 | 59288 |
| 275 | 1222/3125 | 1353/3125 | 78 | 46865 |
| 276 | 1957/5000 | 1352/3125 | 78 | 56787 |
| 277 | 4897/12500 | 1351/3125 | 78 | 64282 |
| 278 | 9803/25000 | 54/125 | 78 | 69364 |
| 279 | 2453/6250 | 1349/3125 | 78 | 72049 |
| 280 | 7857/20000 | 1348/3125 | 77 | 26770 |
| 281 | 19661/50000 | 1347/3125 | 79 | 70286 |
| 282 | 39359/100000 | 43071/100000 | 79 | 90869 |
| 283 | 9849/25000 | 21519/50000 | 79 | 88170 |
| 284 | 39433/100000 | 21503/50000 | 80 | 100145 |
| 285 | 39471/100000 | 42973/100000 | 80 | 113895 |
| 286 | 9877/25000 | 42939/100000 | 80 | 150511 |
| 287 | 19773/50000 | 21453/50000 | 80 | 133348 |
| 288 | 1237/3125 | 5359/12500 | 79 | 88745 |
| 289 | 19811/50000 | 42839/100000 | 79 | 107719 |
| 290 | 39661/100000 | 8561/20000 | 79 | 104314 |
| 291 | 39699/100000 | 42771/100000 | 79 | 98854 |
| 292 | 19869/50000 | 42737/100000 | 79 | 91354 |
| 293 | 39777/100000 | 42703/100000 | 79 | 81831 |
| 294 | 4977/12500 | 10667/25000 | 79 | 95531 |
| 295 | 7971/20000 | 21317/50000 | 79 | 19761 |
| 296 | 19947/50000 | 42599/100000 | 78 | 5064 |
| 297 | 19967/50000 | 10641/25000 | 77 | 20983 |
| 298 | 19987/50000 | 4253/10000 | 79 | 61494 |
| 299 | 20007/50000 | 21247/50000 | 79 | 104939 |
| 300 | 20027/50000 | 42459/100000 | 80 | 5560 |
| 301 | 20047/50000 | 5303/12500 | 81 | 112550 |
| 302 | 20067/50000 | 10597/25000 | 81 | 136584 |
| 303 | 1607/4000 | 42353/100000 | 80 | 133370 |
| 304 | 5027/12500 | 42317/100000 | 78 | 133985 |
| 305 | 1258/3125 | 42281/100000 | 78 | 172621 |
| 306 | 40297/100000 | 8449/20000 | 78 | 179514 |
| 307 | 40339/100000 | 42209/100000 | 77 | 12215 |
| 308 | 2019/5000 | 42173/100000 | 77 | 89942 |
| 309 | 20211/50000 | 42137/100000 | 78 | 127467 |
| 310 | 40463/100000 | 421/1000 | 78 | 132463 |
| 311 | 8101/20000 | 42063/100000 | 78 | 135928 |
| 312 | 40547/100000 | 42027/100000 | 78 | 112253 |
| 313 | 40589/100000 | 4199/10000 | 78 | 112674 |
| 314 | 40631/100000 | 41953/100000 | 77 | 70921 |
| 315 | 40673/100000 | 10479/25000 | 77 | 71349 |
| 316 | 20357/50000 | 20939/50000 | 79 | 130821 |
| 317 | 8151/20000 | 41841/100000 | 80 | 125416 |
| 318 | 40797/100000 | 10451/25000 | 80 | 118583 |
| 319 | 20419/50000 | 20883/50000 | 80 | 136164 |
| 320 | 20439/50000 | 1304/3125 | 80 | 152405 |
| 321 | 40919/100000 | 41691/100000 | 80 | 141436 |
| 322 | 256/625 | 41653/100000 | 80 | 155010 |
| 323 | 41/100 | 8323/20000 | 80 | 167288 |
| 324 | 513/1250 | 41577/100000 | 80 | 125949 |
| 325 | 1027/2500 | 20769/50000 | 81 | 214011 |
| 326 | 257/625 | 83/200 | 81 | 194284 |
| 327 | 1029/2500 | 20731/50000 | 80 | 154831 |
| 328 | 41199/100000 | 41423/100000 | 81 | 94525 |
| 329 | 41239/100000 | 5173/12500 | 83 | 140306 |
| 330 | 20639/50000 | 20673/50000 | 83 | 112438 |
| 331 | 41317/100000 | 41307/100000 | 80 | 9949 |

## 7. Two five-loaded/two-D whole-cycle exclusions

Put c=6291/10000. The D cap constant from
[STRONG_DIRECT_CYCLE_BUDGET.md](STRONG_DIRECT_CYCLE_BUDGET.md) satisfies

```text
a_D=(2sqrt(3-sqrt(2))-1)/(1+sqrt(2)) < c.
```

For an exact check put A=11-2c-3c^2 and B=4+2c+2c^2. Both are positive,
and two squarings reduce the comparison to A<B*sqrt(2), with

```text
2B^2-A^2=190908527864239/10000000000000000>0.
```

Thus every D gap is strictly larger than pi-2atan(c).
The existing loaded-pair angle also satisfies

```text
tan(delta_*)=(7+6sqrt(14))/35>21/25,
```

because sqrt(14)>56/15, whose squared comparison is 3150>3136.
Therefore delta_*>atan(21/25).

Both angles Gamma+atan(21/25) and 4atan(c) lie in (pi/2,pi). Their exact
tangent difference is

```text
tan(Gamma+atan(21/25))=-573/460,

tan(Gamma+atan(21/25))-tan(4atan(c))
 =15299847106711053/5602659663671149940>0.
```

Tangent is strictly increasing on that interval, so

```text
Gamma+delta_*>4atan(c).                             (14)
```

Now take a whole simple-cycle component with five loaded bodies, two
single D transmitters and three direct loaded contacts. The contracted
loaded cycle follows actual radial order by
[RADIAL_ORDER_CYCLE_BUDGET.md](RADIAL_ORDER_CYCLE_BUDGET.md).
Among its three direct gaps, at least two are consecutive: two D gaps
can divide them into only two runs. Apply (1) to those two direct gaps,
the pair bound to the remaining direct gap, and the D cap bound to the
two D gaps. Their total is strictly greater than

```text
Gamma+delta_*+2pi-4atan(c)>2pi,
```

contradicting the circular gap sum. This proves both complete signatures:

| Fixed ID | Canonical word | Proof coverage |
| --- | --- | --- |
| C20-M07-L05-B02-T03 | LLLLDLD | All circle features, contact types, stresses and ten-square completions |
| C20-M07-L05-B03-T03 | LLLDLLD | All circle features, contact types, stresses and ten-square completions |

No refinement of the 336-entry master denominator is needed. Other open
cycle signatures and the branching components are not excluded by this
argument. The imported lower radius window remains the one explicitly
pinned in the earlier stress and cycle reductions.
