# Exclusion of the diagonal-side unique-circle-vertex five-cycle

**Status: independently audited hand proof with sixteen explicit rational rows
(2026-10-29). No Lean verification is claimed.**

**Theorem.** In the unique-circle-vertex normal form for the positive
component `A-U-C-V-B-A`, U cannot be diagonal and V side type.

This supplies the arithmetic needed after the physical classification in
[DIAGONAL_SIDE_CONTACT_CLASSIFICATION.md](DIAGONAL_SIDE_CONTACT_CLASSIFICATION.md).
That classification excludes vertex support at A and reduces side support
to the two load cases treated below. Together they exclude the D-S branch.
The other remaining transmitter choices and the unrestricted n=10 theorem
are not asserted here.

Set `R_0=79/40`, and retain

```
R_0<=R<=3/sqrt(2),
rho=q/p, p=1/sqrt(1+rho^2), q=rho p,
k=sqrt(2)p-q, 0<d<=1-k,
tau=(1-d rho)/(1-d),
w=p+q, v=p-q,
c=(p+q tau)/sqrt(1+tau^2),
e=(p tau-q)/sqrt(1+tau^2),
N=sqrt(2)+w-Rc, T=v-Re.
```

These are the coordinates of the contact Q_A in the orthonormal basis
`n=(-p,-q), t=(q,-p)`. The side-supported square is
`Q_A+[0,1]n+[-u,1-u]t`, and its far vertices have coordinates
`(N+1,T-u)` and `(N+1,T+1-u)`.

The previously proved contact proximity gives `N^2+T^2<(R-1)^2`.
The classification leaves two arithmetic cases:

1. The sole loaded vertex is `(N+1,T-u)`, and
   `0<=u<=min(-T/N,(1-k-d)/q)`.
2. Both far vertices are on the containing circle, in which case
   `N=L=sqrt(R^2-1/4)-1`, `u=T+1/2`, and `u<=(1-k-d)/q`.

We prove that the far vertex in case 1 is circle-clear, and that case 2 is
impossible. The opposite sole-loaded choice has already been excluded by
the physical torque argument in the classification.

## 1. Uniform bounds

Since k<1, squaring `sqrt(2)p<1+q` gives q>1/3, hence
`rho>1/(2sqrt(2))=sqrt(2)/4>7/20`. Also rho<1. The proximity manuscript
proved `1<=tau<=T_max(rho)<5/4`, where

```
T_max(rho)=rho+(1-rho)sqrt(1+rho^2)/(sqrt(2)-rho).
```

It proved T_max increasing through rho=2/3, with these explicit bounds:

```
T_max(2/5)<26/25,
T_max(1/2)<9/8,
T_max(3/5)<47/40,
T_max(2/3)<121/100.
```

All four follow directly from its printed rational table.

The quantity e increases with tau and decreases with rho. If rho<=1/2,
use tau<9/8 and rho>1/3 to get `e<19/sqrt(1450)<1/2`. If rho>=1/2,
use tau<5/4 to get `e<6/sqrt(205)<1/2`. Therefore

```
0<e<1/2, c>sqrt(3)/2.
```

Since tau>=1 and p>q, `c<=w/sqrt(2)`. Consequently

```
N >= sqrt(2)+w-(3/sqrt(2))(w/sqrt(2))
  =sqrt(2)-w/2 >=1/sqrt(2)>7/10.
```

Also T<0. To bound its magnitude, for fixed R,tau write

```
-T=[A+B rho]/sqrt(1+rho^2),
A=R tau/sqrt(1+tau^2)-1>0,
B=1-R/sqrt(1+tau^2)<0.
```

This decreases with rho and increases with tau and R. For rho<=1/2,
evaluate at rho=1/3,tau=9/8. Here e<1/2 and v=2/sqrt(10)>5/8;
using R<17/8 gives `-T<7/16<9/20`.
For rho>=1/2, evaluate at rho=1/2,tau=5/4. Here
`e=6/sqrt(205)<21/50` and `v=1/sqrt(5)>4/9`, giving
`-T<1613/3600<9/20`. Thus

```
0<-T<9/20,     0<-T/N<9sqrt(2)/20<2/3.                  (1)
```

## 2. Monotonicity and reduction to R=R_0

At fixed rho, N and -T increase with d, and N decreases with R.
At fixed d,R, both N and -T decrease with rho. Here are useful explicit
justifications for the latter statements. Put

```
S_d=sqrt((1-d)^2+(1-d rho)^2),
e=v/S_d.
```

Differentiating the angle `atan(tau)-atan(rho)` gives
`c_rho>=w'/S_d>=w'/sqrt(2)`, hence
`N_rho<=w'(1-R/sqrt(2))<0`.
Similarly,
`T_rho>=(Rc-w)/(1+rho^2)>0`, using `c>sqrt(3)/2` and
`R_0 sqrt(3)/2>sqrt(2)>=w`. The table below explicitly checks e<1/2
on every slightly enlarged rectangle used for these comparisons.

Put `U=(1-k-d)/q`. The expression U-T decreases with d. Its derivative is

```
-1/q+Rc(1-rho)/[(1-d)^2+(1-d rho)^2] <0.
```

For a direct bound, set x=1-rho and h=sqrt(2)-1. Then
`k=(h+x)/sqrt(1+rho^2)>(h+x)/sqrt(2)`, and the denominator above is
at least 2k^2. Also qR<=3/2. Thus the positive derivative term, multiplied
by q, is less than

```
(3/2)x/(h+x)^2 <=3/(8h)<1.
```

The last inequality follows from sqrt(2)>11/8.

For case 1, the squared-radius excess is bounded above by the smaller of

```
F_torque=(N+1)^2[1+(T/N)^2]-R^2,
F_projection=(N+1)^2+(T-U)^2-R^2.                       (2)
```

Both decrease with R at fixed rho,d. For the first put z=-T/N. Direct
calculation gives

```
(1/2) dF_torque/dR
 =(N+1)[-c+c z^2/N+e z(N+1)/N]-R.
```

By (1), `z<2/3`, `N>7/10`, and `e<1/2`. The bracket is less than
17/21: the first two terms have negative sum, and the final term is
at most `(1/2)(2/3)(1+10/7)=17/21`. Proximity gives N+1<R, so the
derivative is strictly negative.

For the second, set A_0=sqrt(2)+w and B_0=v. It is affine in R, with
slope `-2[(A_0+1)c+(B_0-U)e]<0`. Indeed U<1 because
`sqrt(2)p>1` and d>0, while A_0+1>3, c>1/2, and e<1/2.
It therefore suffices to prove the desired upper bound in (2) at R=R_0.

## 3. The sixteen interval rows

Every integer in the next three tables represents that integer divided by
`M=1000000`, except for the row number and the explicitly written rational
endpoints and cut zeta. Put

```
r_-=1414213/M, r_+=1414214/M,
sqrt(2) lies strictly between r_- and r_+,
S_a^-= (s_a-1)/M, S_a^+=s_a/M,
S_b^+=s_b/M.
```

For a row [a,b], D bounds `1-k(b)` above; E bounds
`1-k(b)-(3/20)q(b)` above. The cut zeta divides the d-interval.

| Row | a | b | zeta | D | E |
| --- | --- | --- | --- | ---: | ---: |
| 1 | 7/20 | 2/5 | 0 | 58327 | 2619 |
| 2 | 2/5 | 17/40 | 1/50 | 89597 | 30926 |
| 3 | 17/40 | 9/20 | 47/1000 | 120714 | 59160 |
| 4 | 9/20 | 19/40 | 147/2000 | 151631 | 87272 |
| 5 | 19/40 | 1/2 | 1/10 | 182304 | 115222 |
| 6 | 1/2 | 21/40 | 253/2000 | 212693 | 142968 |
| 7 | 21/40 | 11/20 | 153/1000 | 242764 | 170476 |
| 8 | 11/20 | 23/40 | 179/1000 | 272482 | 197711 |
| 9 | 23/40 | 3/5 | 41/200 | 301819 | 224645 |
| 10 | 3/5 | 5/8 | 231/1000 | 330749 | 251250 |
| 11 | 5/8 | 13/20 | 257/1000 | 359252 | 277503 |
| 12 | 13/20 | 7/10 | 61/200 | 414895 | 328875 |
| 13 | 7/10 | 3/4 | 71/200 | 468630 | 378630 |
| 14 | 3/4 | 4/5 | 203/500 | 520381 | 426677 |
| 15 | 4/5 | 9/10 | 497/1000 | 617789 | 517444 |
| 16 | 9/10 | 1 | 607/1000 | 707108 | 601042 |

For any rational f define `tau_f=(1-fa)/(1-f)`.
The following are integer upper-root bounds for
`sqrt(1+a^2)`, `sqrt(1+b^2)`, `sqrt(1+tau_zeta^2)`,
`sqrt(1+tau_D^2)`, and `sqrt(1+tau_E^2)`, respectively.
For each column, reducing its displayed integer by one gives a strict
lower-root bound. Each assertion is a rational inequality verified by
squaring, using D and E as rationals with denominator M.

| Row | s_a | s_b | s_zeta | s_D | s_E |
| --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 1059482 | 1077033 | 1414214 | 1442964 | 1415421 |
| 2 | 1077033 | 1086566 | 1422899 | 1456566 | 1427818 |
| 3 | 1086566 | 1096586 | 1434406 | 1471092 | 1440007 |
| 4 | 1096586 | 1107080 | 1445396 | 1485352 | 1451877 |
| 5 | 1107080 | 1118034 | 1456046 | 1499266 | 1463357 |
| 6 | 1118034 | 1129436 | 1466310 | 1512746 | 1474373 |
| 7 | 1129436 | 1141272 | 1476133 | 1525698 | 1484845 |
| 8 | 1141272 | 1153528 | 1485211 | 1538015 | 1494687 |
| 9 | 1153528 | 1166191 | 1493718 | 1549582 | 1503807 |
| 10 | 1166191 | 1179248 | 1501583 | 1560271 | 1512106 |
| 11 | 1179248 | 1192687 | 1508724 | 1569941 | 1519478 |
| 12 | 1192687 | 1220656 | 1526692 | 1599363 | 1540274 |
| 13 | 1220656 | 1250000 | 1535414 | 1612191 | 1548879 |
| 14 | 1250000 | 1280625 | 1539789 | 1617427 | 1551363 |
| 15 | 1280625 | 1345363 | 1560218 | 1658628 | 1573186 |
| 16 | 1345363 | 1414214 | 1527339 | 1594093 | 1524468 |

The final table gives upper bounds on N(a,zeta), -T(a,zeta), N(a,D),
U(b,zeta), and N(a,E), all at R=R_0.

| Row | n_zeta | m_zeta | n_D | u_zeta | n_E |
| --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 908947 | 243279 | 926198 | 157050 | 909678 |
| 2 | 903540 | 231937 | 921820 | 177934 | 906232 |
| 3 | 904681 | 235375 | 923531 | 179630 | 907580 |
| 4 | 905255 | 238143 | 924685 | 182099 | 908429 |
| 5 | 905406 | 240491 | 925296 | 184036 | 908793 |
| 6 | 905159 | 242381 | 925380 | 185428 | 908691 |
| 7 | 904535 | 243777 | 924956 | 186263 | 908143 |
| 8 | 903459 | 244349 | 924038 | 187537 | 907168 |
| 9 | 902056 | 244329 | 922645 | 188182 | 905786 |
| 10 | 900347 | 243658 | 920792 | 188206 | 904018 |
| 11 | 898349 | 242268 | 918495 | 187621 | 901886 |
| 12 | 899686 | 252772 | 922270 | 191633 | 903903 |
| 13 | 893693 | 244360 | 914932 | 189383 | 897392 |
| 14 | 887012 | 231867 | 905982 | 183098 | 889795 |
| 15 | 884281 | 236854 | 905648 | 180561 | 887025 |
| 16 | 866677 | 170239 | 876663 | 141574 | 866280 |

Here are all the remaining rational checks represented by the tables.
When a lower-case table entry appears below it denotes the displayed
integer divided by M. For f=zeta,D,E define

```
S_f^-=(s_f-1)/M, S_f^+=s_f/M,
B_N(f)=r_+ +(1+a)/S_a^- -R_0(1+a tau_f)/(S_a^+ S_f^+),
B_T(f)=(1-a)/S_a^- [R_0/((1-f)S_f^-)-1].
```

Every row satisfies

```
D >=1-(r_- -b)/S_b^+,
E >=1-(r_- -(17/20)b)/S_b^+,
zeta<=D,
(tau_D-a)/(S_a^- S_D^-)<1/2,
n_zeta>=B_N(zeta), m_zeta>=B_T(zeta),
n_D>=B_N(D), n_E>=B_N(E),
u_zeta>=1+[(1-zeta)S_b^+-r_-]/b,
n_D<93/100, n_E<91/100, m_zeta<9/20.                    (3)
```

All denominators are positive. These checks and the root squares are
explicit rational arithmetic, with no numerical optimization premise.
The e-bound in (3) establishes e<1/2 throughout each rectangle
`a<=rho<=b, 0<=d<=D`, because e decreases with rho and increases with d.
Thus the monotonicities used above remain valid at the enlarged corners.

## 4. The sole far-minus circle vertex is impossible

At R=R_0, if `0<d<=zeta`, monotonicity in rho,d bounds N and -T by
n_zeta and m_zeta. The function `(N+1)^2(1+M_0^2/N^2)` increases with
both N and M_0 for `N>=7/10`, `0<=M_0<=9/20`, since its N derivative
has the sign of `N^3-M_0^2>0`.
Every row except the first satisfies the exact rational comparison

```
(1+n_zeta)^2[1+(m_zeta/n_zeta)^2]
  < R_0^2-1/200.                                      (4)
```

The first row has zeta=0, so this case is empty.

If `d>=zeta`, N is bounded above by n_D. Since U-T decreases with d,
it is at most `U(rho,zeta)-T(rho,zeta)`. The first summand increases
with rho: differentiating gives

```
U_rho=[sqrt(2)-(1-zeta)/sqrt(1+rho^2)]/rho^2>0.
```

The second summand decreases with rho. Thus U-T<=u_zeta+m_zeta.
Every row satisfies the exact rational comparison

```
(1+n_D)^2+(u_zeta+m_zeta)^2 < R_0^2-1/200.              (5)
```

For the sole far-minus vertex, u<=min(-T/N,U), so its squared-radius
excess is at most the smaller of (2). Equations (4)--(5) prove this
minimum is below -1/200 at R=R_0. Radius monotonicity proves it is
negative throughout the original radius interval. The alleged circle
vertex is strictly inside the disk, a contradiction.

## 5. Both far vertices on the circle are impossible

Independently of the cut and torque assumptions, the n_D column bounds
N for every allowed rho,d,R. Thus N<93/100. If N=L, this gives

```
R^2=(N+1)^2+1/4<(193/100)^2+1/4=39749/10000<4,
```

so R<2. We improve the T bound in this case to `-T<7/20`.
For fixed tau,R the expression -T decreases with rho, and it increases
with tau,R. The following five ranges and upper tau bounds therefore
suffice. The e and v values are evaluated at the lower rho endpoint and
the displayed upper tau. Each rational comparison follows by squaring.

| rho range | tau upper | e upper at lower endpoint | v lower there | resulting upper bound for -T |
| --- | --- | --- | --- | --- |
| [1/3,2/5] | 26/25 | 53/sqrt(13010)<93/200 | 2/sqrt(10)>63/100 | 3/10 |
| [2/5,1/2] | 9/8 | 1/sqrt(5)<9/20 | 3/sqrt(29)>11/20 | 7/20 |
| [1/2,3/5] | 47/40 | 54/sqrt(19045)<197/500 | 1/sqrt(5)>11/25 | 87/250 |
| [3/5,2/3] | 121/100 | 305/sqrt(837794)<1/3 | 2/sqrt(34)>1/3 | 1/3 |
| [2/3,1] | 5/4 | 7/sqrt(533)<31/100 | 1/sqrt(13)>27/100 | 7/20 |

All resulting inequalities are strict, using R<2. Consequently
`u=T+1/2>3/20`. Horizontal contact overlap now gives

```
d <=1-k-uq <1-k-(3/20)q.
```

The last right-hand side increases with rho: its subtracted factor is
`(sqrt(2)-(17/20)rho)/sqrt(1+rho^2)`, whose derivative is negative.
The E column consequently bounds d above on each rho interval, and the
n_E column bounds N above. Equation (3) gives N<91/100.
But R>=79/40 implies L>91/100, because

```
(191/100)^2+1/4 =38981/10000 <6241/1600=(79/40)^2.
```

This contradicts N=L, excluding the two-circle-vertex case.

Together with the physical classification, these two arithmetic
contradictions close the remaining side-supported diagonal endpoint.
The tables are finite hand-checkable certificates: every root bracket,
monotonicity, bound, and strict arithmetic comparison is printed here.


The optional [exact checker](check_diagonal_side_clearance.py) reads the
three printed tables and checks their rational inequalities, root brackets,
coverage, both strict clearance margins, and the auxiliary five-range
bounds. The printed finite argument is the proof; the checker is an
independent way to verify its arithmetic.
