# A vertical endpoint path cannot also be normal to the common source edge

**Status:** reviewed exact conditional hand proof with a finite rational
table; root and independent full mathematical reviews passed on 2026-10-31.
This excludes two reflected support rows
inside LSLSLD. It does not close the whole signature or assert a
completion-capacity bound.

Use the entire both-unique-endpoint branch and notation of
[ONE_DIAGONAL_TWO_SIDE_COMMON_SOURCE_EDGE.md](ONE_DIAGONAL_TWO_SIDE_COMMON_SOURCE_EDGE.md).
Suppose A's S direction is vertical, so p=0, q=1, and its top-side
contact parameter alpha remains arbitrary in `[0,1)`. Suppose also that
the C support is row E_A: this same S direction is normal to C's common
edge. No assumption is made about C's circle multiplicity or load split.

**Theorem.** This support row is impossible. Horizontal reflection also
excludes a vertical B endpoint combined with row E_B.

## 1. All remaining quantities reduce to two scalar parameters

Put

```text
d=sqrt(2),       K=2+d,       H=H_A,
n_B=(−r,s),     0<r<s,       r²+s²=1,
delta=1−s,      B=H_B.
```

The case r=0 was already excluded by the common-edge classification.
The horizontal-edge equation in row E_A gives

```text
B=H−delta.                                        (1)
```

Since H²−B²=v²−u² and u+v=K,

```text
u=K/2−delta*(2H−delta)/(2K),       v=K−u.           (2)
```

The common-edge contact length is

```text
ell=d+alpha−r<=1.
```

Consequently `r>=d−1`, while the unique B endpoint gives
`r<1/sqrt(2)`. In particular,

```text
1/12<delta<3/10.                                  (3)
```

For the lower bound, `s²<=2d−2<5/6<(11/12)²`, using d<17/12.
For the upper bound, `s>1/sqrt(2)>7/10`.

Normalize the D magnitude to one. B's torque identity gives

```text
D=v*s−B*r>0,
h+B=B*(s−r)/D.                                    (4)
```

A's vertical-side torque identity, retaining alpha, is

```text
alpha=1−u*(h+H)/H.
```

Using (1) and (4),

```text
ell−1
 = d−r−(u/H)*[delta+B*(s−r)/D]
 = F/(H*D),                                       (5)

F=(d−r)*H*(v*s−B*r)
  −u*[delta*(v*s−B*r)+B*(s−r)].
```

It remains to prove F>0. That will contradict ell<=1. Notice that no
circle equation or torque equation for C has been used.

## 2. A uniform height interval

The radius bounds and (2)--(3) give

```text
u>K/2−delta*H/K
 >17/10−(3/10)*(17/8)/(17/5)
 =121/80>3/2.
```

Here `H<=R<17/8` and `K>17/5`. Thus
`H²=R²−u²<9/2−9/4=9/4`, so H<3/2.

For the other direction, suppose H<=1. Since H and B are both greater
than 1/2, (2)--(3) imply

```text
u=K/2−delta*(H+B)/(2K)
 <K/2−1/(24K)
 <171/100−1/100=17/10.
```

The last line uses `K/2<171/100` and `K<7/2`, hence
`1/(24K)>1/84>1/100`. It follows that

```text
R²=H²+u²<1+289/100=389/100<(79/40)²,
```

a contradiction. Therefore every putative realization satisfies

```text
1<H<3/2.                                           (6)
```

## 3. Concavity reduces the height interval to its endpoints

For fixed r,s,d, write

```text
a=K/2+delta²/(2K),       b=delta/K,
u=a−b*H,
D=c−e*H,
c=(K−a)*s+delta*r,      e=r−b*s,
f=delta*(c−s+r),        g=s−r−delta*e.
```

Then the polynomial in (5) is

```text
F=(d−r)*H*(c−e*H)−(a−b*H)*(f+g*H).
```

Its coefficient of H² is `−(d−r)*e+b*g`. From (3),

```text
0<b<1/10,       e>r−b>3/10,
d−r>1/sqrt(2)>7/10,       g<1.
```

Thus that coefficient is strictly less than
`−(7/10)*(3/10)+1/10=−11/100`. The function F is strictly concave
in H. To prove F>0 throughout (6), it suffices to prove it at H=1 and
H=3/2 for every allowed r.

## 4. The complete rational endpoint table

Use the half-angle parameter `t=r/(1+s)`. Then

```text
r=2t/(1+t²),       s=(1−t²)/(1+t²),
1/5<t<5/12.
```

Indeed `t>r/2>1/5` and `t<sqrt(2)−1<5/12`. Also

```text
140/99<d<99/70,
```

as witnessed by `140²<2*99²` and `99²>2*70²`.

For row j=0,...,15, use the closed rational interval

```text
T_j=[1/5+13j/960, 1/5+13(j+1)/960].                (7)
```

These intervals cover `[1/5,5/12]` without gaps. Evaluate the following
expressions by ordinary rational interval arithmetic, in the displayed
order, for each of H=1 and H=3/2:

```text
t in T_j,       d in [140/99,99/70],       K=2+d,
r=2t/(1+t*t),   s=(1−t*t)/(1+t*t),       delta=1−s,
u=K/2−delta*(2H−delta)/(2K),             v=K−u,
B=H−delta,
F=(d−r)*H*(v*s−B*r)
  −u*(delta*(v*s−B*r)+B*(s−r)).                    (8)
```

All divisors in this evaluation are positive intervals. Products take
the minimum and maximum of the four endpoint products; reciprocals
reverse the positive interval endpoints. Thus these operations enclose
every actual value without a dependency assumption.

The table gives lower bounds for F, in units of 1/1000. Each entry is
the interval evaluation's lower endpoint rounded downward to that unit.
Every entry is positive.

| j | `1000 * lower bound`, H=1 | `1000 * lower bound`, H=3/2 |
| --- | ---: | ---: |
| 0 | 178 | 66 |
| 1 | 162 | 46 |
| 2 | 148 | 30 |
| 3 | 135 | 18 |
| 4 | 125 | 10 |
| 5 | 115 | 6 |
| 6 | 108 | 6 |
| 7 | 101 | 9 |
| 8 | 96 | 15 |
| 9 | 92 | 24 |
| 10 | 89 | 36 |
| 11 | 87 | 50 |
| 12 | 85 | 67 |
| 13 | 85 | 85 |
| 14 | 84 | 106 |
| 15 | 85 | 128 |

The self-contained exact checker
[check_diagonal_vertical_source_side.py](check_diagonal_vertical_source_side.py)
reproduces every entry with rational arithmetic and verifies the printed
table against this file. No root finding or floating-point calculation
is a premise of the proof.

Both endpoint values of F are at least `6/1000>0`. Concavity and (6)
give F>0 throughout the allowed height interval. Equation (5) now forces
ell>1, contradicting the common edge's unit length. This completes the
stated support-row exclusion, including every alpha and every circle
feature at C.
