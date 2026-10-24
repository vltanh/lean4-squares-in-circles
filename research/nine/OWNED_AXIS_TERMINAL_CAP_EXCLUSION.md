# Uniform cap exclusion when the terminal separator is square-owned

This is a complete hand-checkable inequality. It uses no parameter table
or interval cover. It is intended as one step toward WEDGE.2; Y.ALL
additionally requires the separate strict-half-pocket capacity bound.

Let `R=sqrt(17)/2`, `n=(b,a)`, `0<=a<=b`, `a^2+b^2=1`.
Suppose a unit square T has an owned axis `m=(-B,A)`, where
`A,B>=0`, `A^2+B^2=1`. The following three conditions are incompatible:

```
T contained in the disk of radius R,
n.x >= k0 := 1/2+7*a/10  for every x in T,
m.x >= A/2-B           for every x in T.
```

The last condition is exactly the separation of T above/left of the
radial terminal `[1,2] x [-1/2,1/2]` along its owned axis m.
The slightly larger threshold `1/2+a/sqrt(2)` is therefore also excluded.

## 1. The support inequality and its two angular branches

Set

```
l=1-a,     f=b/2-a,       h=b+a/2,
E=3/2-3*a/10,
C=1+l*f,  D=l*h,
alpha=b*A+a*B,  beta=a*A-b*B.
```

Here `alpha>=0`, `alpha^2+beta^2=1`, and `-b<=beta<=a`.
Also `A/2-B=f*alpha+h*beta`.

Combining the two floor constraints in direction `n+l*m`, and then
using disk support in that direction, yields

```
k0+l*(A/2-B)+H(n)+l*H(m)+H(n+l*m)
  <= R*sqrt(1+l^2+2*l*beta).
```

Since m is an owned square axis, `H(m)=1/2` and direct projection on
the owned frame gives

```
H(n)+l*H(m)+H(n+l*m)
 = alpha+(|beta|+l+|beta+l|)/2
 >= alpha+l+max(beta,0).
```

It is enough, therefore, to prove that

```
E+C*sqrt(1-beta^2)+D*beta+max(beta,0)
  > R*sqrt(1+l^2+2*l*beta)                         (1)
```

for `-b<=beta<=a`.

We shall prove that each angular branch reduces to its endpoints,
and then prove all three endpoint inequalities explicitly.

Throughout, `0<=a<=1/sqrt(2)<3/4`, and we use

```
1-(3/5)*a^2 <= b <= 1-a^2/2-a^4/8,
C>=1-a*(1-a)>=3/4,
0<h<=sqrt(5)/2<9/8.
```

The lower bound for b is its chord bound on `a^2 in [0,1/2]`,
weakened using `sqrt(2)>7/5`. The upper bound follows by squaring its
positive right side: its square is `1-a^2+a^6/8+a^8/64`.

## 2. The branch beta>=0 is concave

Subtract the right side of (1) from the left and differentiate twice
with respect to beta. Its second derivative is

```
-C/(1-beta^2)^(3/2)
 + R*l^2/(1+l^2+2*l*beta)^(3/2) < 0.
```

Indeed the positive term is at most `R/(2*sqrt(2))<3/4`, because
`0<l<=1` and `t^2/(1+t^2)^(3/2)` is increasing on `[0,1]`.
The negative term is at most `-C<=-3/4`.
Thus only the endpoints beta=0 and beta=a need to be checked.

## 3. The branch beta<=0: strict concavity after squaring

Put `beta=-sin(delta)`, `alpha=cos(delta)`, with
`0<=delta<=pi/2-theta`, where `sin(theta)=a`.
The left side of (1) is

```
L=E+C*cos(delta)-D*sin(delta).
```

It is positive: since `C>0`, `D=l*h`, `k0>=1/2`, and `h<9/8`,

```
L >= E-D = k0+l*(1-h) > 1/2-l/8 >= 3/8.
```

We may therefore square. Define

```
P(delta)=L^2-(17/4)*(1+l^2-2*l*sin(delta)).
```

We prove `P''<0` throughout this branch. Put

```
U=E*C,
K=(17/4)*l-E*D,
S=C^2+D^2=1+2*l*f+(5/4)*l^2,
A0=U+C^2-D^2,
B0=K-C^2+D^2,
Z=2*C*D-(22/25)*l.
```

First, both `U` and `K` exceed `(11/5)*l`. For U, the lower bound
for b gives

```
C >= 3/2-(3/2)*a+(7/10)*a^2+(3/10)*a^3,

U-(11/5)*l
 >= 1/20-a/2+(3/2)*a^2+(6/25)*a^3-(9/100)*a^4 > 0.
```

The quadratic `1/20-a/2+(3/2)*a^2` has negative discriminant,
and the last two terms are nonnegative. For K,

```
K/l = 17/4-E*h > 17/4-(3/2)*(9/8)=41/16>11/5.
```

For `c=cos(delta)`, `s=sin(delta)`, we have
`c+s-1 >= (4/5)*c*s`. This follows on putting `t=c+s in [1,sqrt(2)]`:
the difference equals `(t-1)*(1-(2/5)*(t+1))>=0`.
Consequently

```
U*c+K*s >= U*c^2+K*s^2+(44/25)*l*c*s.
```

Direct differentiation now gives

```
P''/2
 = -(C^2-D^2)*cos(2*delta)+2*C*D*sin(2*delta)-U*c-K*s
 <= -A0*c^2+2*Z*c*s-B0*s^2.                    (2)
```

The quadratic form on the right is strictly negative, as shown next.

### 3.1. Weighted diagonal dominance: the first inequality

Let `r=22/25`. Since `D=l*h`,

```
A0-(C/D)*Z = E*C-S+r*C/h.
```

As `h<9/8`, we have `r/h>3/4`. Hence

```
A0-(C/D)*Z
 > C*(E+3/4)-S
 = (11/5)*a-(5/4)*a^2+l*f*(1/4-3*a/10)
 >= a*(39/20-7*a/10-3*a^2/10) >= 0.
```

The last inequality uses `f>=-a` and `a<=3/4`.
Thus the first weighted diagonal dominance inequality is strict.

### 3.2. Weighted diagonal dominance: the second inequality

We first prove

```
h/C >= 2/3+a/2.                                  (3)
```

Expanding and using `b>=1-(3/5)*a^2` gives

```
6*h-(4+3*a)*C
 = b*(4+a/2+3*a^2/2)-4+4*a-a^2-3*a^3
 >= a*(9/2-19*a/10-33*a^2/10-9*a^3/10)
 >= (537/640)*a >= 0,
```

where the last bound uses `a<=3/4`. This proves (3).

Now

```
B0-(D/C)*Z = (17/4)*l-E*D-S+r*l*D/C.
```

Using (3), the identity for S, and
`b<=1-a^2/2-a^4/8`, gives the following polynomial lower bound:

```
B0-(D/C)*Z >= Q(a),

Q(a)=13/150+(47/30)*a-(127/75)*a^2-(111/100)*a^3
     +(37/80)*a^4-(7/20)*a^5+(3/80)*a^6.
```

For clarity, before substituting the upper bound for b the lower
expression is exactly

```
(17/4)*l-1-(199/300-11*a/25)*l^2
 -l*(5/2-3*a/10)*b+l*(5*a/4+3*a^2/20).
```

The polynomial Q is strictly concave on `[0,1]`: using `a^2<=a`
and `a^4<=a^3`,

```
Q''(a) = -254/75-(333/50)*a+(111/20)*a^2-7*a^3+(9/8)*a^4
       <= -254/75-(111/100)*a-(47/8)*a^3 < 0.
```

Its two relevant endpoint values are positive:

```
Q(0)=13/150,
Q(1/sqrt(2))=-2047/3200+1109/(1200*sqrt(2))
            >347/48000>0,
```

using `1/sqrt(2)>7/10`. Therefore Q is positive on the whole
interval `0<=a<=1/sqrt(2)`, proving the second strict inequality.

Finally `Z>0`: `C>=3/4`, `h>=b>=1/sqrt(2)`, so
`2*C*h>=3/(2*sqrt(2))>1>r` and `Z=l*(2*C*h-r)>0`.
Thus

```
A0*c^2-2*Z*c*s+B0*s^2
 = (A0-(C/D)*Z)*c^2+(B0-(D/C)*Z)*s^2
   +Z*(sqrt(C/D)*c-sqrt(D/C)*s)^2 > 0.
```

Together with (2), this proves `P''<0`. Hence only the endpoints
beta=0 and beta=-b remain.

## 4. Endpoint beta=0

At this endpoint the left side is

```
L0=k0+1+l*(l+b/2).
```

Using `b>=1-(3/5)*a^2`,

```
L0 >= J(a)=3-(9/5)*a+(7/10)*a^2+(3/10)*a^3.
```

Put `x=a-1/2`, so `-1/2<=x<=1/4`. Direct expansion gives

```
J(a)^2-(17/4)*(1+l^2)
 = 9/256+(13/64)*x+(587/320)*x^2-(5/8)*x^3
   +(319/400)*x^4+(69/100)*x^5+(9/100)*x^6.
```

The coefficient of x^2 after grouping its cubic term is at least
`587/320-5/32=537/320>3/2`. The bracket multiplying x^4 is at
least `319/400-69/200=181/400>0`. Therefore the displayed expression
is at least

```
9/256+(13/64)*x+(3/2)*x^2 >= 695/24576>0.
```

Since J is positive, this proves (1) at beta=0.

## 5. Endpoint beta=-b

The left side is `k0+a=1/2+17*a/10`. Using the lower bound for b,

```
(k0+a)^2-(17/4)*(1+l^2-2*l*b)
 >= T(a)=1/4+(17/10)*a-(323/50)*a^2+(51/10)*a^3.
```

Put `x=a-2/3`, so `-2/3<=x<=1/12`. Then

```
T(a)=7/300-(17/150)*x+x^2*(187/50+(51/10)*x).
```

The bracket is at least `17/50>0`, and the linear part is at least
`7/300-17/1800=1/72>0`. This proves (1) at beta=-b.

## 6. Endpoint beta=a

Here the left side is `2+b+a/5`, and the right side is
`R*sqrt(2-a^2)`. The elementary estimates

```
b>=1-(59/100)*a^2,
sqrt(2-a^2)<99/70-(707/2000)*a^2,
R<33/16
```

give

```
2+b+a/5-R*sqrt(2-a^2)
 >93/1120+a/5+(4451/32000)*a^2>0.
```

The square-root upper estimate is its tangent bound at a=0,
weakened using `sqrt(2)<99/70` and `1/(2*sqrt(2))>707/2000`.
All three endpoints hold. Sections 2 and 3 therefore establish (1)
throughout both branches, contradicting the necessary support inequality.
