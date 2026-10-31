# Global exclusion of the fixed side/vertex ring pattern

**Status:** independently reviewed computer-assisted exact-arithmetic theorem.
This closes the nonuniform branch of the particular ownership pattern in
[SEVEN_RING_ONE_CHIRALITY.md](SEVEN_RING_ONE_CHIRALITY.md). It does not classify the other loaded-ring patterns or close
the unrestricted ten-square proof. A proof of the cone inequalities below
without exhaustive interval subdivision remains a hand-proof task.

The verifier is [check_seven_ring_action.cpp](check_seven_ring_action.cpp).
It uses exact dyadic interval arithmetic, including integer-checked square
roots. Its exhaustive cover has no unresolved neighborhood around the
uniform solution.

## 1. The precise statement

Assume the side/vertex ownership pattern of the cited note, with seven
positive circle loads, seven positive contact magnitudes, and

```text
79/40 <= R <= 3/sqrt(2).
```

Assume also the physical containment and separation hypotheses used in
[SEVEN_RING_INTERNAL_CONCURRENCE.md](SEVEN_RING_INTERNAL_CONCURRENCE.md).
Then the seven angle-action variables are all equal to `pi/7`. Consequently
all force magnitudes and frame gaps are equal, the radius is

```text
R = cos(pi/7) + 1/(2sin(pi/7)),
```

and [REGULAR_SEVEN_LOADED_RING.md](REGULAR_SEVEN_LOADED_RING.md) excludes
completion by three further unit squares.

Only the one-chirality contact ownership is addressed. The geometric proof
that all loaded rings have this ownership is still absent.

## 2. An algebraic map in height coordinates

Let `x=sin(a)` and `y=sin(b)` for consecutive angles in
[SEVEN_RING_ANGLE_ACTION.md](SEVEN_RING_ANGLE_ACTION.md). Define

```text
c  = sqrt(1-y^2),
A  = R c - 1,             B = R y,
D2 = R^2+1-2R c,          H = R x-1,
k  = sqrt(D2-H^2),
d  = (A k+B H)/D2,        e = (B k-A H)/D2,
C  = [k(R-c)+H y]/D2,
K  = k c/C,
q  = [R^2+1-(R y-1)^2-K^2]/(2R),
f_R(x,y) = sqrt(1-q^2).                                  (1)
```

At a physical solution, these quantities are respectively

```text
d=cos(delta), e=sin(delta), C=cos(beta),
k=k_(i-1), K=k_i, q=cos(alpha_(i+1)).
```

Indeed, the first contact equation and its positive derivative give the
formulas for `d,e,k`. Criticality of the angle sum gives `K=k c/C`.
The next identity

```text
K^2=R^2+1-2R cos(alpha_(i+1))-(R y-1)^2
```

then gives `q`. All relevant cosines and heights are positive. Thus every
physical solution gives a period-seven orbit of

```text
T_R(x,y)=(y,f_R(x,y)).                                  (2)
```

This implication is all that the proof needs; a general orbit of (2) is
not asserted to reconstruct a packing.

The necessary conditions used for exclusion of interval boxes are:

* `79/40<=R<=3/sqrt(2)`;
* each input and output height `t` satisfies `0<t<1`,
  `R t>1/2`, and `R sqrt(1-t^2)>1/2`;
* `k>0`, `d>0`, `e>0`, and `C>0`;
* `0<q<1` and `R q>1/2`;
* `d y<=C`.

The last inequality follows from internal concurrence. In the body's frame,
write its loaded vertex as `w=(R cos(b),-R sin(b))`. The outgoing line has
first coordinate `R cos(b)-lambda`, so its intersection with the radial
load line differs from `w` by

```text
(-lambda, lambda tan(b)).
```

The concurrence point belongs to the square; hence `lambda tan(b)<=1`.
Since `lambda=d cos(b)/C`, this is exactly `d y<=C`. Equality is allowed.
No nonneighbor separation test or additional numerical packing premise is
used in the verifier.

## 3. A uniform reference state for every radius

There is a unique `s` in `(0,1)` with

```text
R=sqrt(1-s^2)+1/(2s),                                   (3)
```

in the radius window under consideration: the right side is strictly
decreasing. In fact

```text
413/1000 < s < 23/50.                                  (4)
```

For the lower endpoint put `s0=413/1000` and
`L=7/2+s0^2-1/(4s0^2)=376085283761/170569000000>0`. Direct
rational arithmetic gives

```text
(1-s0^2)/s0^2 - L^2
 =35075577408109694879/29093783761000000000000 > 0.
```

Thus the square of the right side of (3) at `s0` exceeds `9/2`.
At `s1=23/50`,

```text
(79/40-1/(2s1))^2-(1-s1^2)=4681/21160000>0,
```

and `79/40-1/(2s1)>0`. This proves (4).

The pair `(s,s)` is a fixed point of (2). Setting `a=b=asin(s)` and
`delta=2a` solves the contact equation because `2Rs=1+2s sqrt(1-s^2)`.
The positive derivative is

```text
k0=s^2+sqrt(1-s^2)/(2s)>0.
```

Here `beta=a`, so criticality gives the same next `k`, and (1) gives the
next height `s`.

Every physical height lies in `(23/100,49/50)`: its lower bound is at
least `sqrt(2)/6>23/100`, while its upper bound is at most
`sqrt(17/18)<49/50`. Therefore the closed rational box

```text
[s0,s1] x [23/100,49/50] x [23/100,49/50]                 (5)
```

in variables `(s,x,y)` covers all cases, with `R` defined by (3).

## 4. The finite cone lemma

For a pair `(x,y)` set

```text
X=(x-s,y-s),
z=f_R(x,y), w=f_R(y,z), Y=(z-s,w-s),
D=X dot Y,
J=(y-s)(z-s)-(x-s)(w-s).                                (6)
```

The verifier establishes the following finite statement on (5):

> Either one of the necessary physical conditions in Section 2 fails
> within two forward steps, or, for `X!=0`,
>
> ```text
> (y-s)^2-(x-s)(z-s)>0,
> D<0,                  (9/20)D<J<-D.                   (7)
> ```

The first condition concerns the one-step orientation and is part of the
certificate. The even winding count used below must not be inferred from
the two-step bounds alone.

The check is exhaustive interval subdivision, with two kinds of successful
cone leaf. Away from the fixed point it checks (7) directly. Near the fixed
point it uses exact divided differences, so the strict bounds are proved
for every nonzero displacement, however small.

For the latter, each expression `g(x,y)` is accompanied by coefficients
`a,b` satisfying exactly

```text
g(x,y)-g(s,s)=a(x-s)+b(y-s).
```

Products, quotients, and roots use the identities

```text
uv-u0v0 = [(u+u0)(v-v0)+(v+v0)(u-u0)]/2,

q-q0 = [2(u-u0)-(q+q0)(v-v0)]/(v+v0),
  where q=u/v, q0=u0/v0,

sqrt(u)-sqrt(u0)=(u-u0)/(sqrt(u)+sqrt(u0)).
```

The divisions are only evaluated when their interval denominators avoid
zero. The known identity `f_R(s,s)=s` is substituted at the end of each
step. Thus `z-s=a(x-s)+b(y-s)` and `Y=M X` hold exactly, with interval
enclosures for `a,b` and the two by two matrix `M`.

The one-step condition follows from `-a>0` and `4(-a)-b^2>0`.
For the two-step conditions, define symmetric matrices

```text
Q=-sym(M),
N=sym([0 -1; 1 0] M).
```

The checker proves positive definiteness of

```text
Q,       N+(9/20)Q,       Q-N.
```

A symmetric two by two matrix is accepted only when both diagonal lower
bounds and its determinant lower bound are strictly positive. This proves
(7) for all `X!=0`, including boxes meeting the fixed-point curve.

## 5. Why the cone lemma excludes period seven

In (6), `D` is the ordinary dot product of `X` and `Y`, and `J` is
their clockwise cross product.

If an orbit contains `(s,s)`, determinism makes the whole orbit uniform.
Otherwise all centered states are nonzero. The first inequality in (7)
gives a unique clockwise one-step angle `theta_i` in `(0,pi)`. The
remaining inequalities put the clockwise two-step angle in

```text
3pi/4 < theta_i+theta_(i+1) < pi+atan(9/20) < 8pi/7.     (8)
```

The lift in (8) is the sum of the one-step lifts because that sum is in
`(0,2pi)`. The final inequality follows, for example, from

```text
tan(pi/7)>tan(3/7)>3/7+(3/7)^3/3
         =156/343>9/20.
```

Here `tan(t)>t+t^3/3` follows by differentiating and using `tan(t)>t`.
For a period-seven orbit the one-step lifts sum to `2pi m` for an integer
`m`. Summing (8) gives

```text
21pi/4 < 4pi m < 8pi,
```

which contains no multiple of `4pi`. Thus the orbit is uniform.
The frame-turn condition now gives `7(2asin(s))=2pi`, hence
`asin(s)=pi/7`, as claimed.

## 6. Arithmetic and reproducibility

Build and run with a C++17 compiler supporting `__int128`:

```sh
g++ -O3 -std=c++17 research/ten/check_seven_ring_action.cpp -o /tmp/check_seven_ring_action
/tmp/check_seven_ring_action
```

All interval endpoints are multiples of `2^-36`. They are stored exactly
as IEEE binary64 numbers with absolute value below `2^16`; their grid
indices therefore have absolute value below `2^52`. Products and divisions
use signed 128-bit integer floor and ceiling. A square-root guess is
adjusted by exact integer comparisons until it is the integer square root,
then rounded outward. The initial endpoints are rational enclosures, and
subdivision uses an integer grid midpoint shared by both children.
Overflow, a denominator containing zero, a reversed interval, or an
unresolved expression causes further subdivision, never acceptance.
The program exits unsuccessfully if any cell remains unresolved or the
node budget is reached.

The optional interval tightening is the ordinary mean-value bound on a
closed box where all radicals and denominators in (1) are strictly
positive. It uses exact algebraic derivatives, not numerical differences.
To state them compactly, let `F=sqrt(1-q^2)` and `b=e c-d y=sin(beta)`.
Then

```text
F_x = -y q c^2/(F C^3),
F_y = (q/F)[Ry-1+k c b d/(R C^3)+c y/C^2-k^2 y/(R C^2)].
```

For the radius derivative use successive exact differentiation:

```text
k_R=(R-c-xH)/k,
C_R=[k_R(R-c)+k+xy-2(R-c)C]/D2,
K_R=K(k_R/k-C_R/C),
q_R=[R-y(Ry-1)-K K_R-q]/R,
F_R=-q q_R/F.
```

The current corrected run reports:

```text
RESULT nodes 1631795 pass 618545 elim 197353 todo 0 deep 0 maxdepth 29
```

An [independent full mathematical and implementation review](SEVEN_RING_ACTION_AUDIT.md)
passed. A separate
UndefinedBehaviorSanitizer build replayed the complete cover with the same
counts and no sanitizer errors. The audited verifier SHA-256 is
`420d2dc56932b9f5b61d3c0b4d6d1ac5f6121178461fd000845e7c7c8eacf5f1`.

This finite computation is the sole computer-assisted step of the theorem.
It has not been translated into Lean. Replacing the finite cone lemma by
short hand inequalities, and removing the contact-ownership assumption,
are separate remaining tasks.
