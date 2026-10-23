# J — transition positivity from the geometric diagonal endpoint

Baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.
Targets in `Seven/BoundaryProfiles.lean`: `transitionF_pos` and
`diagonal_value_pos`. Prerequisite: the coarse circle/line geometry in
[L_COARSE_TRANSITION_PROOF.md](L_COARSE_TRANSITION_PROOF.md).
This is a human proof and integration recipe, not compiled Lean.

## 1. The original profile and why the old test point is unnecessary

Write `r=rd`, `q=r+1/2=sqrt(13/8)`, `b=a0-1/2=X0-1`, `Y0=u0+1/2`.
The side-labelled circular boundary has coordinates X(t),Y(t), and
`Z(t)=X(t)/3+3Y(t)/4`. Put

```math
\theta(t)=\pi/3-t+s_0,\qquad
F(t)=1-Y(t)-b\sin\theta(t)+Y_0\cos\theta(t).
```

We need F positive on `[2/5,td]`. The old proof uses a numerically selected
interior point 18/25. The new proof uses the actual diagonal endpoint td.
At that endpoint `X=Y=q`, `Z=13q/12`, so

```math
F(t_d)=1-q-b\sin\theta_d+Y_0\cos\theta_d,
\qquad
F'(t_d)=-\frac{12}{13}+b\cos\theta_d+Y_0\sin\theta_d.
```

The exact ratio 12/13 is a geometric simplification unavailable at an arbitrary
interior test point. A stronger uniform curvature bound makes this endpoint
sufficient even though F need not be monotone on the whole interval.

## 2. Improve the curvature to 5/8

The existing derivative identity gives

```math
F''(t)=\frac{39}{16Z(t)^3}
       +b\sin\theta(t)-Y_0\cos\theta(t).
```

On the circular segment Z is increasing, hence `Z(t)<=Z(td)=13q/12`.
Using `q^2=13/8` and `q<51/40`,

```math
\frac{39}{16Z(t)^3}\ge\frac{2592}{2197q}>\frac{37}{40}.
```

The coarse bounds in L imply `theta(t)>31/50` and `theta(t)<pi/2`:
its minimum is at td, and
`theta_d=pi/6-7/12+5rd/12+5u0/4 > 187/300 > 31/50`.
Taylor inequalities at 31/50 imply

```math
\sin\theta(t)>\frac{29}{50},\qquad
\cos\theta(t)<\frac{57}{70}.
```

For these two comparisons it suffices to use
`sin x >= x-x^3/6` and `cos x <= 1-x^2/2+x^4/24`.
Also `b>3/5` and `Y0<19/24`. Therefore

```math
F''(t)>\frac{37}{40}+\frac35\frac{29}{50}
                  -\frac{19}{24}\frac{57}{70}
       =\frac{8797}{14000}>\frac58.
```

Every bound is uniform on the whole interval. No near-minimum test is used.

## 3. Bound the endpoint by monotonic geometry, retaining correlations

The line identity `9a0+11u0=2pi+7` eliminates pi from the endpoint angle:

```math
\theta_d=\frac{9a_0+26u_0+5r-14}{12}.
```

For comparison, allow u and r to vary over the coarse rectangle

```math
\frac{29}{100}\le u\le\frac7{24},\qquad
\frac{17}{22}\le r\le\frac{31}{40},
```

but **retain the circle correlation**

```math
X=\sqrt{13/4-(u+1/2)^2},\quad a=X-1/2,\quad
Y=u+1/2,\quad b=X-1,
\quad\theta=(9a+26u+5r-14)/12.
```

Define

```math
U(u,r)=\frac12-r-b\sin\theta+Y\cos\theta,
\qquad V(u,r)=b\cos\theta+Y\sin\theta-\frac{12}{13}.
```

At the actual transition these equal `F(td)` and `F'(td)`.
This is an analytic enlargement for comparison, not an assumption that all
points of the rectangle are transition states.

Throughout the rectangle, elementary squared comparisons give

```math
\frac{67}{60}<a<\frac98,\quad
0<p:=Y/X<\frac12,\quad
\frac35<\theta<\frac23.
```

Put `k=b cos(theta)+Y sin(theta)` and
`h=-b sin(theta)+Y cos(theta)`. Using `cos(theta)>=7/9`,
`sin(theta)>=141/250`, `sin(theta)<=2/3`, we obtain

```math
k\ge\frac{37}{60}\frac79+\frac{79}{100}\frac{141}{250}
  =\frac{624503}{675000}>\frac{12}{13},
\qquad
h\ge\frac{79}{100}\frac79-\frac58\frac23=\frac{89}{450}>0.
```

The numerical fractions here are products of the displayed coarse geometric
bounds; they are not separately supplied certificates.
Since `a_u=-p` and `theta_u=(26-9p)/12>=43/24`,

```math
U_u=p\sin\theta+\cos\theta-\theta_u k<0,
\qquad U_r=-1-\frac5{12}k<0,
```

```math
V_u=-p\cos\theta+\sin\theta+\theta_u h>0,
\qquad V_r=\frac5{12}h>0.
```

For the first sign one can use `p sin(theta)+cos(theta)<=4/3` and
`theta_u k>(43/24)(9/10)>4/3`. For the third, `sin(theta)>1/2`,
`p cos(theta)<1/2`, and h is positive.
Thus U is minimized, and V maximized, at the upper corner
`u=7/24,r=31/40`. Moreover `V>0` throughout.

## 4. One small rational endpoint evaluation

At this corner `X=sqrt(1511)/24`. Use the tangent upper bound for the square
root at the nearby integer square 39 squared:

```math
\sqrt{1511}<39-\frac5{39},\qquad
X<\frac{379}{234},\qquad a<\bar a:=\frac{131}{117}.
```

This follows simply because `(39-5/39)^2=1511+25/1521`.
At fixed u,r, U decreases with a and V increases with a:
`U_a=-sin(theta)-3k/4<0`, `V_a=cos(theta)+3h/4>0`.
Replacing a by this upper bound is therefore safe in the desired directions.
The resulting angle is the derived rational

```math
\alpha=\frac{2351}{3744}=\frac58+\frac{11}{3744}.
```

There is no five-decimal enclosure of an unknown angle. Only this explicit
rational endpoint is evaluated. For clarity, define
`S5(x)=x-x^3/6+x^5/120`, `S7(x)=S5(x)-x^7/5040`.
On `[5/8,alpha]`, `4/5<cos x<13/16`: the lower bound follows from
`alpha<63/100` and `cos x>=1-x^2/2`; the upper from `cos(5/8)<=C4(5/8)`.
Integration and Taylor at 5/8 give

```math
\frac{37}{63}
 <S_7(\tfrac58)+\frac45\frac{11}{3744}
 \le\sin\alpha
 \le S_5(\tfrac58)+\frac{13}{16}\frac{11}{3744}
 <\frac{47}{80}.
```

The two outside inequalities are direct rational arithmetic in this single
line. From the unit-circle identity,

```math
\frac{123}{152}<\cos\alpha<\frac{17}{21},
```

because
`1-(47/80)^2-(123/152)^2=51/2310400>0` and
`(37/63)^2+(17/21)^2-1=1/3969>0`.
Consequently

```math
F(t_d)>
 -\frac{11}{40}-\frac{145}{234}\frac{47}{80}
                   +\frac{19}{24}\frac{123}{152}
 =\frac{59}{37440}>\frac1{640},
```

```math
0<F'(t_d)<
 \frac{145}{234}\frac{17}{21}+\frac{19}{24}\frac{47}{80}
 -\frac{12}{13}
 =\frac{68647}{1572480}<\frac7{160}.
```

These endpoint estimates are intentionally modest. Their role is explicit:
the value reserve must exceed the squared-slope correction in the next step.
They replace the long chains of separate approximations to J, X0, Y0, X, Y,
Z, a test angle, and a quotient at the old interior point.

## 5. Complete the tangent parabola at the diagonal endpoint

Apply the curvature bound from section 2 with anchor td:

```math
F(t)\ge F(t_d)+F'(t_d)(t-t_d)+\frac5{16}(t-t_d)^2
      \ge F(t_d)-\frac45 F'(t_d)^2.
```

Using section 4,

```math
F(t)>\frac1{640}-\frac45(\tfrac7{160})^2
     =\frac1{32000}>0.
```

This proves the original `transitionF_pos`, with a stated uniform reserve.
The interior `testLabel`, `testValue`, and `testSlope` are unnecessary.

## 6. The diagonal-value certificate disappears as well

The other angle in `diagonalValue` is `psi=td+s0-pi/6`. Since `td<pi/4`,

```math
0<\psi<\theta_d<\pi/2,
\qquad \theta_d-\psi=\pi/2-2t_d>0.
```

The function `H(v)=-b sin v+Y0 cos v` is strictly decreasing on this angle
interval. Therefore

```math
\mathrm{diagonalValue}=1-q+H(\psi)
 >1-q+H(\theta_d)=F(t_d)>\frac1{640}.
```

No Taylor evaluation or narrow interval around the diagonal angle is needed.
For the separate inward-circular caller needing `psi<5/8`, use L's geometric
domain proof, not the deleted five-decimal bracket.

## 7. Integration order and strictness

Suggested helper statements (implementation sketches, not existing results):

```lean
lemma transition_curvature_ge_five_eighths {t : ℝ}
    (ht : 2/5 ≤ t ∧ t ≤ td) :
    (5 : ℝ)/8 ≤ transitionFDD t := ...

lemma transition_diagonal_endpoint :
    (1 : ℝ)/640 < transitionF td ∧
    0 < transitionFD td ∧ transitionFD td < 7/160 := ...
```

Prove L's independent coarse geometry first. Then prove the comparison
rectangle's derivative signs, its rational corner estimates, and the stronger
curvature bound. Apply `Seven.curvature_tangent` at td and complete the square.
Finish `diagonal_value_pos` with the angle-order argument above. Existing
transition-diagonal monotonicity and the actual-state comparison consume the
same positive profile statements and need no redesign.

No old `test_point`, `transitionF_pos`, or `diagonal_value_pos` is used to prove
its own replacement. All endpoint and contact strictness is preserved.

## Validation boundary

The partial derivative identities, circle comparisons, Taylor inequalities,
and rational endpoint reserves are explicit in the proof. Exact symbolic and
rational checks are development cross-checks, not premises. This is a
completed mathematical replacement; Lean implementation, compilation and
kernel checking are not claimed.
