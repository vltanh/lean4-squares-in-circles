# Quantitative fourth-harmonic Fourier bound from balanced M5 windows

**2026-10-13. Complete analytic orientation theorem, NOT a disk radius exclusion.** It improves the earlier bound `|sum exp(4i theta_i)|<=2` by incorporating the intrinsic fraction of windows containing exactly four frames. It applies to both M5 folded types, frame ties and all actual owner configurations.

Let the eight square orientations be `theta_i mod pi/2`, and assume **M5**, so no closed window of length `pi/4` contains six frames. Put

```
alpha_i=4theta_i mod 2pi,     S=sum_i exp(i alpha_i).
```

Let `N(phi)` count the alpha_i in the **centered** half-open semicircle `[phi-pi/2,phi+pi/2)` modulo `2pi`. This has the SAME balanced-window proportion A as the intrinsic start-window definition, because that proportion is independent of translating the window start. Away from the finitely many endpoints, `N(phi)` lies in {3,4,5} and `N(phi+pi)=8-N(phi)`.

The intrinsic Jensen theorem identifies

```
A=(1/pi)*measure{phi in [phi0,phi0+pi): N(phi)=4}
 =lambda_1+lambda_3+lambda_5+lambda_7
```

in **every** maximizing M5 folded chart, independent of `phi0`, relabeling, common rotation, and reflection. Necessarily `0<=A<=1`.

## Theorem: exact balanced-window Fourier envelope

```
|S| <= 2*cos(pi*A/2).                                   (F)
```

Consequently

```
sum_(i<j) sin²(2(theta_i-theta_j))
  >= 15+sin²(pi*A/2) >= 15+A².                         (M)
```

### Pen-and-paper proof

For any beta, integration of the semicircle indicators gives

```
integral_0^(2pi) N(phi)*cos(phi-beta) dphi
   = 2*Re(exp(-i beta)*S).
```

Subtracting four does not alter the integral. Write `H=N-4`, which takes values in {-1,0,1} almost everywhere. Its nonzero support `E` has total length `2pi(1-A)` by the complementary-window identity.

Put `a=pi*(1-A)/2` and `t=cos a`. The set `E*` on which `|cos(phi-beta)|>=t` has length `2pi(1-A)` and is the union of the equal arcs of angular half-width a centered at beta and beta+pi. Since `|cos|-t` is nonpositive outside E*,

```
integral_E (|cos|-t) <= integral_(E*) (|cos|-t).
```

The constant-t integrals cancel because `|E|=|E*|`. Evaluating the elementary cosine integrals yields

```
integral_E |cos(phi-beta)| dphi <=4*sin(a).
```

Therefore

```
2*Re(exp(-i beta)*S)=integral H(phi)cos(phi-beta)dphi
  <=integral_E |cos(phi-beta)|dphi<=4sin(a).
```

Choose beta in the complex direction of S to obtain `|S|<=2sin(a)=2cos(pi*A/2)`. Ties affect only measure-zero endpoints.

The exact identity

```
sum_(i<j)sin²(2(theta_i-theta_j))=(64-|S|²)/4
```

then proves the first part of (M). Concavity of sine on [0,pi/2] gives `sin(pi*A/2)>=A`, proving the second. QED.

## True SAT-width corollary

For the actual sum of all 28 pair support widths

```
w_ij=(1+|cos(theta_i-theta_j)|+|sin(theta_i-theta_j)|)/2,
W=sum_(i<j)w_ij,
c=(sqrt(2)-1)/2,     W0=28+15*c,
```

the proven pair inequality `w_ij-1>=c*sin²(2(theta_i-theta_j))` gives

```
W >= W0+c*sin²(pi*A/2),
J=W-W0-c*A >= c*(sin²(pi*A/2)-A).
```

The J inequality may have a nonpositive right side and **does not replace** the stronger Jensen coercivity `J>=V/4`. Its purpose is a globally anchor-invariant spectral restriction interpolating the limiting 3+5 (A=0, |S|=2) and 4+4 (A=1, |S|=0) two-frame cut data. Those limiting configurations need not themselves satisfy the closed-window M5 condition.

**Status:** a new full-domain orientation theorem, not a center/owner classification. M5-DIFFUSE at `J>3/1000`, the later M6--M8 branches, unrestricted `R_8>=R_*` and equality remain OPEN. No Lean or CI.
