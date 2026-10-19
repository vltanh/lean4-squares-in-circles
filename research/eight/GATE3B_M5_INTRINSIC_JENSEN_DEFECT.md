# Intrinsic M5 Jensen defect: no dependence on the maximizing anchor

**2026-10-13. Complete analytic normalization for M5-DIFFUSE; not an exclusion of the diffuse gate.** Let square orientations be `theta_i mod T`, with `T=pi/2`, `h=T/2=pi/4`. The M5 condition is that a CLOSED clockwise window of width h contains at most five of the eight frames.

Put

```
W = sum_(i<j) (1+|cos(theta_i-theta_j)|+|sin(theta_i-theta_j)|)/2,
W0=(41+15sqrt(2))/2,       c=(sqrt(2)-1)/2.
```

## 1. The balanced-window proportion is an intrinsic invariant

For any orientation start `alpha` let `N(alpha)` count the orientations in the HALF-OPEN arc `[alpha,alpha+h)` modulo `T`. Away from the finitely many interval endpoints,

```
N(alpha+h)=8-N(alpha).
```

Therefore `F(alpha)=1_{N(alpha)=4}` is h-periodic almost everywhere. Define

```
A = (1/h) integral_(alpha0)^(alpha0+h) F(alpha) d alpha.
```

This lies in [0,1] and does not depend on the starting direction `alpha0`. It is invariant under common rotations, relabeling, and reflection (which reverses the orientation circle).

### Theorem: A is exactly the odd folded simplex mass

Choose ANY maximizing M5 anchor, rotate it to zero, and use its sorted folded chart

```
0=x0<=x1<=...<=x7<=h,
lambda_k=(x_k-x_(k-1))/h, k=1..7,
lambda_8=(h-x7)/h.
```

Then

```
A=lambda_1+lambda_3+lambda_5+lambda_7.                (A)
```

Proof for generic distinct frames: the window contains five frames at the anchor. On moving its starting point to the right, its first event removes the anchor, making occupancy four. Among the eight folded events, L removes a frame and H adds one. M5 forces the count to stay between three and five. After every odd event the count is exactly four; after an even event it is three or five. Therefore occupancy is four precisely on intervals `(x0,x1),(x2,x3),(x4,x5),(x6,x7)`. Their total length divided by h is the right side of (A).

For tied frames, the M5 property is equivalent to the strict eight cyclic six-frame span inequalities `theta_(i+5)-theta_i>h`, so it persists under sufficiently small orientation perturbations. Generic perturbations avoid ties, and both the folded gaps and the length of the balanced-window set vary continuously (changes occur only near finitely many frame event endpoints). Pass to the limit. No actual square packing is perturbed. QED.

## 2. The folded pair variance is also intrinsic

Reduce the eight orientations modulo h, producing points on a circle of circumference h. For each unordered pair choose either directed circular arc length `d_ij` between its folded points. Define

```
V=sum_(i<j) d_ij*(h-d_ij).
```

Since the product is unchanged on replacing d by h-d, this is independent of the chosen directed arc, frame ordering, and position of the coordinate cut. In ANY sorted folded M5 chart it is

```
V=sum_(i<j) (x_j-x_i)*(h-x_j+x_i).
```

Thus V is invariant under maximizing-anchor changes, global rotations, reflections, and relabeling, including ties.

## 3. Intrinsic Jensen defect and proof frontier

Define

```
J=W-W0-c*A.
```

By the two theorems, J is a genuine physical orientation invariant, not a chart-dependent quantity. The previously proved pairwise strong concavity gives, in any folded chart,

```
V/4 <= J <= (sqrt(2)/4)*V.
```

At an even folded two-phase vertex (3+5 reference) the limiting values are `(W-W0,A)=(0,0)`; at an odd vertex (4+4 reference) they are `(c,1)`. In BOTH cases J=0. Subtracting c*A is essential: the raw surplus `W-W0` alone does not measure proximity to 4+4 vertices.

Consequently **the current open M5-DIFFUSE condition `J>3/1000` is unambiguous under every legitimate maximizing-anchor normalization**, with necessary intrinsic `V>3sqrt(2)/500`. A packing cannot evade or acquire this designation merely by reanchoring its frames.

The previously verified exact 3+5 and 4+4 certificates exclude `J<=3/1000` at the research squared-radius ceiling. The full `J>3/1000` continuous geometry, M5, M6--M8, unrestricted `R_8>=R_*` and equality remain OPEN. No Lean/CI or global sharpness is claimed.
