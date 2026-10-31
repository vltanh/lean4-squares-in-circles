# A uniform left-section bound for positively tilted units above unequal floors

**Date:** October 30, 2026 UTC.
**Status:** complete proposed one-square family lemma, awaiting independent
full review. The negative-tilt left-edge family is a separate obligation.

Put `Q=1105/256`, `R=sqrt(Q)`, `z=5/4`, and

    g(Y)=sqrt(Q-Y^2), 0<=Y<=R.

Let an actual closed unit square S be contained in the disk `D_Q` and
in the halfplane `y>=f`, where `3/8<=f<=1/2`. Suppose its axes can
be written as

    u=(a,b), v=(-b,a), a>=b>0, a^2+b^2=1.

Write its center as `(x,y)`, and define

    h=(a+b)/2, t=(a-b)/2, w=a+b, delta=z-y,
    k=z-f, C_f=g(f+1), K_f=(f+1)/C_f.

**Theorem.** The actual section of S at height `y=z` is nondegenerate,
and its left endpoint ell satisfies the strict uniform inequality

    ell<C_f-1.                                         (1)

The entire square and its original orientation are retained. The proof
uses the actual top vertex; no pose grid, selected contact, or common
frame with any other square is assumed.

## 1. Section and elementary constants

The top and bottom heights of S are `y+h` and `y-h`, respectively.
The top height is at least `f+w>=11/8>z`. The bottom height is at
most `R-w<=R-1<9/8<z`, since `R<17/8`. Thus the line at z
lies strictly between the square's horizontal supporting lines.

Solving the two relevant side inequalities gives

    ell=max(ell_1,ell_2),
    ell_1=x-(1/2+b*delta)/a,
    ell_2=x+(a*delta-1/2)/b.                            (2)

The actual top vertex is

    P=(x+t,y+h), P_y>=f+w.

All radical arguments below are therefore in the allowed disk range.
We have `3/4<=k<=7/8`. Also `K_f>3/4`: the ratio increases with
f, and at `f=3/8` its square is `484/621>9/16`.

Concavity of g at `f+1` gives

    g(f+w)<=C_f-K_f*(w-1).                             (3)

## 2. The first left edge

The actual top vertex gives the identity

    a*ell_1=a*P_x+b*P_y-1-b*z.

The function `a*g(Y)+b*Y` decreases once `Y>R*b`.
Its entire permitted height interval is on that side, because

    f+w-R*b=f+a-(R-1)*b
              >=f+(2-R)*b>1/4>0.

Consequently the disk and floor constraints, followed by (3), give

    a*ell_1<=a*C_f-a*K_f*(w-1)+b*(w-k)-1.             (4)

The elementary strict inequality

    b*(w-3/4)<1-a+(3/4)*a*(w-1)                      (5)

holds for every `a>=b>0` on the unit circle. Indeed, if E is its
right side minus its left side, then

    4E=b*(3-a)-7*a*(1-a)
       =b/(1+a)*(3+2a-a^2-7*a*b)>0.

Here `a>=1/sqrt(2)>1/2` gives `2a-a^2>=3/4`, while
`ab<=1/2`; the last bracket is at least `1/4`.
Because `k>=3/4` and `K_f>3/4`, (5) is stronger than
the inequality needed in (4). Hence `ell_1<C_f-1`.

## 3. The active second edge

The condition `ell_2>=ell_1` is equivalent to `delta>=t`.
Together with `y>=f+h`, this implies

    a=h+t<=z-f=k<=7/8.                                (6)

At the actual top vertex,

    b*ell_2=b*P_x-a*P_y+a*z.

Since `b*g(Y)-a*Y` is strictly decreasing for positive Y,

    ell_2<=g(f+w)-(a/b)*(w-k).

It is enough to prove

    F(f,a):=g(f+1)-g(f+w)+(a/b)*(w-k)>1.               (7)

### 3.1 The smallest floor is the only extremal floor

For fixed a, with `b=sqrt(1-a^2)` and w fixed,

    partial_f F=-(f+1)/g(f+1)+(f+w)/g(f+w)+a/b>0.

The first two terms have positive sum because `w>1` and
`Y/g(Y)` is increasing. This derivative applies in the interior
of the radical domain and extends the comparison to its closed upper
endpoint by continuity. Lowering f to `3/8` preserves the radical
domain and the active-edge bound `a<=7/8`. Thus

    F(f,a)>=F(3/8,a), 1/sqrt(2)<=a<=7/8.               (8)

### 3.2 At the smallest floor, the diagonal is the only extremal tilt

Put `C_0=g(11/8)` and

    D(w)=C_0-g(3/8+w),
    F_0(a)=D(a+b)+(a/b)*(a+b-7/8).

Throughout this interval,

    D'(w)=(3/8+w)/g(3/8+w)<2.                         (9)

For an explicit exact check, `3/8+w<=3/8+sqrt(2)<9/5`, and

    5*(9/5)^2<4Q,
    4Q-5*(9/5)^2=341/320>0.

Squaring positive quantities proves (9). Differentiating with
`b'=-a/b`, `w'=1-a/b`, and `(a/b)'=1/b^3` gives

    b^3*F_0'(a)
      =w-7/8-b^2*(a-b)*D'(w)-a*b*(a-b)
      >=a^3+3*b^3-7/8.                               (10)

The inequality uses (9), `a-b>=0`, and the exact identity obtained
by replacing D' with 2. The function `a^3+3b^3` decreases on
`[1/sqrt(2),7/8]`: its derivative is `3a(a-3b)<0`, since
`a<=7/8` and `b>=sqrt(15)/8`.

At its right endpoint,

    a^3+3b^3=(343+45*sqrt(15))/512
             >239/256=7/8+15/256.

Therefore `F_0'(a)>0` everywhere on the complete interval. Its
minimum is at `a=b=1/sqrt(2)`.

### 3.3 An exact strict reserve at the final endpoint

At this diagonal endpoint,

    F_0(1/sqrt(2))
      =sqrt(621)/16-g(3/8+sqrt(2))+sqrt(2)-7/8.

The following strict rational bounds suffice:

    sqrt(621)/16>31/20,
    g(3/8+sqrt(2))<17/16,
    sqrt(2)>7/5.

The first square reserve is `149/6400`. For the second, the
inequality `sqrt(2)>7/5>67/48` implies
`(3/8+sqrt(2))^2>51/16=Q-(17/16)^2`.
It follows that

    F_0(1/sqrt(2))
       >31/20-17/16+7/5-7/8=81/80>1.                 (11)

Equations (8)--(11) prove (7) over the full active second-edge
domain, with a uniform reserve. Hence `ell_2<C_f-1` whenever
the second edge is active. If it is inactive, Section 2 already
controls the actual left endpoint. This proves (1).

## 4. Source and verification boundary

The section coordinates and first-edge algebra specialize the method
of Sections 2--3 of `UNRESTRICTED_THREE_SQUARE_CAP.md`, SHA256
`b1359fcb446d93a534dc19dc7582edc5e8067300109810369621e47989ecf77b`.
They are fully reconstructed here. The new active-second-edge argument
retains the factor a/b and proves monotonicity in both the floor and
the entire allowed tilt interval. It requires no additional right-vertex
constraint or finite orientation partition.

This source proves the positive-tilt **left**-section family. Reflection
immediately gives the negative-tilt right-section family, but the opposite
left-edge family must still be proved before asserting a complete
orientation-uniform section theorem. No sharp seven- or nine-square
closure is claimed here.

All calculations are exact. This manuscript changes no earlier frozen
source, original ledger, proof gate, certificate, Lean file or CI state,
and performs no numerical packing or remote publication.
