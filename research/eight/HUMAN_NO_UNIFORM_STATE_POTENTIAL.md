# No universal 2*pi/7 gap from a single outer-square state potential

## Theorem (exact negative result at the eight-square search ceiling)

Let `q_plus=9789/2500`. A square whose center norm is at least
one has a rotation-invariant *single-square state* given by its
center radius `r` and its frame angle `alpha` relative to
its center ray (modulo quarter-turn symmetry).

There is **no function at all** `psi(r,alpha)` with the following
property for **every** pair of interior-disjoint unit squares
contained in `D_sqrt(q_plus)`, with both center norms at least
one and positive counterclockwise center-angle gap
`0<delta<pi`:

    delta + psi(state_target)-psi(state_source)
          >= 2*pi/7.                                   (1)

No continuity, differentiability, linearity, or bounded degree is
assumed of psi. The two exact counterexample pairs use the same
two states in opposite orders and have strictly interior,
unambiguous relative frame angles. The result does not rule
out multi-type budgets with a seven-step odd-cycle cost,
pair inequalities involving two or more neighboring squares,
or potentials with extra global information.

## 1. Two exact rotation-invariant square states

Put

    r_A=1271/1000,    c=120/169,    s=119/169,
    r_B=707/500,     delta=arccos(5/8).

The identity `c^2+s^2=1` follows from `120^2+119^2=169^2`.
Put `a=arctan(s/c)`. Because `0<s<c`, one has
`0<a<pi/4`, so the signed relative tilts are unique.

Define the two states:

    A: center norm r_A, relative frame alpha_A=-a,
    B: center norm r_B, relative frame alpha_B=0.

We construct two separate pairs, both fitting the specified disk:

* Pair AB: center directions `0,delta` and states `A,B`.
* Pair BA: center directions `0,delta` and states `B,A`.

The respective absolute frames are
`-a,delta` for AB and `0,delta-a` for BA.
Both center norms exceed one.

Each A-square's largest vertex squared norm equals

    q_A=r_A^2+1/2+r_A*(c+s)
        =661278529/169000000
        <9789/2500.

Each B-square's largest vertex squared norm equals

    q_B=r_B^2+1/2+r_B
        =978349/250000
        <9789/2500.

Both strict comparisons are immediate by cross multiplication.
Thus all four individual placements obey the search ceiling,
independently of their relative positions.

## 2. The two pair separations are strictly positive

Write

    cos(delta)=5/8,    sin(delta)=sqrt(39)/8.

The separating-axis theorem yields the following **exact**
positive margins, where a margin is the absolute center
projection on a chosen square axis minus the sum of both
squares' support half-widths on that axis:

    Pair AB: choose the first axis e_A of A.
    margin_AB=(24383*sqrt(39)-150870)/676000.          (2)

    Pair BA: choose the second axis f_A of A.
    margin_BA=(25090*sqrt(39)-154919)/676000.          (3)

For example, (2) follows from e_A=(c,-s),
center displacement
`(r_B*5/8-r_A,r_B*sqrt(39)/8)`,
and the relative frame angle `delta+a`.
That angle lies in `(pi/2,pi)`, so the absolute
cosine and sine signs in the exact support sum
are fixed. Expanding `c=120/169`, `s=119/169`
gives the numerator in (2).
For (3), use `f_A` at absolute angle `delta-a+pi/2`
for the target A-square, compared with the source B
frame at angle zero; the same rational dot-product
expansion gives (3).

Both numerators are strictly positive **without decimal
approximations**. Indeed `sqrt(39)>31/5`, since
`39>961/25`, and

    24383*(31/5)-150870=1523/5>0,
    25090*(31/5)-154919=639>0.

Therefore both AB and BA have strictly disjoint closed
squares, not just nonoverlapping open interiors.

## 3. Their identical angular gap is below 2*pi/7

The classical rational bound `pi>157/50` gives

    2*pi/7 > 157/175 =:v.

For `0<v<1`, the alternating Taylor inequality
`cos(v)<=1-v^2/2+v^4/24` holds. Direct rational
substitution yields

    5/8-[1-v^2/2+v^4/24]
      =4959337/11254687500>0.

Since cosine is strictly decreasing on `[0,pi]`
and `cos(delta)=5/8`, it follows that

    0<delta<v<2*pi/7.                                  (4)

This strict bound is proved with rational arithmetic
and an elementary entire-interval Taylor estimate.

## 4. No single-state potential can supply the gap

Apply hypothetical inequality (1) first to pair AB,
then to pair BA. Because their states are the same
two states in opposite orders, their potential
increments cancel exactly:

    [delta+psi(B)-psi(A)]
      +[delta+psi(A)-psi(B)]
       >= 4*pi/7.

Thus `2*delta>=4*pi/7`, or
`delta>=2*pi/7`, contradicting (4).
The contradiction does not depend on the values of
psi or any regularity assumption. This proves
the theorem.

## Interpretation

One cannot complete the seven-outer-cycle case
merely by choosing a clever continuous nonlinear
rotation-invariant label `psi` and demanding
a uniform directed `2*pi/7` gap of **every**
disjoint pair. The counterexample shows why an
odd-seven-step argument with weaker pairwise costs,
or a genuinely multi-square geometric invariant,
is necessary. A pairwise multi-type budget may
still succeed because its seven-word minimum
can exceed `2*pi` even when two-step mean costs
are smaller than `2*pi/7`.

This is a negative result about a proof shortcut.
Neither exact pair constitutes an eight-square
packing below the candidate, and the unrestricted
inequality `R8>=Rhat` remains open.
