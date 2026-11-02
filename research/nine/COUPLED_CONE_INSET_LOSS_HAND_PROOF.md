# A coupled cone gap forces a central whole floor

November 2, 2026. Complete scalar hand proof, with a four-row rational
Bernstein table and a separate exact arithmetic reconstruction. This is
an actual-four caller lemma; no Lean or CI is used.

Put

\[
 Q=1105/256,\quad l=29/60,\quad g_0=15/31,
 \quad \delta=331/20000,\quad J=23/150.
\]

Retain four original physical unit squares forming an actual horizontal
four-chain whose consecutive center comparisons are horizontal cone
comparisons. Retain every physical nonoverlap and closed-Q-disk corner
condition. For a unit of folded slope \(t\in[0,1]\), write

\[
 d=\sqrt{1+t^2},\quad a=1/d,\quad b=t/d,
 \quad h=(a+b)/2,\quad k=(a-b)/2,\quad g=1/(4h).
\]

## 1. The complete own-half-plane clearance

The actual-four inset bounds give

\[
 g_1,g_2>g_0,\qquad x_1+g_1>-\delta,
 \qquad x_2-g_2<\delta.
\]

For an original central square F above the left inner main, with
\(-l\le x_F\le0\), the physical inset clearance gives

\[
 y_F-h_F>y_1+g_0-r_F,
 \qquad r_F=\max\{0,t_F(k_F+\delta+x_F)\}.       \tag{1}
\]

This is the full own-half-plane formula proved in Sections 2--3 of
`CENTRAL_SINGLETON_FLOOR_HAND_TABLE_PROOF.md`. Both chiralities and all
separating axes are included. The steep facet is no weaker than the
displayed shallow facet; the horizontal axis cannot separate; and the
center-chord order excludes a reversed vertical facet. At \(t_F=0\)
the loss is zero. Thus (1) is not an assumed vertical projection edge.

## 2. A scalar bound retaining the unit's own inset

For every \(0\le t\le1\),

\[
 \boxed{\displaystyle
  t\left(B-\frac{t^2}{\sqrt{1+t^2}(1+t)}\right)_+
       <\frac1{32},\qquad B=\delta+J=\frac{10193}{60000}.}
                                                        \tag{2}
\]

Here the strict inequality at \(t=0\) is immediate. If
\(0<t\le t_0=1875/10193=1/(32B)\), omit the strictly positive
subtracted term. This gives a strict bound by \(Bt\le1/32\).

For \(t\ge t_0\), both sides of

\[
 (Bt-1/32)\sqrt{1+t^2}(1+t)<t^3
\]

are nonnegative. Squaring is therefore equivalent to positivity of

\[
 p(t)=t^6-(Bt-1/32)^2(1+t^2)(1+t)^2.              \tag{3}
\]

In increasing powers of t, the coefficients of \(3600000000p(t)\)
are exactly

\[
 (-3515625,\ 31192500,\ -34480999,\ -138378248,
   -134862623,\ -169570748,\ 3496102751).
\]

For an interval \([u,v]\), first substitute \(t=u+(v-u)s\)
and write the power coefficients as \(c_0,\ldots,c_6\). The degree-six
Bernstein coefficients are

\[
 \beta_i=\sum_{j=0}^{i}
             \frac{\binom{i}{j}}{\binom{6}{j}}c_j.
\]

The minimum of the seven exact coefficients is positive in every row:

| Interval | Minimum Bernstein coefficient of p |
| --- | --- |
| \([1875/10193,1/4]\) | \(20711767/589824000000\) |
| \([1/4,5/16]\) | \(195613010401/56623104000000000\) |
| \([5/16,1/2]\) | \(7923782519/268435456000000\) |
| \([1/2,1]\) | \(38487751/5120000000\) |

Because the Bernstein basis functions are nonnegative and sum to one,
this table proves \(p>0\) on the entire interval. It proves (2),
including every endpoint, with no sampling or optimization premise.

The relevant exact coupling identity is

\[
                   k-g=-\frac{t^2}{\sqrt{1+t^2}(1+t)}.       \tag{4}
\]

Consequently, if \(x_F+g_F\le J\), (1), (2), and (4) give
\(r_F<1/32\). The same conclusion follows from the stronger condition
\(x_F+g_F\le l-7/20=2/15<J\).

## 3. The original-square caller

**Theorem.** Let F be an original central square above the left inner
main, with \(x_F\le0\), and suppose

\[
                 x_F+g_F\le J,\qquad y_1\ge-7/20.
\]

Then its whole floor satisfies

\[
 y_F-h_F>-7/20+15/31-1/32
          =1/10+13/4960>1/10.                     \tag{5}
\]

All horizontal and vertical reflections of the theorem also hold.

Two useful ways the original cone constraints supply the first premise
are as follows.

* If \(F<_c R\), R is central, and F is the negative central member,
  then \(x_R-x_F\ge g_F+g_R\) gives
  \(x_F+g_F\le l-g_R<l-7/20=2/15<J\).
* If \(F<_c R\) and an original right-side R obeys the zero-side
  bound \(x_R-g_R<J\), then the same cone comparison gives
  \(x_F+g_F<J\). This also forces \(x_F<0\), since
  \(g_F\ge1/(2\sqrt2)>J\).

In both cases the coupling uses F's own inset halfwidth \(g_F\).
Replacing it by a constant before evaluating the loss discards the
useful identity (4).

## 4. Verification scope

`verify_coupled_cone_inset_loss.py` reconstructs (3), its integer
coefficients, all 28 Bernstein coefficients, the four displayed minima,
and the final floor reserve using exact rational arithmetic. Its report
is `coupled_cone_inset_loss_arithmetic_replay.json`. The scalar table and
the physical caller above constitute the proof; the checker is a
reproducible arithmetic audit of that finite table.
