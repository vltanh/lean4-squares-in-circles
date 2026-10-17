# A state potential may use a consistent square-frame lift

A square's frame is defined modulo a quarter-turn. The sorted relative
centre angle is therefore usually placed in a half-open interval such
as \([-\pi/4,\pi/4)\). A proof may instead work in the larger closed
space of frame lifts and retain both representatives at its boundary.
It may also retain both signed representatives when the sorted
transverse coordinate is zero.

No equality of potential values on these duplicate representatives is
needed for a cyclic inequality. For each physical square in a ring,
choose one representative once and use it in both incident edges. If
the chosen lifted states are \(s_0,\ldots,s_6\), then for **any**
real-valued potential on the lifted state space,

\[
 \sum_{i=0}^{6}\bigl(\psi(s_{i+1})-\psi(s_i)\bigr)=0,
 \qquad s_7=s_0.
\]

The true frame differences change by multiples of \(\pi/2\) when
the lift is changed, but the square width function is quarter-periodic
and the true separating-axis system is merely relabelled. Thus a pair
inequality verified on **all** lifted signed states implies the desired
cyclic inequality for every physical ring, regardless of which one-time
lift choices are used.

For an affine geometric label, define on the signed lifted state

\[
 \psi(a,b,\sigma)=\sigma\arctan(b/a)
                 -\sigma\ell(a,b),\qquad \sigma\in\{-1,1\}.
\]

This potential is odd under reflection of the lifted frame. It need not
vanish at \(b=a\), or even at \(b=0\) if both signed zero lifts are
retained and all their pair cases are checked. Consequently a simpler
core label such as \(\ell_C(a,b)=q_C b\) is admissible even though
the resulting two diagonal-lift potential values differ.

This observation is a change of the auxiliary proof function, not a
claim that a new fitted function satisfies its required pair bounds.
Every bound for the chosen new function must still be proved on the
complete lifted domain. In particular, a dataset containing just one
zero-sign representative cannot by itself support the expanded-domain
claim; both limiting signs must be covered.
