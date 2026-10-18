# Exact rational cap-envelope counterexample at h=3/10

**Status: exact true-unit-square counterexample**, *not* an eight-square
packing or contradiction to the proved h>=1/3 cap envelope.

This strengthens the earlier diagonal-square witness at h=293/1000.
The axis-aligned **one-square** cap envelope
\[
R^2\ge(1+h)^2+(|p_y|+1/2)^2
\]
is **false already at offset h=3/10**, even when
\(R^2\le9789/2500\).

## Genuine rational square and actual true vertices

Set
\[
h=3/10,\quad y=99/100,\qquad
c=8319/11681,\quad s=8200/11681.
\]
The exact Pythagorean identity
\[
8319^2+8200^2=11681^2
\]
shows that
\[
e=(c,s),\quad f=(-s,c)
\]
is a genuine orthonormal unit-square frame.

Take center
\[
p=(h+(c+s)/2,y)
=\left(\frac{58819}{58405},\frac{99}{100}\right).
\]
The four **actual** vertices are
\(p+(i e+j f)/2\) for \(i,j=\pm1\).
Their minimum x coordinate is exactly h,
so the entire square is contained in \(x\ge h\).

Exact fraction arithmetic over **all four true vertices**
gives its maximum squared disk radius:
\[
\max_{v\in S}|v|^2
=\frac{5332904348861}{1364457610000}
\quad(<9789/2500).
\]
The actual disk-containment reserve is
\[
q_+-\max|v|^2
=\frac{1953173771}{272891522000}>0.
\]

However the desired aligned-square envelope at the
same cap offset and actual center y would be
\[
(1+h)^2+(y+1/2)^2
=\frac{39101}{10000},
\]
which is **strictly greater** than the actual
maximum squared vertex norm by
\[
\frac{1130676}{682228805}>0.
\]
Thus the proposed unrestricted envelope fails
even at \(h=3/10>7/24\), with **rational**
centers and frame and strict circle slack.

Every identity is independently replayed in
[verify_rotated_cap_envelope_three_tenths_counterexample.py](verify_rotated_cap_envelope_three_tenths_counterexample.py).
This is an exact construction, not an optimizer residual.

## Implication for computer-to-hand strategy

The now proved
[HUMAN_CAP_ENVELOPE_ONE_THIRD.md](HUMAN_CAP_ENVELOPE_ONE_THIRD.md)
remains completely valid for \(h\ge1/3\).
The counterexample here shows that its
**same one-square inequality cannot be used**
at \(h=3/10\). Hence trying to finish
the remaining S2/k4 same-sign interval
\(7/24<h<1/3\) by simply repeating the
*one-square* envelope is not enough.

The center p here is **outer** (norm >1);
the example has only one square, so it does
**not** disprove a sharper *two-square mixed
inner/outer* cap theorem. That conjecture
must be attacked through genuine two-square
SAT separators and the inner radial constraint.

No global sharp eight-square lower bound,
equality classification or Lean formalization
is claimed by this counterexample.
