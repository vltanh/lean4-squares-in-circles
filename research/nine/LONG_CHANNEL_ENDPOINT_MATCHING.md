# Long normal channels have distinct endpoints forming a matching

**Status: complete hand global geometric and channel theorem; root and
separate independent full audits passed.** Put \(Q=1105/256\).
The geometric theorem below needs only that the actual unit squares
are interior-disjoint and contained in the concentric disk \(D_{\sqrt Q}\).
No lower-radius, boundary-circle, positive-load or contact-owner premise
is used for that theorem.

## 1. A unit center cannot have two different centers at distance at least three

**Theorem 1.1.** If X,Y,Z are three distinct units in such a packing,
the two inequalities
\[
                       |c_X-c_Y|\ge3,\qquad |c_Z-c_Y|\ge3
\tag{1}
\]
cannot both hold.

Every unit center obeys
\[
                          |c|<M:=91/60,
\tag{2}
\]
because its farthest-corner squared norm is at least
\(|c|^2+|c|+1/2\), whereas
\[
                 M^2+M+\tfrac12=\frac{15541}{3600}
                        =Q+\frac{31}{57600}>Q.
\tag{3}
\]
Rotate so \(c_Y=(r,0)\). Equation(1) and (2) give
\(r>3-M>0\). Write \(c_X=(x,y)\). From its squared distance
to \(c_Y\),
\[
                 x<\frac{M^2+r^2-9}{2r}.
\tag{4}
\]
The function on the right is strictly increasing for \(r>0\):
its derivative is
\[
                         \frac12+\frac{9-M^2}{2r^2}>0.
\]
Using \(r<M\), equation(4) consequently gives
\[
               x<M-\frac9{2M}
                    =-\frac{7919}{5460}<-\frac{29}{20}.
\tag{5}
\]
The last comparison has exact strict margin \(1/2730\).
The same bound holds for the first coordinate of \(c_Z\).

Put \(a=29/20\). Every point p satisfying \(|p|<M\) and
\(p_x<-a\) belongs to the open disk centered at \((-a,0)\)
of squared radius
\[
             M^2-a^2=\frac{89}{450}.
\tag{6}
\]
Indeed
\[
 |p+(a,0)|^2=|p|^2+2ap_x+a^2<M^2-a^2.
\]
Both \(c_X,c_Z\) lie in this disk, so
\[
                       |c_X-c_Z|^2<4\frac{89}{450}
                                    =\frac{178}{225}<1.
\tag{7}
\]
Every unit contains its open radius1/2 center disk. Distinct
interior-disjoint units therefore have center distance at least1,
contradicting (7). This proves Theorem1.1.

Equivalently, the simple graph joining actual unit centers whose
distance is at least3 is a matching. The statement applies to all
physical units, including units with no positive force or load.

## 2. The full positive normal-channel consequence

Consider a positive path whose internal bodies are unloaded exact
positive-degree-two transmitters. The full transmission theorem gives
one unit direction n, true endpoint support applications, and reserve
L equal to the sum of the internal widths. If there are at least two
internal bodies, \(L\ge2\), and
\[
                    n\cdot(c_B-c_A)
                       =L+H_A(n)+H_B(n)\ge3.
\tag{8}
\]
Every actual side mean is retained in this equality.

**Theorem 2.1.** A body cannot be the endpoint of two such channels
to two distinct other endpoint bodies, when each channel has at least
two internal transmitters.

Otherwise the two endpoint-center distances in (8) violate
Theorem1.1. The endpoint bodies may carry any loads, have arbitrary
degrees or further positive forces, and need not touch the circle.
Only the internal transmitters require their stated exact degree
and zero load. No other force is deleted to manufacture a channel.

The conclusion is about distinct endpoint pairs. It does not forbid
two different long channels between the same two endpoint bodies.
The previously quantified two-loaded six-cycle has precisely that
parallel-pair structure, and is not excluded by this theorem.

## 3. Complete three-load simple-cycle consequences

Suppose the entire positive component is a simple cycle with
exactly three loaded bodies. Its three maximal unloaded runs connect
three distinct endpoint pairs in the contracted triangle. Each run
has at most two bodies, and a two-body run consists of two side-normal
transmitters: otherwise its center projection already exceeds the
diameter bound in (2). These are the full channel reserve bounds of
PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md, Section2.

Two runs of length2 would share one of the three loaded endpoints
and lead to two distinct other loads. Theorem2.1 excludes that.
Therefore the total number of unloaded bodies is at most
\[
                                2+1+1=4.
\tag{9}
\]
The entire component has at most seven bodies.

**Corollary 3.1.** Every simple positive component with at least eight
bodies and exactly three positive circle-loaded bodies is excluded,
with all remaining physical squares retained. This conclusion does
not require proper loaded concurrences or a circle-neighbor premise
at the three loads.

For exactly seven bodies, the full remaining three-load run pattern
is \((2,1,1)\), or cyclic edge gaps \((3,2,2)\). For exactly six bodies
the possible patterns are \((1,1,1)\) and \((2,1,0)\). The latter
whole orbit is separately excluded by
SIX_CYCLE_THREE_LOAD_LONG_CHANNEL_EXCLUSION.md; the alternating
six-body and the seven-body patterns are not excluded here.

More generally, with at least three loaded bodies, the length-two
unloaded runs of a simple cycle form a matching on its contracted
loaded cycle. In particular at most \(\lfloor k/2\rfloor\) such
runs occur for k loads. This is an exact combinatorial consequence
of actual center geometry, not a replacement of the physical
transmitters by fictitious contacts.

## 4. Scope

No normal convention is needed for Theorem1.1. The channel consequences
use the existing full force/torque transmission theorem and retain
all physical circle masks, actual shared means and arbitrary endpoint
equilibria. Additional positive forces at a supposed internal
transmitter invalidate that channel hypothesis and may not be omitted.

No coarse six-body row is declared closed. The theorem supplies a
uniform long-channel obstruction in every component and the full
simple-cycle load-family exclusions stated in Section3. No numerical
search, Lean compilation or CI is a premise.

