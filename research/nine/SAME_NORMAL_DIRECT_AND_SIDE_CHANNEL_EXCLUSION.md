# A direct contact and a width-one channel cannot leave a root in the same normal direction

Date: October 26, 2026.

**Status: complete radius-free local geometric proof and full C5
parallel-root consequence, accepted after independent root review.**
See REVIEW_SAME_NORMAL_AND_S_C5_DIRECTION_ROOT_2026_10_26.md.
No force at an endpoint is deleted or given a smaller degree.

## 1. Complete local theorem

Let A,B,C be three distinct actual unit squares in an interior-disjoint
physical packing with the existing selected strict point-normal convention.
Suppose:

* A--B is an actual positive contact with outward A normal n and
  original application p.
* A--U--C is an actual width-one normal channel, with the SAME
  outward A normal n and original A application q. Thus U is a
  true unloaded degree-two side transmitter and the original C
  application is \(q+n\).
* B and C are also joined by a real normal channel of reserve
  \(w\ge1\), all of whose internal bodies are true unloaded
  degree-two transmitters.

All three endpoint degrees, circle loads, other forces and actual
support means are unrestricted. The two channel interiors remain
occupied by their original physical squares.

**Theorem.** These hypotheses are impossible.

The same-normal premise is an equality of the original normals. No
new normal is selected to make the theorem apply.

## 2. One inward unit segment forces every inequality to be equality

Both p and q belong to the same supporting face of A in direction n.
A unit-square support face is a single vertex or a unit side; hence

\[
                              |q-p|\le1.
\tag{1}
\]

The point p minimizes n on B. The full inward unit-segment lemma,
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md, Lemma 3.1, gives

\[
                               p+n\in B.
\tag{2}
\]

This lemma retains every side mean: in own coordinates every nonzero
normal component starts at its corresponding supporting endpoint and
moves inward by at most one; a zero component does not move.

The real other channel from B to C gives a separating projection
gap w, so every B-to-C displacement has norm at least w. But the
actual point \(q+n\in C\) and (2) give

\[
 1\le w\le\operatorname{dist}(B,C)
       \le |(q+n)-(p+n)|=|q-p|\le1.
\tag{3}
\]

Indeed the normal channel itself attains its reserve w as a
point-to-point displacement, so its endpoint distance is exactly w.
Every quantity in (3) is therefore one. In particular p,q are
opposite endpoints of one side of A, n is an A side axis, and

\[
                         t:=q-p,\qquad |t|=1,\quad t\perp n.
\tag{4}
\]

The vector t is a shortest vector from B to C. Their actual normal
channel gives another shortest vector. The convex difference C-B
has a unique shortest vector, since the midpoint of two distinct
equal-norm minimizers has smaller squared norm. Thus their actual
channel direction is t, and

\[
  B\subseteq\{x:t\cdot x\le t\cdot(p+n)\}
            =\{x:t\cdot x\le t\cdot p\}.
\tag{5}
\]

## 3. The forced equality violates the existing strict point convention

The chosen endpoint p of A's support side is its minimum-t support,
whereas (5) makes p a maximum-t support of B. The actual A--B
contact also separates them along n. Consequently their entire
physical intersection is the single point p:

    n dot x = n dot p and t dot x = t dot p.

It is a vertex of A by (4). It is also a vertex of B, since it
simultaneously minimizes n and maximizes the independent direction t.
Its original selected A--B normal n is an A side axis, contrary to
the strict common-normal convention at a singleton vertex/vertex
contact.

This contradiction includes every equality in (1)--(3), all actual
shared means and their endpoints, and every orientation of B and C.
It does not presume that the original A--B interface was a singleton:
the equality argument first proves that physical fact.

## 4. The entire parallel-root C5 load13 S-leaf domain

Take the exact C5-plus-leaf component

    A--B--V--C--U--A, with genuine S leaf L at A,

with block loads exactly B,C and true unloaded degree-two U,V.
Keep all original nine physical squares and the full radius window.
The genuine leaf gives \(h_A(e)=d\), with L the actual radial S
unit beyond this support in the leaf direction e.

The A--U--C reserve is one. To check this without changing a force,
the genuine-leaf root meets the disk of radius
\(\epsilon=\max(d-1,0)\), so its support h in any channel direction
is at least \(-\epsilon\). The sharp contained-unit center bound
at C gives \(h+w_U\le d\). Thus

\[
 w_U\le d+\epsilon
       \le \max(d,2d-1)<31/30<\sqrt2.
\tag{6}
\]

The actual one-transmitter possibilities are \(1,\sqrt2\), so
\(w_U=1\). The other real channel B--V--C has reserve at least one.

Suppose the two actual root cycle forces were parallel. Their sum
balances the genuine positive leaf force, so their common line is
parallel to e. Neither actual normal can point along \(+e\):
any distinct unit beyond the support \(e\cdot x=d\) would, by
the complete sharp support equality theorem in
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1, have to be
the unique radial S unit L itself. In particular the root-channel
transmitter U cannot be another such unit, and B cannot be L.

Both actual root cycle normals therefore equal \(-e\).
The local theorem applies directly, using the unchanged direct
A--B contact, the real side channel A--U--C and the other actual
normal channel B--V--C. This excludes the complete parallel-root
S-leaf alternative, with arbitrary aligned or tilted root frame.

There is no need to assign a concurrence at a parallel root, to fix
a side mean, or to discard any original positive force. The leaf
retains both equal original circle weights, and the B/C physical
masks and all their individual weight endpoints remain arbitrary.

The nonparallel S-leaf part of M6.B5L.C5.L13.S remains open.
The separate whole D-leaf exclusion is in
D_LEAF_C5_TWO_SEPARATED_LOADS_EXCLUSION.md. This source introduces
no new roadmap gate or numerical certificate and ticks no shared
ledger entry. No Lean compilation or CI is used.
