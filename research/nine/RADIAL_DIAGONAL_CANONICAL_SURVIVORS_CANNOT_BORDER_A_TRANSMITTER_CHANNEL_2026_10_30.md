# Two screened canonical endpoints exclude every nonempty transmitter channel

Date: October 30, 2026. Author: joint-pockets continuation.
Comparison tree: `4d2b3d62ce489b3251f0241d6c592e868fd7a410`.

**Status: complete proposed hand exclusion, awaiting independent review.**
This excludes every genuine nonempty unloaded full-degree-two channel
between two endpoints covered by the canonical rotation theorem. It
therefore excludes, simultaneously, the four-, five-, and six-loaded
short-seven-cycle subclasses in which all loaded vertices satisfy that
theorem's complete physical-contact test. Both transmission widths,
every channel length, actual application means, and all additional
physical squares are retained. The radius bound for the exclusion is
the larger exact range `R<=3/sqrt(2)`.

The hypothesis is conditional on the actual physical contacts. This is
not a closure of the unrestricted short-C7 remainder or an original
coarse parent. In particular, two-circle loaded bodies, side-owned
contacts at a moving endpoint, and additional physical contacts that
fail the complete test are not removed.

## 1. Endpoint hypotheses and the exact canonical survivor

Fix an original packing first minimizing R and then
`Phi=sum_i |c_i|^2`. Retain its full physical force-and-torque
certificate. Let A and B be two distinct actual loaded bodies. At
each endpoint assume the complete hypotheses of

`CANONICAL_ROTATION_OF_UNBLOCKED_UNIQUE_CIRCLE_TWO_FORCE_BODIES_2026_10_30.md`,
Theorem 4.1.

For clarity, each has exactly two positive body-pair forces,
nonparallel original force lines, one physical circle corner with
positive coefficient, and a proper concurrence `q=tau z` in the
actual square, `0<tau<=1`. Each original positive contact normal
uniquely exposes a vertex of the endpoint. Every additional actual
touching square, even one with zero pair coefficient, must have an
actual fixed separator exposing a unique vertex p of the endpoint
and satisfying `p-q=alpha n`, `alpha>=0`. At the two positive
neighbors the original normal and original application must be used.

The referenced theorem proves, with

\[
                \sigma=\frac1{\sqrt2},\qquad r=R-\sigma>0,
\]

that each endpoint has a unit radial direction e and a parameter
`0<delta<sigma`, with

\[
\begin{split}
 c&=r e,\qquad z=Re,\qquad q=(r+\delta)e,\\
 p_\pm&=r e\pm\sigma Je,\\
 n_\pm&=\frac{-\delta e\pm\sigma Je}
                    {\sqrt{\delta^2+\sigma^2}}.            \tag{1.1}
\end{split}
\]

Here `p_+,p_-` are its two actual original applications and
`n_+,n_-` their outward unit normals. Its two positive contact
magnitudes agree. The proof below does not require that their
common value agree with a value chosen independently at the other
endpoint; the actual channel already enforces that agreement.

The proper-concurrence hypothesis is supplied in the project's
radius window by `FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md`, Lemma 1.1,
at the stated true-degree-two and nonparallel scope. The extra
physical-contact test remains a separate hypothesis.

## 2. Equal-radius ports cannot start an inward channel of unit length

For either sign in (1.1), direct scalar products give

\[
 |p_\pm|^2=r^2+\sigma^2=:\rho^2,
 \qquad
 p_\pm\cdot n_\pm
   =g(\delta):=\frac{\sigma^2-r\delta}
                         {\sqrt{\delta^2+\sigma^2}}.       \tag{2.1}
\]

The value rho depends only on the common containing radius R,
not on the direction e, the endpoint, or delta. Consequently every
actual positive application at A and B lies on the same circle of
radius rho. This is a statement about their actual original ports,
not about replacement points or a virtual contact.

The function g is strictly decreasing on `[0,sigma]`, since

\[
  g'(\delta)
    =-\frac{\sigma^2(r+\delta)}
                  {(\delta^2+\sigma^2)^{3/2}}<0.           \tag{2.2}
\]

Using `0<delta<sigma` and `sqrt(2 sigma^2)=1` yields

\[
       p_\pm\cdot n_\pm>g(\sigma)
                    =1-\frac R{\sqrt2}.                   \tag{2.3}
\]

In particular, if

\[
                        \sigma<R\le\frac3{\sqrt2},        \tag{2.4}
\]

then every such outward port projection is strictly greater than
`-1/2`, including the upper endpoint `R=3/sqrt(2)`.

Suppose for a contradiction that two such actual ports satisfy

\[
                         p_B-p_A=L n,
                  \qquad L\ge1,                          \tag{2.5}
\]

where n is the original outward contact normal at A. Equality of
their squared norms in (2.1) implies

\[
          0=|p_A+Ln|^2-|p_A|^2=2L(p_A\cdot n)+L^2.
\]

Since `L>0`, this forces

\[
                            p_A\cdot n=-\frac L2
                                          \le-\frac12,    \tag{2.6}
\]

contradicting (2.3)--(2.4). Only the actual normal at A and the
common port radius are used in this final contradiction.

## 3. Every genuine nonempty transmitter channel has exactly (2.5)

Consider an original positive path

\[
                     A-U_1-\cdots-U_m-B,\qquad m\ge1,      \tag{3.1}
\]

where every internal `U_j` is unloaded and has full positive
body-pair degree exactly two. “Unloaded” means that all its circle
coefficients are zero; it may still have physical circle contacts.
No additional positive chord or branch at an internal vertex may
be deleted to obtain this premise. All applications below are the
genuine shared application points or actual aggregate means.

Orient the path from A to B. At an internal unloaded true-degree-two
body, force balance says that its incoming and outgoing directed
force vectors are the same nonzero vector. Hence every edge in
(3.1) has one common magnitude mu>0 and one common unit direction n.
The internal body's origin-moment equation is

\[
             \det(p_{\rm out}-p_{\rm in},\mu n)=0.
\]

Thus its outgoing and incoming applications have difference parallel
to n. They lie on its opposite supporting faces in directions n
and `-n`. Their projection difference is the full width of that
actual square in direction n. For any orthonormal square frame
u,v this width is

\[
                   w=|n\cdot u|+|n\cdot v|\ge1,            \tag{3.2}
\]

because the squares of these two nonnegative summands sum to one.
Consequently the exact point difference is `w n`, with `w>=1`.

The same actual application on each body pair is used at its two
ends. Summing all internal point differences therefore telescopes:

\[
           p_B-p_A=\left(\sum_{j=1}^{m}w_j\right)n
                          =L n,\qquad L\ge m\ge1.          \tag{3.3}
\]

The normal n is precisely the original outward normal at A on
the first edge; at B the outward normal is `-n`. Formula (3.3)
is (2.5), so Section 2 applies.

This rederives the needed part of the physical normal-channel
Lemma N.1 in `PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md`. The sharper
classification `w_j in {1,sqrt(2)}` is unnecessary here. Thus no
width pattern, shared-side height, or channel length needs a separate
case argument. Additional zero-weight contacts along the internal
channel do not alter its force and torque equations; those actual
bodies are never moved or removed.

**Theorem 3.1 (uniform channel exclusion).** Under (2.4), no genuine
nonempty positive path of unloaded full-degree-two internal bodies
can join two distinct endpoints satisfying the complete canonical
rotation hypotheses of Section 1. The full original packing and
all its other physical contacts remain in the argument.

For the project threshold the upper-radius comparison is exact:

\[
             Q=\frac{1105}{256}<\frac{1152}{256}
                                      =\frac92.
\]

Hence `R^2<=Q` implies the strict upper inequality in (2.4), and
the existing lower radius window gives `R>sigma`. The exclusion
holds throughout the entire closed candidate interval, including
`R^2=1105/256`.

## 4. Simultaneous cycle consequences

**Corollary 4.1 (every cycle size).** Let a positive component be a
simple cycle with at least two loaded vertices and at least one
unloaded vertex. In (2.4), it cannot have every loaded vertex satisfy
the complete endpoint hypotheses of Section 1.

*Proof.* A nonempty maximal run of unloaded vertices lies between
two distinct consecutive loaded vertices. The internal vertices
have full positive degree two because the entire component is a
simple cycle. Its loaded endpoints satisfy Section 1 by hypothesis.
Theorem 3.1 excludes the run. QED.

In fact, only the two endpoints of one such run need satisfy the
test. It follows that in any surviving cycle, the loaded vertices
that fail the complete test must meet every nonempty unloaded run
at at least one endpoint. This is a uniform necessary condition on
the whole cycle; it does not remove the failing vertices or infer
that their zero-weight contacts are absent.

**Corollary 4.2 (all three short-C7 load cardinalities at once).** In
the closed project window, no short-run simple positive seven-cycle
with four, five, or six loaded vertices can have all loaded vertices
satisfy the complete endpoint hypotheses of Section 1.

Indeed all three cardinalities leave at least one unloaded vertex
and at least two loaded vertices, so Corollary 4.1 applies without
distinguishing their cyclic arrangements. The proof also permits
longer unloaded runs; it does not depend on the isolated-transmitter
reduction, the number of completion squares, or the number of
diagonal transmitters.

A concrete entire physical subclass excluded by this result is:
every loaded core body has one physical circle corner, two
nonparallel positive forces, exactly two actual physical neighboring
squares, and each original positive normal strictly exposes one of
its vertices. Proper concurrence then gives (4.1) of the rotation
source, and there is no additional physical contact at that endpoint
to be screened. This excludes all four-, five-, and six-load C7
patterns in that physical subclass simultaneously. More generally,
additional actual contacts are allowed whenever their full
geometric condition in Section 1 has been checked.

True positive degree two alone is insufficient for this corollary.
Extra physical contacts may carry zero weight and still fail the
complete test. A physical second circle corner is also retained
even when its coefficient is zero. No claim is made about those
remaining alternatives, or about a loaded degree-three body obtained
by overlooking a positive edge.

## 5. Inputs, verification, and unchanged scope

| Source read | SHA-256 | Consumed statement |
| --- | --- | --- |
| `CANONICAL_ROTATION_OF_UNBLOCKED_UNIQUE_CIRCLE_TWO_FORCE_BODIES_2026_10_30.md` | `94f4d2ed11af153196d7e68644c5a21b0f3e4619abcb2b042d54a00d1450bda3` | Full complete-contact feasible rotation and exact necessary survivor, Theorem 4.1. |
| `PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md` | `ec8be96131806c998d8a768526d2deb644c28be72559d34e033c8d07d917ffab` | Full source read; Lemma N.1 is the existing normal-channel statement, with the exact needed consequence rederived in Section 3. |
| `FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md` | `7d0c4092ba133a832cf963f329b1c3a6442a3260576f16319293835b39e6d282` | Full source read; its local Lemma 1.1 supplies actual proper concurrence only under the precise degree and nonparallel assumptions. |

The rotation theorem has a separate complete nonauthor review in
`REVIEW_CANONICAL_COMPLETE_CONTACT_ROTATION_AND_RADIAL_DIAGONAL_SURVIVOR_COMMON_CERTIFICATE_2026_10_30.md`.
This channel consequence requires its own independent review before
adoption. The exact scalar-product and width arguments above are
hand proofs over the full continuous domain.

No original fine or coarse ledger flag changes here. The unrestricted
short-C7 remainder, its unscreened physical-contact and circle-mask
alternatives, and the original n=9 sharp lower bound remain open.
No numerical search, mesh, computational certificate, Lean/Lake
invocation, CI dispatch, remote mutation, or replacement of an
actual physical body was used.
