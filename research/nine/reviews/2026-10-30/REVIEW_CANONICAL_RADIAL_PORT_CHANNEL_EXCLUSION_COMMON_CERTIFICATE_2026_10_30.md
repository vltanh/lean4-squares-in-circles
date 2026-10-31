# Independent review of the canonical radial-port channel exclusion

Date: October 30, 2026. Reviewer: common_certificate continuation.

Target:
`RADIAL_DIAGONAL_CANONICAL_SURVIVORS_CANNOT_BORDER_A_TRANSMITTER_CHANNEL_2026_10_30.md`

Target SHA-256:
`1391bc7d07817c3cc38e3aca152aa909ae354749e4702a9fec462d3a77e87434`.

This final pin updates only the direct-input hash of the preceding
rotation source after its closing-display formatting repair. The
complete channel proof and hypotheses are unchanged.

**Verdict: ACCEPT at the full printed scope.** I read the entire target
and independently reconstructed every scalar inequality, original-channel
identity and cycle application. The previously reviewed complete-contact
rotation source is retained at its frozen hash and its exact hypotheses.
There is no unscreened seven-cycle or original coarse-parent closure.

## 1. Exact original endpoint geometry

The complete-contact rotation theorem was independently reviewed in
`REVIEW_CANONICAL_COMPLETE_CONTACT_ROTATION_AND_RADIAL_DIAGONAL_SURVIVOR_COMMON_CERTIFICATE_2026_10_30.md`.
Its target hash is
`94f4d2ed11af153196d7e68644c5a21b0f3e4619abcb2b042d54a00d1450bda3`,
which matches the channel source's pin.

The channel source retains all its required assumptions: the original
radius/Phi minimum, one physical circle corner at each endpoint,
positive circle coefficient, exactly two original positive pair forces,
nonparallel proper force lines, unique exposure at both original
positive applications, and the stated separator condition at every
additional actual contact including zero-weight contacts.

With `sigma=1/sqrt(2)` and `r=R-sigma`, its actual ports and normals are

    p_±=r e±sigma Je,
    n_±=(-delta e±sigma Je)/sqrt(delta^2+sigma^2),
    0<delta<sigma.

Both ports have norm squared `r^2+sigma^2`, independent of the endpoint's
radial direction and of its delta. Therefore two such endpoint bodies
in the same containing circle have exactly equal actual port radii.
No contact point is replaced by a constructed point to obtain equality.

## 2. Whole-interval strict projection bound

For either sign I compute

    p_±.n_±=(sigma^2-r delta)/sqrt(delta^2+sigma^2)=g(delta).

Differentiation gives

    g'(delta)=-sigma^2(r+delta)/(delta^2+sigma^2)^(3/2)<0,

because the source assumes `R>sigma` and hence `r>0`. The endpoint
calculation is exact:

    g(sigma)=sigma^2-r sigma=1-R/sqrt(2),

using `sqrt(2sigma^2)=1`. The actual strict interval `delta<sigma`
therefore gives

    p_±.n_±>1-R/sqrt(2)>=-1/2

throughout `sigma<R<=3/sqrt(2)`. Strictness remains at the upper
radius endpoint. It comes from unique vertex exposure in the prior
rotation theorem; it is not an omitted side-contact limit.

If two equal-radius actual ports satisfy `p_B-p_A=L n` with `L>=1`
and n the original outward normal at A, expanding their equal squared
norms gives `p_A.n=-L/2<=-1/2`, a direct contradiction. Only equality
of the endpoint port radii and the strict projection at A are needed.

## 3. The original channel gives the exact vector displacement

The source explicitly assumes every internal path body is unloaded
and of true full positive degree two. It does not infer that premise
by deleting a branch or chord. Each body's force equation identifies
the two original directed force vectors, so one positive magnitude
and one signed unit direction propagate along the whole actual path.

Origin-moment balance makes the difference of its outgoing and
incoming applications parallel to that direction. Their actual
support projections differ by the full square width

    |n.u|+|n.v|>=1.

The lower bound follows from orthonormality and the unit norm of n;
it does not use a special orientation. Consequently the full vector
difference is `w n` with `w>=1`. Since both bodies of each pair use
the same original application point or aggregate mean, the successive
differences telescope exactly to

    p_B-p_A=(sum_j w_j)n,    sum_j w_j>=m>=1.

This verifies the required displacement without selecting a new mean
or treating a force projection as a Euclidean point displacement.
All original zero-weight contacts at internal bodies remain physical;
those bodies are not moved in this proof, so these contacts do not
invalidate the equilibrium consequence.

The older discrete side/diagonal classification is unnecessary here,
as the target states. Its sharper possible widths are automatically
included by the whole-angle width bound. All channel lengths are
handled in one argument.

## 4. Radius and every stated cycle caller

The exact project comparison is `1105/256<1152/256=9/2`, so the full
closed project interval lies below `3/sqrt(2)`. The existing lower
window is above `sigma`. Thus the proof includes equality at the
candidate radius, without claiming that every equality packing is
already canonical.

For an entire simple positive cycle with at least two loaded vertices
and at least one unloaded vertex, choose a maximal nonempty unloaded
run. Its two loaded endpoints are distinct, and all internal bodies
have full degree two in the original component. If both endpoints
meet the complete rotation hypotheses, the channel theorem excludes
that run. In particular, if every loaded vertex meets the test,
the cycle is impossible.

This argument applies simultaneously to short C7 with four, five or
six positive loads. It does not need to distinguish their cyclic
placements, transmitter widths or run lengths. The necessary surviving
condition is accurately stated: endpoints failing the complete test
must meet every nonempty unloaded run. Failure of the sufficient
test is not claimed to prove that all possible motions are blocked.

The concrete subclass with exactly two actual physical neighbors at
each loaded body correctly makes the extra-contact check vacuous.
In the project window the previously read local proper-concurrence
theorem supplies `q=tau z` and nonnegative original ray coefficients
under the stated nonparallel and degree assumptions. The physical
single-circle condition remains necessary; a second circle corner
with zero coefficient is not erased.

## 5. Scope of acceptance

This is a complete exclusion of every genuine nonempty transmitter
channel between two endpoints passing the full canonical test, and
of all the stated screened cycle subclasses. Side-owned contacts at
the moving endpoint, physical shared segments, two-circle masks,
extra contacts failing the test, and higher positive endpoint degrees
remain outside the theorem. Those are genuine remaining cases.

The review imports no new numerical observation, changed stress,
graph suppression or post-extraction normal choice. It changes no
original inventory flag and supplies no Lean verification. No pose
search, mesh, compiler, or CI was used.
