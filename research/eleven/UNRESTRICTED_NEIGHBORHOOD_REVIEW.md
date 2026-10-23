# Independent review of the explicit physical neighborhood

Review outcome: **PASS**, including direct replay of
`check_unrestricted_neighborhood.py`. The theorem gives an explicit
`N<=1/10^7` neighborhood of the enlarged exact slider family in which every
physical packing has `q>=qc`, with complete physical equality. All eleven
individual angles and all permitted center coordinates may vary. This is
a quantitative local theorem; it does not assert global capture.

## Physical owners and analytic remainder

The norm estimates imply each unsigned physical separator slack changes
by at most `8N`: the projection changes by at most `3N+3N`, and the
1-Lipschitz support width changes by at most `2N`. The exact transverse and
oblique alternative-axis margins therefore preserve the complete local
owner cover. Both owners at every parallel contact remain in the maximum;
the opposite signed projection is excluded by its strictly positive
reference sign. The oblique angle margins preserve the smooth support
quadrant.

The rotation remainder bound `||R_omega z-z-Jz*omega||<=||z||*omega^2/2`
is valid uniformly. It gives the claimed disk error below `10N^2`, including
the actual squared displacement term. For each projection, the normal
remainder and normal/center cross product give less than `9N^2/2`.
Both the smooth oblique support and the nonsmooth parallel support have
error at most `2N^2`. The maximum is Lipschitz in the maximum norm, so
maximizing the two parallel owner slacks does not enlarge the error.
These checks justify the common bound `|f_i-D_i|<=10N^2` for all 24 slacks.

## Stress, grouped estimate, and contradiction

The exact angular-flow inequality has the needed sign:
`sum w_i D_i<=rho-T/100`. The certified `W<20`, individual `w_i>1/100`,
and nonnegative physical slacks consequently imply, when rho<=0,

    T<=20000N^2,       0<=f_i<=20000N^2,
    |D_i|<=20010N^2.

The nine-edge graph connects exactly the three stated orientation groups,
so replacing angles by their group representatives changes each individual
angle by at most T. The absolute angular coefficient sums are bounded by
five for disk and oblique rows. For a parallel row, the smooth replacement
and the removed absolute-value penalty together are also below `5T`.
Hence the grouped rows satisfy `|L_i|<=120010N^2`.

The inverse-norm computation has the correct transpose convention: a column
of the inverse transposed Jacobian is a row of the inverse Jacobian. The
ordinary-angle conversion multiplies only the two output angle rows by
`2/(1+t^2)<2`. The interval solver therefore certifies the claimed inverse
infinity norm below 40. The grouped matrix is independent of the slider h,
because the two selected slider edges have fixed vertical normals and no
group-angle derivative.

The grouped vector retains every center and radius deviation. Recovering
the eleven independent angles costs at most T, yielding exactly

    N <= (40*120010+20000)N^2 = 4820400N^2.

This contradicts `0<N<=1/10^7`. At N=0, the separate physical slider
necessity theorem forces the actual h into `[H,a]`, including endpoints.
The formal enlarged reference interval causes no gap: its selected
equalities and all constants were verified uniformly, even when the
reference itself is outside the physical slider range.

The supplied checker replay passed every bound, including all 24 inverse
column solves. The earlier angular-flow, owner-margin, root, and
fixed-orientation certificates remain explicit dependencies. No optimizer
result, finite difference, or unproved second-order condition is used.

## SHA-256 bindings

| File | SHA-256 |
| --- | --- |
| `UNRESTRICTED_NEIGHBORHOOD.md` | `4c61f010ef2a1897f79cfce1c94f76f964eb99469856e38e9675b6479b9ffa78` |
| `check_unrestricted_neighborhood.py` | `d34764aaf516468b7e4633bd9380e41d6fc20c22d8d9bc2a052873a14a2a2644` |
