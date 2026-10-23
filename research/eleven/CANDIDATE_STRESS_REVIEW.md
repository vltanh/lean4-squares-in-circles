# Independent review of the candidate stress and local theorem

Reviewed `FIXED_ORIENTATION_STRESS.md`, `LOCAL_OPTIMALITY.md`, their two
checkers, the interval linear solver, and the supporting contact-family and
isolated-root arithmetic. The fixed-frame terminal theorem and the unrestricted
**local** theorem are sound on this review. Neither proves the global n=11
lower bound.

## Fixed-frame contract and rank

The terminal hypotheses explicitly include the fourteen chosen separator
halfspaces as well as the three fixed frames. Keeping the frames fixed alone
would not supply those halfspaces. The note correctly retains this distinction.

The 24 coordinates are 21 centre coordinates, two independent group half-angle
coordinates, and q. Square 1's omitted horizontal coordinate has zero
derivative in every selected active constraint. The two frame derivative
formulas, the three cross-group support derivatives, the signs of the pair
incidence entries, and the disk gradients agree with the stated functions.
In particular the q column is a partial derivative at fixed centres; it does
not incorrectly differentiate the formula giving the reference centres.

The outward interval Gaussian elimination is valid: every chosen pivot
interval excludes zero; interval division encloses every actual pivot division;
setting normalized diagonal and eliminated entries to 1 and 0 uses exact
algebraic identities. The back substitution therefore encloses the actual
solution. This proves full rank and the strictly positive weights, rather
than merely a floating-point residual near a singular matrix.

The weights and matrix are independent of the horizontal slider. Exact
centre balance and the q row give the displayed square-completion identity.
At equality, the eight centres carrying disk weights are fixed. The selected
separators then fix centres 4 and 8 and square 1's height. The remaining
physical separating-axis check correctly leaves precisely H<=h<=a, with no
owner assumed for the slider's limiting oblique contact.

## Physical angular case cover

For a parallel edge contact with transverse displacement tau, both owners
must be retained. The directional maximum is exactly

    n dot (v_j-v_i) + tau*(omega_i+omega_j)/2
      - (1-|tau|)*|omega_j-omega_i|/2.

The formula follows directly from taking the maximum of the two owner
derivatives. The strict |tau|<1 bound excludes the perpendicular axes locally.
For each nonparallel contact, the fifteen strict alternative-axis failures and
the positive selected projection make its chosen signed owner locally
mandatory. Thus the argument applies to actual physical nonoverlap near the
family, including owner switches.

The angular flow signs give r_i=incoming-outgoing, hence
sum r_i*omega_i=sum f_ij*(omega_j-omega_i). The two tilted-group balances
follow exactly from the two group-angle rows of the dual system. The remaining
group balance follows from global rotation invariance and centre balance.
Interval containment of zero is only a consistency check, as the note states.
The strict capacity margins then force equal angle velocities within each
group when the radius velocity is nonpositive.

## Why first-order information is sufficient here

The proof removes both exact zero-cost freedoms before taking a limit: common
rotation is fixed by square 0, and the reference contact configuration is
chosen with the perturbed packing's own slider coordinate. The remaining
displacement therefore has zero slider and gauge components. All 24 selected
constraints remain exact equalities even for the slightly extended formal
slider configurations.

Smooth expansions, together with the Lipschitz absolute-value and maximum
operations, give the stated uniform second-order error on the compact
extended slider interval. Any hypothetical sequence of different feasible
packings with q<=q_c yields a unit limiting displacement satisfying every
necessary first-order inequality. Positive angular margins and the full-rank
Jacobian force that displacement to vanish. This is a contradiction and
establishes an actual neighborhood theorem; it is not a claim that stationarity
alone implies local minimality.

## Execution and scope

Ran `python check_local_angular_stress.py`, which also runs the fixed-orientation
stress certificate. The exact checks passed: all 24 weights exceed 1/100,
all nine angular flow margins exceed 1/100, and all fifteen nonparallel
alternative axes have slack below -1/100. The root certificate and slider
necessity checks also passed.

This review supports closing the conditional fixed-frame sharpness/equality
gate and the unrestricted local sharpness/equality gate. An explicit numerical
capture neighborhood, a global capture theorem, and a complete classification
of distant configurations remain separate obligations. No Lean was written
or executed.
