# Uniform positive contact-moment flux on a stressed seven-outer ring

## Theorem

Choose an eight-square radius minimizer below radius two.
Suppose the seven noncentral square centers have norm at least
one and their induced *actual-contact* graph is the full
seven-cycle in circular center order.

Fix any normalized physical stress as in
HUMAN_CONTACT_EQUILIBRIUM.md. Assume **all chosen stress
multipliers on contacts with the central square C vanish**.
This assumption holds, in particular, if C has no actual
contact with the ring; it may also hold if C has actual
contacts which are assigned zero stress weight.

Then:

1. Every one of the seven outer-cycle contact edges has
   strictly positive stress weight.
2. The seven directed angular contact moments are all the
   same positive number tau.
3. If an outer vertex has no positive circle multiplier,
   its two neighboring contact forces cancel; their
   separating normals are opposite and their weights
   equal. If that square is strictly inside the disk,
   the existing two-contact alignment theorem applies
   provided no other actual contacts occur.
4. No independent tree or disconnected positive-stress
   component exists.

This is an exact conditional result; it does not assert
that the central square must be stress-free, and it does
not yield the sharp n=8 lower bound by itself.

## Proof

Number the outer squares S_0,...,S_6 by circular order;
the actual edges are E_i=S_i-S_(i+1), with indices mod 7.
For each E_i orient a separating normal n_i from
S_i to S_(i+1). Let Lambda_i>=0 be its combined
contact multiplier in the chosen normalized stress
and z_i its effective common contact point if
Lambda_i>0.

HUMAN_OUTER_MOMENT_ORIENTATION.md proves that for
**every** actual outer contact, any available normal
and common contact point have strictly positive
angular moment:

    z_i cross n_i>1/20.                                (1)

Thus define

    tau_i=Lambda_i*(z_i cross n_i)>=0,

with tau_i=0 by convention when Lambda_i=0. The
positivity theorem gives

    tau_i>0 if and only if Lambda_i>0.                  (2)

Circle constraint forces act radially and therefore
have zero moment about the origin. Under the present
hypothesis the central contacts also exert no chosen
forces. Physical moment balance on S_i now reads

    tau_(i-1)-tau_i=0.                                  (3)

This sign convention follows because the predecessor
pushes S_i along +n_(i-1) at its common contact point,
whereas the successor exerts -n_i on S_i.

Equation (3) around the seven vertices implies

    tau_0=tau_1=...=tau_6=:tau>=0.                     (4)

The stress is **normalized**: the total circle
multiplier is one. If all contact multipliers were
zero, the translation force balance on every square
would say 0=2*sum_alpha mu_(i,alpha)*x_(i,alpha).
For a square centered inside the containing disk
in its fixed frame, the exact center-support
inequality in HUMAN_CONTACT_EQUILIBRIUM.md, section 4,
implies that the vanishing contact force is equivalent
to vanishing total circle multiplier m_i.
Every mu coefficient would therefore vanish,
contradicting normalization. Hence at least one
contact multiplier is positive.

By the central-stress-free hypothesis, this positive
multiplier is on some outer-cycle edge. Its tau_i
is positive by (2), so (4) gives tau>0. Applying
(2) to every edge now shows Lambda_i>0 for all
seven edges. This proves the first two assertions.

At an outer vertex with no positive circle
multiplier, the force equation has zero right
side. Exactly two positive stress forces act
there, along its two neighboring ring contacts.
Their sum can vanish only when they have equal
magnitudes and opposite unit normals. Thus
the local force-transmission assertion holds.
If the vertex is strictly inside the disk and
has exactly these two *actual* contacts, the
analytic opposite-contact alignment theorem in
HUMAN_CYCLE_ANALYSIS.md applies. Positive stress
degree two is not being silently equated with
actual degree two when extra zero-weight
contacts may occur.

Finally all seven edges have positive weight,
so their positive-stress graph contains one
connected seven-cycle. The central square
is stress-free and has no positive edge,
and there are no other squares. This proves
the fourth assertion.

## Limitation

The central square might have two or more
positively stressed spokes into the seven-outer
ring; then its contact moments enter the flux
equations and the ring fluxes need not agree.
The alternate outer-path-with-inner-attachments
case also does not satisfy the hypotheses.
To prove R8>=Rhat one must eliminate or
quantitatively bound those alternatives as well
as the stress-free full-ring branch. A constant
moment flux alone is not a radius obstruction.


## Two central stressed spokes give exactly two flux plateaus

There is a second **conditional, exhaustive** refinement.
Suppose, instead of the stress-free hypothesis of the theorem,
that the physical stress has exactly two nonzero central
contact resultants, at distinct ring vertices S_a,S_b.
All ring vertices are outer; there are no other inner
squares. By HUMAN_TWO_FORCE_SQUARE_CLASSIFICATION.md,
the central forces are equal and opposite, act along
one common line, and their normals are either a
central side normal or a central vertex diagonal.

Let M_i denote the scalar moment on outer S_i of
its stress force from C, setting M_i=0 when C
has no positive stress contact with S_i.
The contact reaction on C is opposite at the same
effective point, so moment balance on C gives

    M_a+M_b=0,           M_i=0 for i not a,b.        (5)

Physical moment balance on every outer square is

    tau_i-tau_(i-1)=M_i,   tau_i>=0,                 (6)

where tau_i denotes the positively oriented outer
ring moment of edge S_i-S_(i+1), defined in
the theorem above. Thus the sequence tau_i is
**constant on each of the two circular outer
edge arcs from S_a to S_b and back**.
There are two nonnegative plateau values
tau_+,tau_-, and their difference is M_a
(up to the choice of which arc is called +).
Their difference may vanish if the common
central force line is radial about the disk origin.

At least one plateau is strictly positive.
Indeed, if every ring tau_i were zero, then
every ring stress multiplier would vanish by
the outer contact strict-moment theorem.
The entire positive stress graph would consist
of the two central spokes and would be a
three-vertex tree. The nonradial-component
theorem of HUMAN_CONTACT_EQUILIBRIUM.md,
sections 7--8, excludes any nontrivial stress-tree
component in the established eight-square
minimizer radius range R>sqrt(2)+1/2.
Normalization excludes the empty graph.
Consequently the stress support around the ring
is either its entire seven-cycle (both plateaus
positive), or **one contiguous positive run**
between the two central spokes (one plateau
zero, the other positive). A mixture of
several disjoint positive ring runs is
impossible under this two-spoke hypothesis.

The statement permits additional *actual*
contacts carrying zero chosen stress; it
concerns the flux and support of one fixed
physical stress. It does not classify
higher central stress degree, nor establish
the sharp radius in either remaining plateau
case.
