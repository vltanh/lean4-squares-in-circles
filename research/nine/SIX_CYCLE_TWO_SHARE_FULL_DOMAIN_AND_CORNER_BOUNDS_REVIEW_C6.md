# Independent review: complete two-share C6 domain and corner bounds

Date: October 26, 2026.

Reviewed source: `SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md`.

**Verdict: accepted as an exact whole-domain reduction and necessary
inequalities.** The source does not assert an exclusion of the two-share
family or closure of an original gate, and this review makes neither
assertion. No numerical optimization, Lean compilation, or coefficient
certificate is used in the review.

## 1. Exhaustive contact-type cover

The strict-turn normal form gives at most one genuine shared interface
at each loaded unit. The accepted double-shared-channel exclusion gives
at most one such interface at each transmitter. Two shares therefore
form a matching in the original six-cycle.

Reflection of the complete packing, with reversal of cyclic labeling,
interchanges incoming and outgoing applications. The transformed
directed side is `-T u`, and its new base is `T(b+u)`. Substituting the
old circle corner `b+chi u+v` gives the transformed bit `1-chi`.
Cyclic relabeling and this reflection reduce the constant words to
`111` and the nonconstant words to `110`.

For `111`, the only possible shares are outgoing, and the three choices
of a pair of loaded units form a single cyclic orbit. For `110`, the
three possible placements are `{0,1}`, `{0,2}`, and `{1,2}`. The last
uses transmitter 1 twice and is excluded by the already accepted
double-shared-channel theorem. This proves the stated exact cover by
three rows. In particular it does not identify the two allowed mixed
placements or omit a physical share with an endpoint mean.

## 2. Exact local algebra

In the local frame with incoming normal `(1,0)` and outgoing normal
`(c,s)`, write the incoming and outgoing magnitudes as `a,b>0`.
Then `F=(a-bc,-bs)` and `D^2=a^2+b^2-2abc`.

For a nonshared bit-one body,

```
g = (a+bs, a-bc),
E^2 = 2a^2+b^2+2ab(s-c),
F dot g = a(a-bc),
F dot (-Jg) = D^2+ab s.
```

For a nonshared bit-zero body,

```
g = (b(c+s), a+b(s-c)),
E^2 = a^2+2b^2+2ab(s-c),
F dot g = -b(b-ac),
F dot (-Jg) = D^2+ab s.
```

The actual shared means give respectively
`g=-(b+a(s-c))Jn_next` and
`g=(a+b(s-c))Jn_previous`. These substitutions verify every magnitude
in the source's first local table and every dot product in its corner
table. All dividing factors are positive on the stated domain.

The strict physical-mask statement is also correct: subtracting the
squared radii of each adjacent vertex from the squared radius of the
unique actual circle corner gives exactly the two strict inequalities
in (8). These are properties of the actual square, independently of
which nonnegative circle-load weights were selected. Combining them
with the verified local dot products yields precisely the source's
four rows. No neighboring vertex may be silently allowed to lie on the
circle in this unique-corner branch.

## 3. Uniform constants and scope

Completing the square in the first shared inequality gives the stated
strict bound with `cos(theta)+sqrt(4R^2-1)sin(theta)`. Since the cosine
is negative and the sine is at most one, the radius window gives
`sqrt(1041)/8`; its squared gap below `81/20` is `219/1600`.

For each nonshared type, `E^2-D^2` has exactly the positive value
printed in the source. Dividing the appropriate corner inequality by
the positive incoming or outgoing force square gives (12). The
rational upper bounds on `R` and `-cos(theta)` give the coefficient
`6831/4480` and constant `101/32`. At `x=27/10` the resulting
quadratic has value `151/8960>0`, and its derivative is at least
`17361/4480>0` for every larger `x`. Thus `x<27/10` follows over the
entire continuous domain, with no angle or force-ratio subdivision.

The source keeps the full force scale, all actual means, all three
transmitters and all three extra squares. Its closure and virial
identities are used as necessary consequences of the unchanged channel
equations. No relaxation is represented as a sufficient packing model.
The source accurately retains the two-share contradiction, the
one-share completion problem, the obtuse one-radial problem, equality,
and the previous prerequisite audit as open obligations.
