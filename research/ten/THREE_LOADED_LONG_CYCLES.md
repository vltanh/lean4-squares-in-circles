# Three-loaded simple cycles have at most seven bodies

**Status:** exact hand proof; the radius and moment comparison have received
independent mathematical review. This excludes three specific transmitter
cases in the finite mixed-cycle inventory. It does not exclude all mixed
positive components or prove the unrestricted ten-square bound.

Suppose a packing of unit squares in an origin-centered disk of squared
radius at most `9/2` has a positive stress component whose **whole body-pair
graph is a simple cycle**, with exactly three circle-loaded bodies. Then
that component has at most seven bodies.

Use the physical force conventions and degree-two transmission theorem of
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md). An unloaded
body in this whole cycle has degree two, so it is a side transmitter S of
width one or a diagonal transmitter D of width `sqrt(2)`. This statement
must not be applied to a cycle that is only a block of a branching positive
component: its unloaded vertices can have additional positive edges.

## 1. A transmission path separates endpoint centers

Every square center satisfies

```text
|c| <= A=(sqrt(17)-1)/2.                            (1)
```

Indeed, in the square's own frame a center of norm r has a farthest vertex
of squared norm at least `r^2+r+1/2`. Containment in the disk gives
`r^2+r+1/2<=9/2`, yielding (1).

Consider a nonempty unloaded transmission path between loaded endpoint
squares H and L. Let d be its unit direction from H to L and let W be the
sum of the unloaded widths. The transmission theorem gives endpoint
support contacts `p_H,p_L` with `p_L-p_H=W d`. Consequently

```text
d dot(c_L-c_H)=W+h_H(d)+h_L(d)>=W+1,               (2)
```

where `h_H,h_L` are the endpoint squares' directional halfwidths. Each
unit square has halfwidth at least `1/2` in every direction. In particular

```text
|c_L-c_H| >= W+1.                                  (3)
```

Combining (1) and (2) gives `W+1<=2A<25/8`, so `W<17/8`. Since each
unloaded width is either `1` or `sqrt(2)`, a run contains at most two
unloaded bodies, and a run of length two consists of two side transmitters.
Its width is exactly two and its endpoint centers are at distance at least
three. A run of length one has width at least one and endpoint centers
at distance at least two.

These are inequalities between the actual endpoint centers. No assumption
about a common square orientation or a common force line for different
paths is made.

## 2. Eight or nine bodies force too large a three-center moment

The three loaded bodies divide the cycle into three unloaded runs of
lengths `r_1,r_2,r_3`, each in `{0,1,2}`.

For eight bodies their lengths sum to five, so, up to permutation, they
are `(2,2,1)`. For nine bodies they are `(2,2,2)`. Ten or more bodies
would require a sum of at least seven and are already impossible.

In either remaining case all three runs are nonempty. For the loaded
centers `c_1,c_2,c_3`, (3) therefore gives two pairwise distances at least
three and the third at least two. Hence

```text
|c_1-c_2|^2+|c_2-c_3|^2+|c_3-c_1|^2 >= 9+9+4=22. (4)
```

On the other hand the exact three-point identity and (1) give

```text
sum_(i<j) |c_i-c_j|^2
 = 3 sum_i |c_i|^2 - |c_1+c_2+c_3|^2
 <= 9 A^2
 = (81-9sqrt(17))/2
 < 22.                                             (5)
```

The last strict inequality is equivalent to `37<9sqrt(17)`, which follows
by squaring the positive quantities: `37^2=1369<1377=81*17`.
Equations (4) and (5) contradict each other, completing the proof.
Contact equality and the containing radius `3/sqrt(2)` are both allowed.

## 3. The exact finite cases closed

The [cycle inventory](cycle_cases.json) retains its original 80 binary
families and 279 transmitter cases. This theorem closes precisely the
following entries; [cycle progress](cycle_progress.json) records their
status separately so the coverage inventory remains fixed.

| Stable case ID | Canonical transmitter word | Unloaded run lengths |
| --- | --- | --- |
| `C20-M08-L03-B01-T01` | `LSLSSLSS` | `1,2,2`, all side transmitters |
| `C20-M08-L03-B01-T02` | `LDLSSLSS` | `1,2,2`, the single transmitter diagonal |
| `C20-M09-L03-B01-T01` | `LSSLSSLSS` | `2,2,2`, all side transmitters |

The three-loaded cases of lengths five, six, and seven remain governed
by their separate reductions. Components with more loaded bodies or with
branching cyclic graphs are outside this theorem.
