# A uniform central core at the candidate ceiling

This is a global intermediate certificate theorem for arbitrary eight-square
packings at squared radius at most 98/25. It neither assumes common exterior
orientations nor a candidate contact graph.

## 1. Extended-state pair certificate

In a sorted side frame write the center of a square as (a,sigma*u), with
0<=u<=a. Unlike the earlier exterior marker lemma, allow a below 1/2:

    5/12 <= a <= 3/2,    0<=u<=a,
    (a+1/2)^2+(u+1/2)^2 <= 98/25.

Define a NEW marker label for this theorem only:

    ell_core(a,u)=min(11u/10+(u/a)^4/5,
                      5/9+3u/5-17a/50,
                      157/200).

The denominator is positive. The label remains between 0 and 157/200 on the
full enclosing rectangle. This label is different from ell_ring in
SHARP_MARKER_RING.md: the >7/8 ring theorem must not silently be applied to it.

The exact verifier `verify_central_core.cpp` proves that two disjoint squares
in this extended state domain have core-marker distance strictly greater than
11/14. It checks all four first-frame support sums for each sign pair and
uses the reverse/reflected pair to cover the second-frame axes. The same
separating-axis argument as the exterior certificate then gives the claim.

The quartic term was found by exploratory optimization. The proof uses the
full-domain interval verification, not the discovery procedure.

## 2. Executed exact certificate

Compile and run:

```sh
g++ -O3 -std=c++17 research/eight/verify_central_core.cpp -o /tmp/n8core
/tmp/n8core
```

The code shares the 48-bit dyadic interval engine, exact integer rounding,
Taylor bounds, and admissibility contractions of the existing marker verifier.
The starting a lower endpoint is rounded downward from 5/12 and the gap upper
endpoint upward from 11/14. Thus neither exact boundary is missed.

The quotient u/a is enclosed by positive interval division; intersecting its
upper enclosure with 1 is valid because every feasible state has u<=a. No
floating-point value accepts a terminal box. Only strictly positive exact
support lower bounds do so; budget exhaustion is failure, not success.

All four cases terminated:

| signs | Nodes | Positive terminal boxes | Maximum depth | Minimum leaf margin, denominator 2^48 |
| --- | ---: | ---: | ---: | ---: |
| -1,-1 | 5199 | 2600 | 31 | 3290350679 |
| -1,+1 | 11383 | 5692 | 41 | 1211334 |
| +1,-1 | 14133 | 7067 | 31 | 4332916735 |
| +1,+1 | 47359 | 23680 | 42 | 37826307 |

There were no empty terminal leaves after the sound contractions. Each case
satisfies nodes=2*leaves-1. The domain includes squares containing the origin
but not too deeply; the proof does not incorrectly presume they are exterior.

## 3. The unique central square has a uniform interior reserve

If all eight sorted states had a>=5/12, their eight core markers would have
successive cyclic gaps greater than 11/14. Their sum would therefore exceed
8*(11/14)=44/7>2*pi, contradicting pi<22/7.

Consequently one square has sorted primary offset a<5/12. In its own frame its
center C=(cx,cy) satisfies

    max(|cx|,|cy|)<5/12.

It contains the origin in its open interior and is unique, since open square
interiors are pairwise disjoint. More strongly, it contains the entire CLOSED
disk of radius 1/12 in its OPEN interior: for any point |p|<=1/12, each local
coordinate of p-C has absolute value at most 1/12+max(|cx|,|cy|)<1/2.

After a rigid frame change and a square symmetry one may thus assume

    0<=cy<=cx<5/12,

without restricting any exterior orientation.

## 4. Consequences for all seven exterior squares

Every other closed square avoids that closed disk. Indeed, a point belonging
to its closed square and the open central square can be approximated from its
interior while staying in the central open square, contradicting interior
disjointness.

For sorted exterior coordinates (a,u), with a>=1/2 and 0<=u<=a, the minimum
squared distance from the origin to the closed square is exactly

    (a-1/2)^2 + max(u-1/2,0)^2.

Hence every exterior square satisfies

    (a-1/2)^2 + max(u-1/2,0)^2 > 1/144.        (1)

Because max(u-1/2,0)<=a-1/2, this implies

    a > 1/2+1/(12*sqrt(2)) > 5/9.

If u<=1/2, the stronger bound a>7/12 follows. The two exterior-state bounds
are consequences, not new assumptions introduced into the packing problem.
They may be relaxed to non-strict inequalities in a numerical certificate.

The previous >7/8 exterior-ring theorem still applies with its own ell_ring.
Combining them leaves seven exterior squares outside a fixed central disk,
with ordered marker gaps between 7/8 and 29/28 and total excess below 9/56.

## 5. Why this is useful and what remains

The earlier exact seven-exterior counterexample had a square arbitrarily close
to the origin. It is excluded by (1). This does not prove that ALL seven-ring
counterexamples disappear: that stronger optimization problem must still be
solved, rather than inferred from exclusion of one example.

An exploratory seven-square optimization including the empty radius-1/12 disk
returned the candidate value as its smallest feasible value in 50 starts.
That is a search diagnostic, not a lower-bound proof or exhaustive search.
The exact theorem proved here is the central core and the resulting state
restriction. A sharp global obstruction remains to be established.

No Lean formalization is attempted. This certificate is an intermediate
mathematical result; analytical simplification remains possible later.
