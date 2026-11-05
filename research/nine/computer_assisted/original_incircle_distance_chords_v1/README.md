# Necessary center-distance chords for original unit squares

Disjoint original unit squares have disjoint open incircles of radius 1/2, so their center distance is at least 1. On a certified signed component and transverse interval, a rational chord of the lower unit semicircle gives a necessary affine row in the original center coordinates. No selected separating axis, orientation sign, mask bit, or circle-radius premise is used.

`HAND_PROOF.md` derives the complete implication, including all closed endpoints and degenerate endpoint heights. The independent decoder reconstructs every literal coefficient, verifies the two exact endpoint inequalities, and checks the consuming state's same-pair sign and transverse interval. The producer proposes dyadic lower square-root endpoints; no floating-point output is trusted.

## Reproduce

```sh
python -B -S check_controls.py /tmp/incircle-chord-controls.json
```

The exact controls exercise both component axes and signs on 440 rational unit-distance configurations, and reject 96 damaged right-hand sides or invalid state guards. The checker uses only Python's standard library and does not import the producer.

The family has been used in numerical B/C continuations and independently checked weighted B-prefix deductions. This small packet proves the row family only. A future whole-cell certificate must replay its own original domain, every ancestor and complete closed cover, and each consuming state's guards; these controls do not replace those obligations.

New original-cell credit: 0. New mask credit: 0. No Lean, Lake, compilation or CI is used.
