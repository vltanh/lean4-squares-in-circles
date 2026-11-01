# Direct nine-square pilot — implemented model and exact row-family result

The source specification previously attached to D.1.a is now implemented in [emit_unrestricted_nine.py](emit_unrestricted_nine.py). The [complete source proof](UNRESTRICTED_MODEL_AND_ROW_CERTIFICATE.md) proves representation, disk containment, pair separation, absolute-value-free quadratic branches, exact strict-radius elimination and the optional global rotation gauge.

The emitter is unrestricted: independent square centers and orientations, all 36 actual corners, and all 36 pair nonoverlap predicates. It contains no stress or contact-graph hypothesis. Variable-radius mode has 37 real variables and 83 assertions. Strict-Q with a legal common rotation gauge has 34 real variables and 80 assertions. Every polynomial has degree at most two; each pair is eight alternatives of four inequalities.

[Exact emitted-text tests](test_unrestricted_nine.py) use a separately written parser and polygon-area intersection oracle. All six modes pass the known oblique equality witness and deliberate invalid controls. [Saved execution report](unrestricted_model_test_report.json). These are finite regression tests, not a proof by sampling.

A first proof-producing pilot now has a [rational quadratic certificate](row43_certificate.json), [generator](make_row43_certificate.py), [separate verifier](verify_row43_certificate.py), and [passing replay report](row43_verification_report.json). It proves q>=1105/256 for the ENTIRE continuous parallel four-over-three row subfamily, allowing free gaps, row offsets/heights and two arbitrary additional physical squares. Its exact identity has ten nonnegative hypothesis terms and six weighted squares, with zero coefficient residual.

**This is not a cover of arbitrary relative orientations.** It is not asserted novel relative to earlier row-source mathematics; it independently demonstrates the direct exact proof format. No general SMT solver was installed; the install attempt failed because network name resolution was unavailable, so no general solver run/result is claimed. No separate human review, Lean or CI occurred.

**ACTIVE NEXT: D.3.c.** Extract an obstruction/certificate covering unrestricted orientation domains, or document a concrete limitation and deliberate pivot. Do not enumerate additional checkpoints inside the already solved row profile. The global sharp lower bound and complete equality classification remain OPEN.
