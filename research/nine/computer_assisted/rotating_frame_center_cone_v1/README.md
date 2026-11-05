# Original-square rotating-frame center cone rows

Necessary exact rational support rows at Q=1105/256. The package is restricted to the cone family.

Run `python -B -S verify_packet.py` from this directory. Only the Python standard library is required. The producer is `physical_center_cone_rows.py`; its interface is `generate(angles)` and `row(angles,owner,axis,sign,nx,ny)`. The independent interface is `independent_center_cone_rows.verify_literal(literal,angles)`. Supply independently reconstructed physical angle intervals in the production verifier.

The hand proof derives cap=352321/232320 and k=30/121 directly from the four original corner inequalities and an exact completing-square identity. Each guard is checked at both endpoints of a closed certified slope interval. No new geometric case or auxiliary variable is introduced.

`ACTUAL_WEIGHTED_EXCERPT.json` retains a real 17-row bound deduction with a positively weighted cone row. Its verifier checks the new cone literal and the complete exact dual sum and outward-rounded bound, conditional on the older printed row families. Their provenance and the original-cell ancestry remain obligations of the existing physical verifier. The complete bound record is compressed in `ACTUAL_WEIGHTED_BOUND_RECORD.json.gz`; its local independent replay result is also saved. The local replay validated232 deductions and529 printed rows, including3 cone rows and1 accepted incircle chord.

This is a row-family publication packet. It claims zero original-cell and zero mask closures. Discovery continuations and complete original-cell certificates are separate.
