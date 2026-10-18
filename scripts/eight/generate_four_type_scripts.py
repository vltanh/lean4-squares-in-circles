#!/usr/bin/env python3
"""Write the finite F5 proof scripts, without evaluating their propositions.

This is source generation only.  The continuous expressions and sound
closed-box compiler live in Lean.  No certificate replay, Lean invocation,
numeric search, or audit is performed by this script.
"""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / "SquaresInCircles/Eight/Arithmetic/FourTypePairs.lean"
BRANCHES = ["coreSide", "coreCorner", "low", "middle", "high"]
BEGIN = "-- BEGIN FINITE FOUR-TYPE PROOF SCRIPTS"
END = "-- END FINITE FOUR-TYPE PROOF SCRIPTS"


def main() -> None:
    lines = [BEGIN, ""]
    for source in BRANCHES:
        for target in BRANCHES:
            lines.extend([
                "set_option maxRecDepth 2000000 in",
                "set_option maxHeartbeats 0 in",
                f"theorem {source}_{target}_certificates :",
                "    ∀ p r four : Bool,",
                f"      certify depth (problem .{source} .{target} p r four)",
                f"        (domain .{source} .{target})=true := by",
                "  decide",
                "",
            ])
    lines.extend([
        "theorem source_axis_certificates (s t : Branch) (p r four : Bool) :",
        "    certify depth (problem s t p r four) (domain s t)=true := by",
        "  cases s <;> cases t",
    ])
    for source in BRANCHES:
        for target in BRANCHES:
            lines.append(f"  · exact {source}_{target}_certificates p r four")
    lines.extend(["", END])
    text = TARGET.read_text()
    before, rest = text.split(BEGIN, 1)
    _, after = rest.split(END, 1)
    TARGET.write_text(before + "\n".join(lines) + after)
    print("Wrote 25 unevaluated finite proof scripts covering 200 analytic chart/sign/source-axis cases.")


if __name__ == "__main__":
    main()
