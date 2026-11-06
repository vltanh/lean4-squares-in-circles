"""Exact boundary control for Cd402; plotting is diagnostic, not a closure.

Run: python visualize_boundary.py [output-directory]
The arithmetic uses fractions only. Matplotlib is needed only for plotting.
No Lean or CI is invoked. The control satisfies the CLOSED weak-link
relaxation, not the original strict CD bit, and lies at Q, not below Q.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import sys

Q = F(1105, 256)
LABELS = "ABCDEFGHI"
CENTERS = [(-F(3, 2), -F(1, 16)), (-F(1, 2), -F(17, 16)),
           (F(1, 2), -F(17, 16)), (F(3, 2), -F(1, 16)),
           (-F(1), F(15, 16)), (F(0), F(1)), (F(1), F(15, 16)),
           (-F(1, 2), -F(1, 16)), (F(1, 2), -F(1, 16))]
LINKS = [(0, 1), (1, 2), (2, 3), (4, 5), (5, 6)]


def verify():
    """Check every original square and pair, without floating arithmetic."""
    largest = F(0)
    for x, y in CENTERS:
        for sx in (-1, 1):
            for sy in (-1, 1):
                value = (x + F(sx, 2)) ** 2 + (y + F(sy, 2)) ** 2
                assert value <= Q
                largest = max(largest, value)
    for i in range(9):
        for j in range(i + 1, 9):
            dx = abs(CENTERS[j][0] - CENTERS[i][0])
            dy = abs(CENTERS[j][1] - CENTERS[i][1])
            assert max(dx, dy) >= 1  # Exact aligned-square separation.
    for i, j in LINKS:
        dx = CENTERS[j][0] - CENTERS[i][0]
        dy = CENTERS[j][1] - CENTERS[i][1]
        assert dx >= abs(dy)
        assert dx == 1  # Every selected projection link is actual.
    assert CENTERS[3][1] - CENTERS[2][1] > F(2, 3)
    assert CENTERS[7][0] <= CENTERS[8][0]
    assert (CENTERS[7][0] - CENTERS[1][0]
            - CENTERS[7][1] + CENTERS[1][1]) <= 0
    assert largest == Q
    return {"status": "PASS_EXACT_BOUNDARY_CONTROL",
            "corner_checks": 36, "pair_checks": 36, "cone_checks": 5,
            "largest_corner_squared": str(largest),
            "strict_CD_bit": False, "strict_subcritical_radius": False,
            "new_original_cell_closures": 0,
            "interpretation": "Boundary of the relaxation, not a counterexample."}


def draw(output):
    import math
    import matplotlib.pyplot as plt
    from matplotlib.patches import Circle, Rectangle
    fig, ax = plt.subplots(figsize=(8, 8))
    ax.add_patch(Circle((0, 0), math.sqrt(float(Q)), fill=False,
                        linestyle="--", linewidth=1.5))
    for label, (x, y) in zip(LABELS, CENTERS):
        ax.add_patch(Rectangle((float(x)-.5, float(y)-.5), 1, 1,
                               fill=False, linewidth=1.5))
        ax.text(float(x), float(y), label, ha="center", va="center", fontsize=15)
    ax.set(xlim=(-2.3, 2.3), ylim=(-2.3, 2.3), aspect="equal",
           xlabel="Horizontal coordinate", ylabel="Vertical coordinate",
           title="Cd402: exact boundary control, not a strict-mask packing\n"
                 "R squared = 1105/256; CD projection gap = width sum = 1")
    ax.grid(alpha=.2)
    fig.tight_layout()
    fig.savefig(output / "sharp_boundary.svg")
    fig.savefig(output / "sharp_boundary.png", dpi=160)
    plt.close(fig)


def main():
    output = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(".")
    output.mkdir(parents=True, exist_ok=True)
    report = verify()
    (output / "exact_boundary_report.json").write_text(json.dumps(report, indent=2)+"\n")
    draw(output)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
