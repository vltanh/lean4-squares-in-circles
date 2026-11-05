# Height threshold 7/10 for an extra original with slope at most 1/2

The actual-AB two-link row terminal now excludes height variation at most `7/10` when the selected extra original satisfies `|tan(theta_extra)|<=1/2`, in addition to the original good-D and D/G corridor guards. The unrestricted extra orientation still uses the separately accepted `16/25` theorem.

The complete rational Bernstein certificate has 28 domains, 127 leaves, 15,875 independently recomputed coefficients, and zero unresolved frontier. It proves scalar coefficient `701/1000`, leaving an exact margin `1/1000` at the physical height threshold. The hand proof supplies the full physical lifting and the equality exclusion in the strict-CD caller.

```sh
python -B -S check_conditional_three_angle.py cover /tmp/conditional070-replay.json
```

The checker imports no numerical solver or discovery code. The half-angle box is `[0,29/70] × [0,17/72] × [0,29/70]` in order D, extra, B. The extra slope condition is essential. All sign, owner and boundary alternatives within that box are retained.

This result was discovered to strengthen the remaining A-c744 component. Its whole original remains OPEN until every complementary domain is excluded and independently replayed. New original-cell credit: 0. New mask credit: 0. No Lean, Lake, compilation or CI was run.
