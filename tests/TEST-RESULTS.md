# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: the harness oracle, `oracle_parse` in tests/run_tests.py run under Python 3.13.17, a second reading of SPEC.md that settles every verdict; Scapy 2.8.0 built some inputs and RFC 2131 and RFC 2132 others by hand, but no outside decoder judges any input
- Seed: 20261026
- Inputs: 4104
- Failures: 0
- Command: python3 tests/run_tests.py --seed 20261026 --count 1500 --raw-count 1200 --area-count 800
- ISC DHCP and dnsmasq captures: not present in this environment, no capture corpus run
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)

## Counts

| part | inputs | agreed |
| --- | --- | --- |
| fixed cases: hand-built messages, the pad cases, the rejection shapes | 26 | 26 |
| requests with no codes, answered none | 2 | 2 |
| the README example, answered ok: with the same codes | 1 | 1 |
| the readings that depart from the RFCs, with the verdict SPEC.md states | 17 | 17 |
| random well formed messages (seed 20261026) | 1500 | 1500 |
| random raw byte strings (seed 20261026) | 1200 | 1200 |
| random option areas behind a fixed part and cookie (seed 20261026 + 1) | 800 | 800 |
| mutations of one message: every truncation, every single byte flip, two targeted changes | 536 | 536 |
| packets built by Scapy 2.8.0, from tests/scapy-packets.txt | 10 | 10 |
| malformed request lines, answered error | 12 | 12 |
| total | 4104 | 4104 |

An input agrees when the tool's answer is the oracle's answer, byte for byte, and, when it is `ok:`, the reprint is a well formed message, as `Spec.parse_wf` says. The harness keeps no list of excused differences: every disagreement counts as a failure.

Of the 800 random option areas, the oracle takes 133 and turns away 667.
