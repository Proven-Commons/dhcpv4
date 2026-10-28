# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: a strict reading of the rules in SPEC.md written in the harness (Python 3.12.3), plus hand-built fixed cases from RFC 2131 and RFC 2132
- Scapy: Scapy in the project venv (venv/bin/python); packets built with its BOOTP and DHCP layers and settled by the oracle
- ISC DHCP and dnsmasq captures: not present in this environment, no capture corpus run
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261026
- Fixed cases (hand-built messages, the pad cases, the rejection shapes): 26 of 26 agreements
- Requests with no codes, answered none: 2 of 2
- Random well formed messages: part of 2700 of 2700 agreements in the random run (well formed 1500, raw byte strings 1200)
- Mutations (every truncation, every single byte flip, targeted): 536 of 536 agreements
- Scapy cross checks: 10 of 10 agreements
- Malformed requests answered error: 12 of 12
- Differential inputs: 3274
- Differential agreements: 3274
- Named differences: none
- Failures: 0
