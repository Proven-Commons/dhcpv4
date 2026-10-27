# dhcpv4

A Lean parser for DHCPv4 wire messages. This is a Proven Commons project: it rebuilds a widely used format in Lean and proves the new code follows its written specification.

Status: not verified. No code has landed yet. Plan issue 1 holds the first slice, and it is unclaimed. The specification has not been approved by a reviewer, so do not call this verified.

## First slice

DHCPv4 messages, with the RFC 2131 header of 236 fixed bytes plus options as type length value items from RFC 2132. Message types DISCOVER, OFFER, REQUEST, ACK, NAK, DECLINE, RELEASE, and INFORM. Option 53, the message type, is required. End option and padding are handled.

This is distinct from the dns repo and the ip repo. Both are different message formats. This repo assigns addresses. The ip repo parses addresses.

## Main claim

Decoding a message gives the same fields back. An option length that runs past the end of the message is rejected. A message without option 53 is rejected.

## Test oracles

- ISC DHCP and dnsmasq captures.
- The Scapy packet builder.
- Wireshark dissectors.

No single standard test corpus covers option edge cases, so captures must be assembled. That is recorded here, not hidden.

## Score

15 out of 18, first pass score in mission issue 19, the round 4 sheet. Created at the org owner's direction on that sheet, on the judgement that the slice, claim, and oracles are sound and that it duplicates no existing repo.

## What is not in this slice

- Lease state.
- Relay agent handling.
- DHCPv6.

## Layout, when the first slice lands

The layout follows the Proven Commons template in the mission repo, under bar/template. Spec.lean holds the statements a reviewer approves. Proofs.lean holds the proofs under the same names. Main.lean holds the command line tool used by the tests. The bar check runs in CI on every change.
