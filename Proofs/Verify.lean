/-
  Axiom check for the round trips, the soundness theorem,
  and the statement of which inputs the parser takes.
  Building this file prints the axioms the proofs depend on.
  The expected output is only the three standard Lean axioms:
  `propext`, `Classical.choice`, `Quot.sound`, or a subset of
  them. Any other name here breaks the verified bar.
-/

import Proofs.RoundTrip
import Proofs.Accept

#print axioms Dhcp.Proofs.parse_print
#print axioms Dhcp.Proofs.print_parse
#print axioms Dhcp.Proofs.parse_wf
#print axioms Dhcp.Proofs.parse_accepts_iff
