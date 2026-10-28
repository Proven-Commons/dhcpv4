/-
  Axiom check for the headline theorems. Building this file prints
  the axioms the proofs depend on. The expected output is only
  the three standard Lean axioms: `propext`, `Classical.choice`,
  `Quot.sound`, or a subset of them. Any other name here breaks
  the verified bar.
-/

import Proofs.RoundTrip

#print axioms Dhcp.Proofs.parse_print
#print axioms Dhcp.Proofs.print_parse
