import EuclidElements.Book1.Proposition01

/-!
# Axiom/dependency audit for Proposition I.1

Because the geometry, explicit postulates, and hidden assumptions are passed as
parameters/typeclasses rather than declared as global Lean axioms, the theorem
is model-parametric.  This file asks Lean to print the theorem and its kernel
axiom dependencies when compiled interactively.
-/


#print Euclid.Book1.proposition1_construction
#print Euclid.Book1.proposition1
#print axioms Euclid.Book1.proposition1_construction
#print axioms Euclid.Book1.proposition1
