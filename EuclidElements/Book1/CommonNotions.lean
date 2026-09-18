/-!
# Euclid Book I: Common Notions 1--5

Euclid states the Common Notions for arbitrary magnitudes, not only segments.
This file therefore gives a generic formal language for magnitudes.  Concrete
geometric congruence laws used in Book I are recorded separately in
`ImplicitAxioms.lean`, because segment addition/subtraction requires additional
incidence and order structure.
-/

namespace Euclid.Book1

/-- A minimal abstract language in which Euclid's five Common Notions can be stated. -/
structure MagnitudeLanguage where
  Magnitude : Type
  equal : Magnitude → Magnitude → Prop
  add : Magnitude → Magnitude → Magnitude
  subtract : Magnitude → Magnitude → Magnitude
  coincides : Magnitude → Magnitude → Prop
  properPart : Magnitude → Magnitude → Prop
  less : Magnitude → Magnitude → Prop

/-- Euclid's five Common Notions, stated abstractly for magnitudes. -/
class CommonNotions (M : MagnitudeLanguage) : Prop where
  /-- CN1: Things equal to the same thing are equal to one another. -/
  cn1 : ∀ {a b c : M.Magnitude}, M.equal a b → M.equal b c → M.equal a c

  /-- CN2: If equals are added to equals, the wholes are equal. -/
  cn2 : ∀ {a b c d : M.Magnitude},
    M.equal a b → M.equal c d →
    M.equal (M.add a c) (M.add b d)

  /-- CN3: If equals are subtracted from equals, the remainders are equal. -/
  cn3 : ∀ {a b c d : M.Magnitude},
    M.equal a b → M.equal c d →
    M.equal (M.subtract a c) (M.subtract b d)

  /-- CN4: Things which coincide with one another are equal to one another. -/
  cn4 : ∀ {a b : M.Magnitude}, M.coincides a b → M.equal a b

  /-- CN5: The whole is greater than the part. -/
  cn5 : ∀ {part whole : M.Magnitude},
    M.properPart part whole → M.less part whole

end Euclid.Book1
