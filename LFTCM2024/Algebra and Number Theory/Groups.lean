import Mathlib

section Groups

variable {G H : Type*} [Group G]


/-The first one is showing that a group of exponent two is commutative.The usual proof is
to begin with the equation (g * h) * (g * h) = 1, and then multiply on the right by h, to get
g * h * g = h, now multiply on the right by g and you get the result.
-/
lemma exp_two_comm (hG : ∀ g : G, g * g = 1) :  ∀ g h : G, g * h = h * g := by
    intro g h --there are definitely shorter proofs, but this one maximizes the amount of lean-ing you do.
    have j :  g * h * g * h = 1 := by sorry
    have l : g * h * g = g * h * (g * h) * h := by sorry
    have m : g * h * g = h := by sorry
    sorry --I'll let you finish this one. You might also want to look at `calc` to maybe make it shorter.


/-Here is construction of a group homomorphism given by the inverse map.
you can actually strengthen this to get that if this is a homomorphism,
then the group is commutative. But I'll leave that for you to play with. -/

def inv_grp_hom [CommGroup H]: H →* H where
  toFun g :=  g⁻¹
  map_one' := by sorry
  map_mul' := by
    simp
    intro x y
    sorry --here is where you need commutativity of the group. Look at `mul_comm`.
