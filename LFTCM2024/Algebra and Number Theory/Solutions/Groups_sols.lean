import Mathlib

section Groups

variable {G H : Type*} [Group G]


/-The first one is showing that a group of exponent two is commutative.The usual proof is
to begin with the equation (g * h) * (g * h) = 1, and then multiply on the right by h, to get
g * h * g = h, now multiply on the right by g and you get the result.
-/
lemma exp_two_comm (hG : ∀ g : G, g * g = 1) :  ∀ g h : G, g * h = h * g := by
    intro g h --there are definitely shorter proofs, but this one maximizes the amount of lean-ing you do.
    have j : (g * h) * (g * h) = 1 := by
      apply hG
    have l : g * h * g = g * h * (g * h) * h := by
      rw [← mul_assoc]
      have w : g * h * g * h * h = g * h * g * (h * h) := by
        rw [← mul_assoc]
      rw [w, hG, mul_one]
    have m : g* h * g = h := by
      rw [l, j, one_mul]
    have n : g* h * g* g = h * g := by
      rw [m]
    have p : g * h = g * h * g * g := by
      rw [mul_assoc, hG, mul_one]
    rw [p, n ]


/-Here is construction of a group homomorphism given by the inverse map.
you can actually strengthen this to get that if this is a homomorphism,
then the group is commutative. But I'll leave that for you to play with. -/

def inv_grp_hom [CommGroup H]: H →* H where
  toFun g :=  g⁻¹
  map_one' := by simp
  map_mul' := by
    simp
    intro x y
    apply mul_comm
