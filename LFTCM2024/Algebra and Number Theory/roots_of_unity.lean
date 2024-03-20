import Mathlib.NumberTheory.Cyclotomic.Basic


open scoped NumberField BigOperators

variable {F : Type*} [Field F] [NumberField F] (ζ : 𝓞 F) (n : ℕ)


--First lets look at the two defining properties of a primitive root
example (h : IsPrimitiveRoot ζ n) : ζ ^ n = 1 := by exact h.pow_eq_one

example (h : IsPrimitiveRoot ζ n) : ∀ l : ℕ, ζ ^ l = 1 → n ∣ l := by exact h.dvd_of_pow_eq_one

example :  IsPrimitiveRoot ζ 1 ↔ ζ = 1 := by exact IsPrimitiveRoot.one_right_iff

/- Next lets look at geometric sums. Note that we have  `geom_sum_mul_neg` which says
(∑ i in Finset.range n, x ^ i) * (1 - x) = 1 - x ^ n, so we can use this to check the sum divides
the rhs  -/
lemma geo_sum_dvd (j : ℕ) : (∑ i in Finset.range j , ζ ^ i) ∣ 1 - ζ ^ j := by
  rw [← geom_sum_mul_neg]
  sorry

-- % is the remainder operator
example : 5 % 2 = 1 := by norm_num

--we can use it to find inverses modulo n, we'll need this later
lemma coprime_exists_inverse {n j : ℕ} (h : j.Coprime n) (hn: 1 < n) : ∃ k : ℕ, j * k % n = 1 := by
  exact  Nat.exists_mul_emod_eq_one_of_coprime h hn

/-Associated is defined quite generally: Two elements of a `Monoid` are `Associated` if one of them is another one
multiplied by a unit on the right. For what follows, we will use equivalence of the definition
in terms of mutual divisibility see `dvd_dvd_iff_associated`

 Its stated in a weird way, with this Coprime to 0 thing, but its to make it uniform later.
-/

lemma associated_case_0 (j : ℕ) (hj : j.Coprime 0) : Associated (1 - ζ ) (1 - ζ ^ j) := by
  -- you may want to use `Nat.coprime_zero_right`
  sorry

--use that 1-th primitive roots are 1 and then associated_zero_iff_eq_zero
lemma associated_case_1 (j : ℕ) (h : IsPrimitiveRoot ζ 1) :
    Associated (1 - ζ ) (1 - ζ ^ j) := by
  --look at `IsPrimitiveRoot.one_right_iff`
  sorry


/-Lets check that (1 - ζ ) and  (1 - ζ ^ j) are associated -/
theorem associated_one_sub_pow_primitive_root_of_coprime {n j : ℕ} (h : IsPrimitiveRoot ζ n)
  (hj : j.Coprime n) : Associated (1 - ζ ) (1 - ζ ^ j) := by
  refine' associated_of_dvd_dvd ⟨∑ i in Finset.range j, ζ ^ i, by rw [← geom_sum_mul_neg, mul_comm]⟩ _
  rcases eq_or_ne n 0 with (rfl | hn')
  · sorry
  /-now do the n = 1 or n > 1 case. For the n > 1 case, find the inverse of j modulo n and use
  ∑ i in Finset.range m, (ζ ^ j) ^ i where m is the inverse.
  -/
  sorry


/-Using the above we can then do the general case-/
theorem associated_one_sub_pow_primitive_root_of_coprime_gen {n j k : ℕ} (h : IsPrimitiveRoot ζ n)
  (hk : k.Coprime n) (hj : j.Coprime n) : Associated (1 - ζ ^ j) (1 - ζ ^ k) := by
  suffices ∀ {j : ℕ}, j.Coprime n → Associated (1 - ζ) (1 - ζ ^ j) by
    sorry
  exact associated_one_sub_pow_primitive_root_of_coprime ζ h
