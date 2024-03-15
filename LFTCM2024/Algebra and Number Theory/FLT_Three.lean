import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Int.Parity
import Mathlib.RingTheory.Int.Basic


/- Here are some examples of working with ℕ and ℤ in mathlib, the idea is to prove a bit of the
descent step used in the n=3 case. -/

/-We have gcd's. They take two integers and return the gcd and a natural number, if you go and look
at Std.Data.Int.Gcd you'll see some lemmas about this. Try and find the results for the following
or try `apply?`

Divides is defined for integers as a ∣ b to mean there is some c such that a * c = b. This operation
is called dvd in mathlib. -/

example (a b : ℤ) (h : a ∣ b) : ∃ c, b = a * c := by
  obtain ⟨c, hc⟩ := h
  use c

lemma gcd_lem_1 (a b : ℤ) : (Int.gcd a b : ℤ) ∣ a ∧ (Int.gcd a b : ℤ) ∣ b := by
    --Beware you need to use \| to get the ∣ symbol
  constructor
  exact Int.gcd_dvd_left
  sorry

/- If something divides two numbers then it divides their sum -/
lemma dvd_lem (a b c d : ℤ) (ha : d ∣ a) (hb : d ∣ b) (hab : a + b = c) : d ∣ c := by
  rw [← hab]
  sorry

/-We can also deal with powers, using `Int.pow_dvd_pow_iff` in the next one might be useful -/
lemma gcd_lem_2 (a b c d: ℤ) (k : ℕ) (hk : 0 < k) (ha : d ∣ a) (hb : d ∣ b)
    (hab : a ^ k + b ^ k = c ^ k) : d ∣ c := by
  obtain ⟨A, HA⟩  := ha
  sorry

/- Here is a small lemma you might need below-/
lemma ne_zero_lem (a b c : ℤ) (ha : a ≠ 0) (habc : a = b * c) : b ≠ 0 := by
  sorry

/-First we can check what happens if the tripple is not assumed to be coprime. In this case we can
divide out the by gcd and get a smaller solution

One way to do this is to use gcd_lem_1 and _2 to get the gcd divides a,b,c and then divide out by the gcd
To divide out, you can write a= d A, b = d B, c = d C (with d the gcd) and then divide out by d^k to get
and equation wrt A B and C.

-/
theorem exists_smaller_sol_if_not_coprime {n : ℕ} (hn : 0 < n) {a b c : ℤ} (ha' : a ≠ 0)
    (h : a ^ n + b ^ n = c ^ n) :
    ∃ a' b' c' : ℤ, a' ≠ 0 ∧ a'.natAbs ≤ a.natAbs ∧ a' ^ n + b' ^ n = c' ^ n :=
  by
  set d := Int.gcd a b
  obtain ⟨A, HA⟩ : ↑d ∣ a := @Int.gcd_dvd_left a b
  --repeat this for b and c

  have hd : d ≠ 0  := sorry --you might need this to get a' ≠ 0

  have HA' : A.natAbs ≤ a.natAbs := by sorry
  sorry



/- We can basically use the same proof to make the result stronger. In this case you could simply
prove the result in the stronger form and remove the weaker one, or use the one above to prove this, but that might be tricky
-/
theorem coprime_full {n : ℕ} (hn : 0 < n) {a b c : ℤ} (ha' : a ≠ 0) (hb' : b ≠ 0) (hc' : c ≠ 0)
    (h : a ^ n + b ^ n = c ^ n) :
    ∃ a' b' c' : ℤ, a' ≠ 0 ∧  b' ≠ 0 ∧ c' ≠ 0 ∧
      a'.natAbs ≤ a.natAbs ∧ b'.natAbs ≤ b.natAbs ∧ c'.natAbs ≤ c.natAbs ∧ a' ^ n + b' ^ n = c' ^ n  := by
    sorry
    --copy the proof of the above one and just add the b and c parts
