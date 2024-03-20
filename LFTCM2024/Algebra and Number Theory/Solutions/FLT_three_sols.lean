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
  exact Int.gcd_dvd_right (a := a) (b := b) -- its not necessary to specify the a and b, but this is how you do it

/- If something divides two numbers then it divides their sum -/
lemma dvd_lem (a b c d : ℤ) (ha : d ∣ a) (hb : d ∣ b) (hab : a + b = c) : d ∣ c := by
  rw [← hab]
  exact dvd_add ha hb

/-We can also deal with powers, using `Int.pow_dvd_pow_iff` in the next one might be useful -/
lemma gcd_lem_2 (a b c d: ℤ) (k : ℕ) (hk : 0 < k) (ha : d ∣ a) (hb : d ∣ b)
    (hab : a ^ k + b ^ k = c ^ k) : d ∣ c := by
  obtain ⟨A, HA⟩  := ha
  obtain ⟨B, HB⟩  := hb
  rw [← Int.pow_dvd_pow_iff hk, ← hab, HA, HB, mul_pow, mul_pow, ← mul_add]
  exact dvd_mul_right _ _

/- Here is a small lemma you might need below-/
lemma ne_zero_lem (a b c : ℤ) (ha : a ≠ 0) (habc : a = b * c) : b ≠ 0 := by
  intro hb
  rw [hb, zero_mul] at habc
  exact ha habc

/-First we can check what happens if the triple is not assumed to be coprime. In this case we can
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
  obtain ⟨B, HB⟩ : ↑d ∣ b := @Int.gcd_dvd_right a b
  obtain ⟨C, HC⟩ : ↑d ∣ c :=
    by
    rw [← Int.pow_dvd_pow_iff hn, ← h, HA, HB, mul_pow, mul_pow, ← mul_add]
    exact dvd_mul_right _ _
  have hdpos : 0 < d := Int.gcd_pos_of_ne_zero_left _ ha'
  have hd := Int.coe_nat_ne_zero_iff_pos.mpr hdpos
  have hsoln : A ^ n + B ^ n = C ^ n :=
    by
    apply Int.eq_of_mul_eq_mul_left (pow_ne_zero n hd)
    simp only [mul_add, ← mul_pow, ← HA, ← HB, ← HC, h]
  have HA' : A.natAbs ≤ a.natAbs := by
    rw [HA]
    simp only [Int.natAbs_ofNat, Int.natAbs_mul]
    exact le_mul_of_one_le_left' (Nat.succ_le_iff.mpr hdpos)
  refine ⟨A, B, C, ?_⟩
  constructor
  · have := ne_zero_lem a A d ha' --note this isn't quite what we need, so in practice its better to go back up and restate the lemma to get exactly what you need.
    apply this
    rw [HA]
    ring
  constructor
  exact HA'
  exact hsoln


/- We can basically use the same proof to make the result stronger. In this case you could simply
prove the result in the stronger form and remove the weaker one, or use the one above to prove this, but that might be tricky
-/
theorem coprime_full {n : ℕ} (hn : 0 < n) {a b c : ℤ} (ha' : a ≠ 0) (hb' : b ≠ 0) (hc' : c ≠ 0)
    (h : a ^ n + b ^ n = c ^ n) :
    ∃ a' b' c' : ℤ, a' ≠ 0 ∧  b' ≠ 0 ∧ c' ≠ 0 ∧
      a'.natAbs ≤ a.natAbs ∧ b'.natAbs ≤ b.natAbs ∧ c'.natAbs ≤ c.natAbs ∧ a' ^ n + b' ^ n = c' ^ n  := by
    set d := Int.gcd a b
    obtain ⟨A, HA⟩ : ↑d ∣ a := @Int.gcd_dvd_left a b
    obtain ⟨B, HB⟩ : ↑d ∣ b := @Int.gcd_dvd_right a b
    obtain ⟨C, HC⟩ : ↑d ∣ c := gcd_lem_2 a b c d n hn (@Int.gcd_dvd_left a b) (@Int.gcd_dvd_right a b) h
    have hdpos : 0 < d := Int.gcd_pos_of_ne_zero_left _ ha'
    have hd := Int.coe_nat_ne_zero_iff_pos.mpr hdpos
    have hsoln : A ^ n + B ^ n = C ^ n :=
      by
      apply Int.eq_of_mul_eq_mul_left (pow_ne_zero n hd)
      simp only [mul_add, ← mul_pow, ← HA, ← HB, ← HC, h]
    have HA' : A.natAbs ≤ a.natAbs := by
      rw [HA]
      simp only [Int.natAbs_ofNat, Int.natAbs_mul]
      exact le_mul_of_one_le_left' (Nat.succ_le_iff.mpr hdpos)
    have HB' : B.natAbs ≤ b.natAbs := by
      rw [HB]
      simp only [Int.natAbs_ofNat, Int.natAbs_mul]
      exact le_mul_of_one_le_left' (Nat.succ_le_iff.mpr hdpos)
    have HC' : C.natAbs ≤ c.natAbs := by
      rw [HC]
      simp only [Int.natAbs_ofNat, Int.natAbs_mul]
      exact le_mul_of_one_le_left' (Nat.succ_le_iff.mpr hdpos)
    exact
      ⟨A, B, C,
        right_ne_zero_of_mul (by rwa [HA] at ha'), right_ne_zero_of_mul (by rwa [HB] at hb'),
          right_ne_zero_of_mul (by rwa [HC] at hc'), HA', HB', HC', hsoln,⟩
