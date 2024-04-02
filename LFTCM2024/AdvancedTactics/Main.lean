/-
LFTCM 2024: Advanced Tactics
-/

import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

open scoped NNReal

/-
`refine`: apply with holes

`refine` is a tactic like apply, where one can apply a lemma or hypothesis to the goal, but
leaving some of the lemma's hypotheses as new goals to be proven afterwards.
-/

section refine
open Real

/- In mathlib, we have (more general versions of) the following:
`lemma Continuous.add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) : Continuous (f + g)`
-/

example : Continuous (sin + cos) := by
  /- To prove this, the natural thing to do is to first use the above lemma, and then afterwards
  deal with the fact that cos and sin are individually continuous. -/
  refine Continuous.add ?_ ?_
  · exact continuous_sin  -- can be found using `exact?`
  · exact continuous_cos

/- We can name the holes -/
example : Continuous (sin + cos) := by
  /- To prove this, the natural thing to do is to first use the above lemma, and then afterwards
  deal with the fact that cos and sin are individually continuous. -/
  refine Continuous.add ?sin ?cos
  case sin =>
    exact continuous_sin
  case cos =>
    exact continuous_cos

end refine


/-
`simp`: the simplifier

`simp` is basically "`rw` on autopilot". It has a set of lemmas it is allowed to use
(the "simp-set"), and it tries to rewrite the goal (or a hypothesis) repeatedly using these lemmas
until it can no longer do so.

The simp-set in constructed in two ways: lemmas can be passed explicitly to simp in the tactic call,
and lemmas in the library (or your code) can be tagged with `@[simp]` to include them automatically
in the simp-set.

It can be called in various ways:
- `simp` uses the default simp-set (i.e. lemmas tagged with `@[simp]`) on the goal
- `simp only [foo, bar]` uses only `foo` and `bar` in its simp-set, not the lemmas tagged with
  `@[simp]`. This is often nearly the same as `rw [foo, bar]`, but the simp-set is not ordered.
- `simp [foo, bar]` uses the default simp-set plus `foo` and `bar`.
- `simp at h` calls simp at the hypothesis `h` rather than the goal.
- `simp [-foo]` *removes* `foo` from the simp-set
-/

section simp

open Real

/- Let's use trigonometric functions for the example. We have the following in mathlib:

@[simp] lemma sin_zero : sin 0 = 0 := ...
@[simp] lemma add_zero : x + 0 = x := ...
-/

example (x : ℝ) : x + sin 0 = x := by
  rw [sin_zero, add_zero]

/- Note that the rewrites are ordered, this doesn't work -/
example (x : ℝ) : x + sin 0 = x := by
  rw [add_zero, sin_zero]

/- Let's do it with simp -/
example (x : ℝ) : x + sin 0 = x := by
  simp only [add_zero, sin_zero]

/- Since the relevant lemmas are already tagged... -/
example (x : ℝ) : x + sin 0 = x := by simp

/-
Note that simp rewrites *from left to right*, so one should only tag lemmas with `@[simp]` when
going from left to right constitutes a clear simplification of the expression.
-/

/- This would be a very bad simp lemma -/
lemma zero_eq_sin_zero : 0 = sin 0 := sin_zero.symm

/- Let's see what happens when we try to use it -/
example (x : ℝ) : x + sin 0 = x := by
  simp only [zero_eq_sin_zero]   -- maximum recursion depth has been reached: not good...
  -- Internally, it will rewrite `sin 0` to `sin (sin 0)` to `sin (sin (sin 0))` and so on.
  sorry

/- Even worse, if we just *add* this lemma to an already working simp set, it pollutes it
and makes simp fail: -/
example (x : ℝ) : x + sin 0 = x := by
  simp [zero_eq_sin_zero]  -- fails, despite the fact that `sin_zero` and `add_zero` are still there
  sorry

/- We can add a lemma in the reverse direction, like for `rw` -/
example (x : ℝ) : x + sin 0 = x := by
  simp only [← zero_eq_sin_zero, add_zero]

/- We can add arguments to lemmas -/
example (x : ℝ) (h : 1 + x = 0) : x + 1 = 0 := by
  --simp [add_comm, h]  -- fails
  simp [add_comm x, h]  -- succeeds!

/- We can use `simp` on a hypothesis -/
example (x : ℝ) (h : 1 + x = 0) : x + 1 = 0 := by
  simp only [add_comm (1 : ℝ)] at h
  exact h

/- We can also use simp to unfold definitions -/
def myFunc (x : ℝ) := x

example : sin (myFunc 0) = 0 := by
  -- simp    -- simp by itself doesn't work, since `myFunc` is not unfolded by default
  simp only [myFunc]    -- This replaces `myFunc x` with its definition
  simp  -- Finishes the job

/- Of course this also works -/
example : sin (myFunc 0) = 0 := by simp [myFunc]

/- Another difference between `rw` and `simp` is that `simp` can rewrite under binders -/

example : ∀ (x : ℕ), x + x = 2 * x := by
  -- rw [two_mul]    -- fails because of the `∀`
  simp only [two_mul]
  -- Left with `ℕ → True`, which is the same as `∀ (n : ℕ), True`
  intro x
  trivial
  -- another option is to use `simp_rw`
  -- Left with `ℕ → True`, which is the same as `∀ (n : ℕ), True`
  --simp_rw [two_mul]

/- `simp_rw` is basically the same `rw` (i.e. it applies lemmas in order), except that it
uses the `simp` engine internally and can rewrite under binders. -/

end simp

/-
Coercions/casting

In informal math, we can say things like `ℚ ⊆ ℝ`, but in Lean these are distinct types,
and an element of `ℚ` is *not* a real number. However, it can be coerced to a real. If
we have a variable `x` of type `ℚ`, we can write `(x : ℝ)` to view it as a real.

This can cause some pain, because these coercions can get in the way.
-/

section cast

example (x : ℚ) (y : ℤ) (h : x + y = (0 : ℝ)) : x + y = 0 := by
  -- exact h    -- doesn't work, wrong type
  exact_mod_cast h

-- The problem can show up even without explicit casting
example (x : ℚ) (y z : ℤ) (h : y + z = 1) : y + z + x = 1 + x := by
  -- rw [h]   -- doesn't work
  rw_mod_cast [h]
  simp

/- Other useful tactics to deal with casting: `norm_cast`, `push_cast` -/

end cast

/-
`ring`, `group`, `abel`: domain-specific simplification

Suppose we have an expression like `x + y + z - x - 3y + z`. Clearly this should be easy to
show that this is equal to `-2*y + 2*z`, but very annoying to do using tactics seen so far.
-/

section ring
variable {x y z : ℝ}

example : x + 3 * y + z - x - y + z = 2 * y + 2 * z := by
  rw [add_comm x, add_assoc, add_comm x z, ← add_assoc, add_sub_assoc, sub_self, add_zero]
  -- Finally cancelled out the `x - x`!
  --simp   -- simp made no progress -- come on!!
  -- please make it stop
  ring

example : x + 3 * y + z - x - y + z = 2 * y + 2 * z := by ring

example : (x + y) * (x - y) = x^2 - y^2 := by
  ring

/- This works for commutative rings; there's also `abel` which works in a slightly more
general setting but is usually a bit less powerful. `group` works for groups.

These tactics basically work by turning the expressions into a normal form.
-/

example {R : Type*} [Ring R] (x y z : R) :
    x + y + z - y - x = z := by
  -- ring   -- ironically doesn't do anything: `R` is not commutative
  abel
  -- I had to simplify the example, `abel` doesn't deal well with things like `3 : R`

end ring

/-
`norm_num`: dealing with numerical calculations

This is a tactic that simplifies numerical expressions. It works internally using a system of
plugins that tell it how to compute particular functions applies to numeric literals.
-/

example : (1 : ℝ) + 1 = 2 := by
  -- simp    -- simp fails (already a bit embarrassing)
  -- exact?  -- finds a lemma specific to 1+1, or times out
  norm_num

example : 5 ∣ 10 := by
  -- simp    -- simp again fails
  -- exact?  -- I will pay a beer to anyone who sees this coming
             -- (unless it times out, no beer for this outcome)
  norm_num

/-
`linarith`: dealing with systems of linear inequalities

This is a tactic that can make deductions based on a set of linear inequalities in the
context. Uses Fourier-Motzkin elimination.
-/

section linarith

example (x y z : ℝ) (h1 : x + y + z ≤ 15) (h2 : 10 ≤ x + y) : z ≤ 5 := by linarith

/- It can also handle equality constraints and/or goals -/

example (x y z : ℝ) (h1 : x + y + z = 15) (h2 : 10 ≤ x + y) : z ≤ 5 := by linarith
example (x y z : ℝ) (h1 : x + y + z = 15) (h2 : 10 = x + y) : z = 5 := by linarith

/- It won't really do anything else, to make sure it works, everything relevant
has to be in the context -/
example (x : ℝ) : 0 ≤ ‖x‖ := by linarith

/- It doesn't just work for reals, it can deal with any linearly-ordered commutative
ring -/

example {R : Type*} [LinearOrderedCommRing R] (x y z : R)
  (h1 : x + y + z ≤ 15) (h2 : 10 ≤ x + y) : z ≤ 5 := by linarith

/- So it will fail for i.e. non-negative reals -/

example (x y z : ℝ≥0) (h1 : x + y + z ≤ 15) (h2 : 10 ≤ x + y) : z ≤ 5 := by linarith

/- It also has to be linear -/

example (x : ℝ) : 0 ≤ x ^ 2 := by linarith

/- There's a souped-up version called `nlinarith` that can solve some nonlinear problems -/
example (x : ℝ) : 0 ≤ x ^ 2 := by nlinarith

end linarith

/-
`omega`: like `linarith` for integers

If you're dealing with integers, natural numbers, `Fin n`, there is another similar
tactic called `omega`.

It automatically uses things like `0 ≤ n` for any `n : ℕ`, or that `x < y` is equivalent to
`x + 1 ≤ y`.
-/

example (x y z : ℕ) (h1 : x + y + z = 15) (h2 : 10 < x + y) : z + 1 ≤ 5 := by omega

/- For the computer scientists in the room, this tactic is actually in Lean core and
is used to check array bounds automatically, and to automatically prove termination of
recursive functions. -/

def ackermann (m n : ℕ) : ℕ :=
  match m, n with
  | 0, _            => n + 1
  | m' + 1, 0       => ackermann m' 1
  | m' + 1, n' + 1  => ackermann m' (ackermann (m' + 1) n')

/-
`positivity`: Proving that an expression is positive/nonnegative/nonzero

It is often the case that one can deduce that an expression is "obviously positive" just from
its structure. Example: `x + y` if `x` and `y` are both positive.

It works using a plugin system, where each plugin is a small program that can prove that an
expression of a particular form (say, `exp x`) is positive/nonnegative/nonzero.
-/

section positivity

open Real

example (x y z w : ℝ) (h : 0 ≤ w) : 0 < ‖x‖ + exp y + z ^ 2 + w := by
  -- simp   -- simp modifies the expression but doesn't really make headway
  positivity

end positivity

/-
`calc` blocks: sequences of equalities/inequalities
-/

example (h₁ : x ≤ 5) (h₂ : y = 10) : x + y ≤ 15 := by
  calc x + y = x + 10 := by rw [h₂]
    _ ≤ 5 + 10 := by exact Nat.add_le_add h₁ le_rfl
    _ = 15 := by norm_num

/-
`gcongr`: working with inequalities (and other relations)

Suppose we need to prove that `f x ≤ f y` where `f` here could be a complicated expression which
is monotone in its argument. So we want to reduce this to showing that x ≤ y. Here `gcongr` very often
helps.

It works by tagging relevant lemmas in the library, and these are then applied to reduce the goal
to what we want.
-/

section gcongr
open Real

example (x y : ℝ) (h : y ≤ x) : sin x + y ≤ 1 + x := by
  calc sin x + y ≤ 1 + y := by
              gcongr
              -- Here the relevant lemma was `add_le_add_right`, which states that
              -- `a + c ≤ b + c` (with the relevant hypotheses). This lemma is tagged
              -- with `@[gcongr]`, similar to the `@[simp]` tag.

              -- Now we are left with `sin x ≤ 1`: surely that's in mathlib!
              -- exact?
              exact sin_le_one x
    _ ≤ 1 + x := by
              -- gcongr can also finish the job with hypotheses in the context
              gcongr

end gcongr

/- `conv`: Zooming in to an expression.

Sometimes we have a big expression, and we'd like to "zoom in" on part of it and apply
tactics only to that part. To do this:
1. Use `conv?`
2. Click on the subexpression you want to zoom into
3. Click "Generate conv"
4. Profit
 -/

section conv

open Real

example (x y z : ℝ) (h : sin (x + y) + cos (z + x) = 1) :
    sin (x + y) + cos (x + z) = 1 := by
  --conv?
  conv =>
    enter [1, 2, 1]
    rw [add_comm]
  exact h

end conv
