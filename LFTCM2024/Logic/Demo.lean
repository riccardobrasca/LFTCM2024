import Mathlib.Tactic
/-
## LFTCM2024: Logic

This morning you learnt some fundamental tactics like
`rw`, `apply`, `exact`, `have` and `intro`.

To make complex mathematical statements, we need to be able to use logical connectives and
quantifiers. In this session we'll learn how to do that, using the tactics you saw this morning,
and some new ones.

For each logical construction, we need to know two things:
1. how to *use* a statement containing it, like a local hypothesis, or a theorem in the library
2. how to *prove* a statement containing it.

## Tactics we'll use in this section:
(To-do: this list is subject to change)
Tactics we won't really discuss are in brackets.

# `→`, `¬`, `∀`: the function-like logical constructions
· To use: `apply`, `apply _ at _`, `exact`, (`specialize`)
· To prove: `intro`, `push_neg` (for `¬`), (`rintro`)

# `∧`, `↔`, `∃`: inductive propositions with 1 constructor
· To use: `rcases ⟨_, _⟩`, `rw` (for `↔`), (`choose`, `cases`, `cases'`, `obtain`, `match`)
· To prove: `constructor`, `use`, `exact ⟨_, _⟩`

# `∨`: inductive proposition with 2 constructors
· To use: `rcases _ | _`, (`cases`, `cases'`, `match`)
· To prove: `left`, `right`

# Miscellaneous tactics we'll meet
· `exfalso`, `unfold`, `rfl`, `ext`, `by_contra`, `contrapose`
-/

namespace LFTCM2024
section
/-
## Function-like logical constructions: implication, negation, and the universal quantifier

We start with implication statements, `¬` statements and `∀` statements.
All three are kind of similar. -/

/-
# Implication statements

An implication statement is a statement of the form "P implies Q", where `P` and `Q` are
propositions. In Lean this is written as `P → Q`, like a function type; a proof of
`P → Q` behaves like a function too. You can type `→` with `\to`.

This is part of the "propositions-as-types paradigm". Types are where "data" live - `ℕ`
is a type, and it has terms like `0` and `5`. A proposition `P : Prop` is like `ℕ` in that
it can have terms - i.e. proofs - but any 2 "terms of type `P`" are equivalent in Lean,
because it's proof-irrelevant. If a proposition is false, it has no terms.

Treating implication statements (and `¬` and `∀` statements) as like functions can
help you remember how to use them.
-/

/- First let's see how to *use* an implication statement;
you already know how to do this. -/
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  apply hPQ
  exact hP

/-
So we can see `hPQ` as a function that eats a term of type `P` - i.e. a proof - and spits out a
proof of `Q`. You've already seen `apply`; we use it to reason backwards, using `hPQ` to say
"to prove `Q`, it suffices to prove `P`." I guess you could see it as "we're going to make a term
of type `Q` by *applying* the function `hPQ` to an input".

A more intuitive use of the word `apply` is in "`apply _ at _`": this lets us apply an
implication statement to an existing hypothesis - i.e. use forward reasoning.
-/
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  apply hPQ at hP
  exact hP

/-
Next we need to know how to prove an "implies" statement.
-/
lemma one (P Q : Prop) (hQ : Q) : P → Q := by
  intro hP
  exact hQ

/- `intro` lets us introduce assumptions and variables. From a function-y perspective, we're
defining a function from proofs of `P` to proofs of `Q` and saying "let `hP` be any proof of
`P` - we map it to `hQ`." -/

/- Unimportant remark: `intro` is like moving things before the colon, i.e.
lemmas `one` and `two` are proofs of the same proposition. -/
lemma two (P Q : Prop) (hQ : Q) (hP : P) : Q := by
  exact hQ

#check one
#check two -- same output

/- As another example, let's prove transitivity of implication.
There are invisible brackets in the statement of our theorem, because `→` associates to the
right.

We want to define a function that eats a proof of "`P` implies `Q`" and spits out another
function: one that eats a proof of "`Q` implies `R`" and spits out a proof of "`P` implies `R`."
-/
example (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  intro hPQ hQR hP
  apply hQR
  apply hPQ
  exact hP
  --exact hQR (hPQ hP)

/-
# Negation statements

Next we'll look at `False` and negation statements. `False` is defined to be a `Prop` with no
terms. Meanwhile, negation statements are statements beginning with `¬`, which you can type
with `\not`. Given a proposition `P`, `¬ P` is defined to mean `P → False`, so it's an
implication statement in disguise.
-/
example : P → ¬¬ P := by
  intro hP hnotP
  apply hnotP
  exact hP

/- In that example we both used and proved a `¬` statement.
Sometimes we also want to use the fact that any statement follows from `False`. In practice
this shows up when proving a proposition `P` by case-splitting on some condition, since
sometimes we can conclude `P` in a particular case by showing that case can never occur.
To derive another proposition from a proof of `False`, we use the `exfalso` tactic: -/
example (P : Prop) : False → P := by
  intro hFalse
  exfalso
  exact hFalse

/- We'll see more tactics for working with negations when we've introduced more complicated
logical connectives to combine them with. -/

/-
# Universal quantifiers

Now let's move onto universal quantifiers: `∀` statements, typed with `\all`. If an
implication `P → Q` is a bit like a function type, say, `ℕ → ℚ`, then a `∀` statement is
like a dependent function type: a type of functions whose codomain is dependent on the
function input.
For example, we can talk about functions that send a natural number `n : ℕ` to an element
of `ℤ/nℤ`; in Lean we can write the type of such functions via `(n : ℕ) → ZMod n`,
`Π (n : ℕ), ZMod n` or even `∀ n : ℕ, ZMod n`.

We can dress a non-dependent function type like `ℕ → ℚ` as a dependent one: `∀ n : ℕ, ℚ`
means the same thing as `ℕ → ℚ`. So we can expect to be able to treat `∀` statements
similarly to implication statements. -/
/- Likewise, we can dress up an implication statement as a `∀` statement: -/
section

variable (P Q : Prop)
#check ∀ (hP : P), Q -- `P → Q : Prop`

end
/- But quantifying over all proofs of `P` is a bit pointless when they're all equivalent.

Here's a more meaningful `∀` statement:
-/
example : ∀ P : Prop, False → P := by
  intro P hFalse
  exfalso
  exact hFalse
/-
We proved this earlier, except the `P` was before the colon; this time we can use `intro` to
introduce variables `P : Prop` and `hFalse : False` to the local context, so
indeed, proving a `∀` statement is just like proving an implication. Let's quantify
over some different types this time: -/
section
variable {α β γ : Type}

def Injective (f : α → β) : Prop :=
  ∀ x y, f x = f y → x = y

example (f : α → β) (g : β → γ) (hf : Injective f) (hg : Injective g) :
    Injective (g ∘ f) := by
  intro x y hxy
  apply hf
  apply hg
  exact hxy

/-
## Inductive propositions with 1 constructor:
## Conjunction, bi-implication and the existential quantifier
Now for a different group of similar logical connectives:
`∧` (\and), `↔` (\iff) and `∃` (\exists, except you just have to type \ex). The
previous group were all like function types; this group correspond to a different kind of type -
inductive types. In particular they're all inductive propositions with 1
constructor, which is why they behave similarly. It doesn't matter what this means; the
important thing is we can use the same tactics to deal with all 3.

The statements `P ∧ Q` and `P ↔ Q` both represent two pieces of information, and each
side is independent of the other one.

Meanwhile, like `∀`, `∃` is dependent: -/
section
/- Let `P` be a predicate on `α`: -/
variable (α : Type) (P : α → Prop)

#check ∃ x, P x
end
section
/-
# Conjunction
-/
variable (P Q : Prop)

/- Here are some ways to use and prove `∧` statements: -/
example (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.2
  · exact h.1

example (h : P ∧ Q) : Q ∧ P := by
  rcases h with ⟨hP, hQ⟩
  constructor
  · exact hQ
  · exact hP

example (h : P ∧ Q) : Q ∧ P := by
  rcases h with ⟨hP, hQ⟩
  use hQ, hP

example (h : P ∧ Q) : Q ∧ P := by
  rcases h with ⟨hP, hQ⟩
  exact ⟨hQ, hP⟩

/-
# Bi-implication
-/

/- It's exactly the same story for `↔`: -/
example (h : P ↔ Q) : Q ↔ P := by
  constructor
  · exact h.2
  · exact h.1

example (h : P ↔ Q) : Q ↔ P := by
  rcases h with ⟨hP, hQ⟩
  constructor
  · exact hQ
  · exact hP

example (h : P ↔ Q) : Q ↔ P := by
  rcases h with ⟨hP, hQ⟩
  use hQ, hP

example (h : P ↔ Q) : Q ↔ P := by
  rcases h with ⟨hP, hQ⟩
  exact ⟨hQ, hP⟩

/- However, `↔` leads a double life - it also behaves just like `=`, meaning we
can `rw` `↔` statements the way we can `rw` equalities. -/
example (hPQ : P ↔ Q) (hQR : Q ↔ R) : P ↔ R := by
  rw [hPQ, hQR]

/-
# Existential quantifiers
-/

/- We can use an `∃` statement by deconstructing it and replacing `∃ x, P x` with a
term `x : α` and a hypothesis `hx : P x`. -/
example (α : Type) (P : α → Prop) (h : ∃ x, P x) : ¬ (∀ x, ¬ P x) := by
  intro hnot
  rcases h with ⟨x, hx⟩
  apply hnot x
  exact hx
  -- exact hnot x hx

example (α : Type) (P Q : α → Prop) (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by
  rcases h with ⟨x, hPx, hQx⟩
  use x, hQx, hPx

example (α : Type) (P Q : α → Prop) (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by
  rcases h with ⟨x, ⟨hPx, hQx⟩⟩
  exact ⟨x, hQx, hPx⟩

example (α : Type) (P Q : α → Prop) (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by
  rcases h with ⟨x, ⟨hPx, hQx⟩⟩
  constructor
  · exact ⟨hQx, hPx⟩

example (α : Type) (P Q : α → Prop) (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by
  choose x hPx hQx using h
  constructor
  · exact ⟨hQx, hPx⟩

/-
As before, the tactics we're using can see underneath definitions (unlike `rw`):
-/
def Surjective {α β : Type} (f : α → β) : Prop :=
  ∀ x, ∃ y, f y = x

example {α β γ : Type} (f : α → β) (g : β → γ) (hf : Surjective f)
    (hg : Surjective g) : Surjective (g ∘ f) := by
  unfold Surjective at *
  intro x
  rcases hg x with ⟨z, hz⟩
  rcases hf z with ⟨y, hy⟩
  use y
  rw [← hz, ← hy]
  rfl

/- `rfl` proves definitional equalities; i.e. it succeeds when both sides
  are equal by definition. -/

/- We can shorten this using the "`rfl` trick": because `hy` and `hz` are equalities, if
we name them `rfl`, they automatically get rewritten wherever possible in the local context: -/
example {α β γ : Type} (f : α → β) (g : β → γ) (hf : Surjective f)
    (hg : Surjective g) : Surjective (g ∘ f) := by
  intro x
  rcases hg x with ⟨y, rfl⟩
  rcases hf y with ⟨z, rfl⟩
  use z
  rfl

/-
# Inductive propositions with 2 constructors: Disjunction
Final logical connective: `∨` (type `\or`). This is a little like the previous
group, in that `∨` is an inductive type, but instead of one constructor with 2 pieces
of information, `∨` has two constructors: you can prove `P ∨ Q` either by proving
`P` or proving `Q`.
-/

example (h : P ∨ Q) : Q ∨ P := by
  rcases h with hP | hQ
/- Now there are 2 goals. -/
  · right
    exact hP
  · left
    exact hQ

/- Since `↔` behaves like `=`, `rfl` can also prove this: -/
lemma dvd_def {m n : ℕ} : m ∣ n ↔ ∃ a, n = m * a := by
  rfl

/- By combining the 2nd group of logical constructions and `∨` we can start to see the power of
`rcases`: -/
example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  simp_all only [dvd_def] -- a tactic for next session, but we don't really need it here
  rcases h with ⟨a, ha⟩ | ⟨b, hb⟩
  · use a * k
    rw [ha, mul_assoc]
  . use b * n
    rw [mul_comm, hb, mul_assoc]

end
