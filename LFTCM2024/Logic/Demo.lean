import Mathlib.Tactic
/-
## LFTCM2024: Logic

This morning you learnt some fundamental tactics like
`rw`, `apply`, `exact`, `have` and `intro`.

To make complex mathematical statements, we need to be
able to use logical connectives and quantifiers. In this session
we'll learn how to do that, using the tactics you saw this morning,
and some new ones.

For each logical construction, we need to know two things:
1. how to *use* a statement containing it, like a local hypothesis,
or a theorem in the library
2. how to *prove* a statement containing it.

## Tactics we'll use in this section:
Tactics we won't really discuss are in brackets.

# `→`, `¬`, `∀`: the function-like logical constructions
· To use: `apply`, `apply _ at _`, `exact`, `specialize`
· To prove: `intro`, `push_neg` (for `¬`), `rintro`

# `∧`, `↔`, `∃`: inductive propositions with 1 constructor
· To use: `rcases ⟨_, _⟩`, `rw` (for `↔`), (`choose`, `cases`,
  `cases'`, `obtain`, `match`)
· To prove: `constructor`, `use`, (`exact ⟨_, _⟩`)

# `∨`: inductive proposition with 2 constructors
· To use: `rcases _ | _`, (`cases`, `cases'`, `match`)
· To prove: `left`, `right`

# Miscellaneous tactics we'll meet
· `assumption`, `exfalso`, `unfold`, `rfl`, `ext`, `by_contra`,
  `by_cases`, `contrapose!`, `tauto`, `set`

## Exercises
Anything proved with `sorry` in this file is an exercise.
You can make the exercises easier by using `apply?`, `rw?`
or `exact?` and thus finding the corresponding result in
mathlib, but that's not really the point of them - the point is
to understand how to deal with logical connectives yourself.

Sometimes you might find yourself having to use the same sublemma
in multiple different exercises. See if you can state it as a
separate lemma (don't state it as an `example` - state it as `lemma`
and give it a name) so that you can use it whenever you need to.
Feel free to turn the existing `example`s into lemmas if you want to
reuse them.
Factoring out the right lemmas is a really important skill to learn.

Do whichever exercises you feel you need to; the last 2 are a little
trickier.
-/
set_option linter.unusedVariables false
namespace LFTCM2024
section
/-
## Function-like logical constructions: implication,
## negation, and the universal quantifier

We start with implication statements, `¬` statements and `∀` statements.
All three are kind of similar. -/

/-
# Implication statements

An implication statement is a statement of the form "P implies Q", where
`P` and `Q` are propositions. In Lean this is written as `P → Q`, like a
function type; a proof of `P → Q` behaves like a function too.
You can type `→` with `\to`.

(This is part of the "propositions-as-types paradigm". Types are where "data"
live - `ℕ` is a type, and it has terms like `0` and `5`. A proposition
`P : Prop` is like `ℕ` in that it can have terms - i.e. proofs - but any 2
"terms of type `P`" are equivalent in Lean, because it's proof-irrelevant. If
a proposition is false, it has no terms.)
-/

/- First let's see how to *use* an implication statement;
you already know how to do this. -/
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  apply hPQ
  exact hP

/-
So we can see `hPQ` as a function that eats a term of type `P` - i.e. a
proof - and spits out a proof of `Q`. You've already seen `apply`; we use
it to reason backwards, using `hPQ` to say "to prove `Q`, it suffices to
prove `P`."

A more intuitive use of the word `apply` is in "`apply _ at _`":
this lets us apply an implication statement to an existing hypothesis
- i.e. use forward reasoning.
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

/- `intro` lets us introduce assumptions and variables. From a function-y
perspective, we're defining a function from proofs of `P` to proofs of `Q`
and saying "let `hP` be any proof of `P` - we map it to `hQ`." -/

/- (Unimportant remark: `intro` is like moving things before the colon, i.e.
lemmas `one` and `two` are proofs of the same proposition.) -/
lemma two (P Q : Prop) (hQ : Q) (hP : P) : Q := by
  exact hQ

#check one
#check two -- same output

/- As another example, let's prove transitivity of implication.
There are invisible brackets in the statement of our theorem, because `→`
associates to the right.

We want to define a function that eats a proof of "`P` implies `Q`" and spits
out another function: one that eats a proof of "`Q` implies `R`" and spits out
a proof of "`P` implies `R`."
-/
example (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  intro hPQ hQR hP
  apply hQR
  apply hPQ
  exact hP
  --exact hQR (hPQ hP)

/-
# Negation statements

Next we'll look at `False` and negation statements. `False` is defined to
be a `Prop` with no terms. Meanwhile, negation statements are statements
beginning with `¬`, which you can type with `\not`. Given a proposition `P`,
`¬ P` is defined to mean `P → False`, so it's an implication statement in disguise.
-/
example : P → ¬¬ P := by
  intro hP
  intro hnotP
  apply hnotP
  exact hP

/- In that example we both used and proved a `¬` statement.
Sometimes we also want to use the fact that any statement follows from
`False`. In practice this shows up when proving a proposition `P` by
case-splitting on some condition, since sometimes we can conclude `P` in
a particular case by showing that case can never occur.
To derive another proposition from a proof of `False`, we use the `exfalso` tactic: -/
example (P : Prop) : False → P := by
  intro hFalse
  exfalso
  exact hFalse

/- Finally, note that `x ≠ y` is notation for `¬(x = y)`. -/
example (a b : ℕ) : a ≠ b → b ≠ a := by
  intro hab hnot
  apply hab
  rw [hnot]

/- We'll see more tactics for working with negations when we've introduced
more complicated logical connectives to combine them with. -/

/-
# Universal quantifiers

Now let's move onto universal quantifiers: `∀` statements, typed with `\all`.
We can treat `∀` statements just like we treated implications, because technically
implication statements are a special case of `∀` statements.

(If an implication `P → Q` is a bit like a function type, say, `ℕ → ℚ`,
then a `∀` statement is like a dependent function type: a type of functions
whose codomain is dependent on the function input.
For example, we can talk about functions that send a natural number `n : ℕ`
to an element of `ℤ/nℤ`; in Lean we can write the type of such functions
via `(n : ℕ) → ZMod n`, `Π (n : ℕ), ZMod n` or even `∀ n : ℕ, ZMod n`.

We can dress a non-dependent function type like `ℕ → ℚ` as a dependent one:
`∀ n : ℕ, ℚ` means the same thing as `ℕ → ℚ`.
Likewise, we can dress up an implication statement as a `∀` statement): -/
section

variable (P Q : Prop)
#check ∀ (hP : P), Q -- `P → Q : Prop`

end
/- But quantifying over all proofs of `P` is a bit pointless when they're
all equivalent.

Here's a more meaningful `∀` statement:
-/
example : ∀ P : Prop, False → P := by
  intro P hFalse
  exfalso
  exact hFalse
/-
We proved this earlier, except the `P` was before the colon; this time we
can use `intro` to introduce variables `P : Prop` and `hFalse : False` to
the local context, so indeed, proving a `∀` statement is just like proving
an implication. Let's quantify over some different types this time: -/
section
variable {α β γ : Type}

def Injective (f : α → β) : Prop :=
  ∀ x y, f x = f y → x = y

example (f : α → β) (g : β → γ) (hf : Injective f) (hg : Injective g) :
    Injective (g ∘ f) := by
  unfold Injective at hf hg ⊢
  intro X Y hXY
  apply hf
  apply hg
  exact hXY

/- If you want to see what's going on better, you can use the `specialize`
tactic to partially apply a local hypothesis to some inputs. -/
example (f : α → β) (g : β → γ) (hf : Injective f) (hg : Injective g) :
    Injective (g ∘ f) := by
  intro X Y hXY
  unfold Injective at hf
  specialize hf X Y
  apply hf
  specialize hg (f X) (f Y)
  apply hg
  exact hXY

/-
## Inductive propositions with 1 constructor:
## Conjunction, bi-implication and the existential quantifier
Now for a different group of similar logical connectives:
`∧` (\and), `↔` (\iff) and `∃` (\exists, except you just have to
type \ex). The previous group were all like function types; this group
correspond to a different kind of type - inductive types. In particular
they're all inductive propositions with 1 constructor, which is why they
behave similarly. It doesn't matter what this means; the important thing
is we can use the same tactics to deal with all 3.

The statements `P ∧ Q` and `P ↔ Q` both represent two pieces of
information, and each side is independent of the other one.

Meanwhile, like `∀`, `∃` is dependent: -/
section
/- Let `P` be a predicate on `α`: -/
variable (α : Type) (P : α → Prop)

/- (example of a predicate:) -/
def biggerThan10 : ℕ → Prop := by
  intro n
  exact 10 < n

/- Then `∃` statements look like this: -/
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

/- However, `↔` leads a double life - it also behaves just like
`=`, meaning we can `rw` `↔` statements the way we can `rw` equalities. -/
example (hPQ : P ↔ Q) (hQR : Q ↔ R) : P ↔ R := by
  rw [hPQ, hQR]

/-
# Existential quantifiers
-/

/- We can use an `∃` statement by deconstructing it and replacing
`∃ x, P x` with a term `x : α` and a hypothesis `hx : P x`. -/
example (α : Type) (P : α → Prop) (h : ∃ x, P x) : ¬ (∀ x, ¬ P x) := by
  intro hnot
  rcases h with ⟨x, hx⟩
  apply hnot
  exact hx

example (α : Type) (P Q : α → Prop) (h : ∃ x, P x ∧ Q x) :
    ∃ x, Q x ∧ P x := by
  rcases h with ⟨x, hPx, hQx⟩
  use x, hQx, hPx

example (α : Type) (P Q : α → Prop) (h : ∃ x, P x ∧ Q x) :
    ∃ x, Q x ∧ P x := by
  rcases h with ⟨x, hPx, hQx⟩
  constructor
  · use hQx, hPx

example (α : Type) (P Q : α → Prop) :
    (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  rintro ⟨x, hPx, hQx⟩
  use x, hQx, hPx

/-
As before, the tactics we're using can see underneath definitions
(unlike `rw`):
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
/- `rfl` proves definitional equalities; i.e. it succeeds when both
sides are equal by definition. -/

/- We can shorten this using the "`rfl` trick": because `hy` and `hz` are
equalities, if we name them `rfl`, they automatically get rewritten wherever
possible in the local context: -/
example {α β γ : Type} (f : α → β) (g : β → γ) (hf : Surjective f)
    (hg : Surjective g) : Surjective (g ∘ f) := by
  intro x
  rcases hg x with ⟨y, rfl⟩
  rcases hf y with ⟨z, rfl⟩
  use z
  rfl

/-
# Inductive propositions with 2 constructors: Disjunction
Final logical connective: `∨` (type `\or`). This is a little like the
previous group, in that `∨` is an inductive proposition, but instead
of one constructor with 2 pieces of information, `∨` has two constructors:
you can prove `P ∨ Q` either by proving `P` or proving `Q`.
-/

example (h : P ∨ Q) : Q ∨ P := by
  rcases h with hP | hQ
/- Now there are 2 goals. -/
  · right
    exact hP
  · left
    exact hQ

/- If you want to use `rintro` here you need to add brackets. -/
example : P ∨ Q → Q ∨ P := by
  rintro (hP | hQ)
  · right
    exact hP
  · left
    exact hQ

/- By combining the 2nd group of logical constructions and `∨` we can
start to see the power of `rcases`. -/

/- First of all here's the definition of "divides". Since `↔` behaves
like `=`, `rfl` can also prove this: -/
lemma dvd_def {m n : ℕ} : m ∣ n ↔ ∃ c, n = m * c := by
  rfl

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
/- A tactic for next session, but we don't really need it here: -/
  simp_all only [dvd_def]
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · use a * k
    rw [mul_assoc]
  . use b * n
    rw [mul_comm, mul_assoc]

/- Some exercises. -/

example (P Q R : Prop) :
    P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry

example (P Q R : Prop) :
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry

example : ¬P → P ∨ Q → Q := by
  sorry

example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  sorry

/-
## Classical logic
-/

/- Earlier we proved: -/
example : P → ¬¬P := by
  intro hP hnotP
  exact hnotP hP

/- But to prove the converse we need to use classical logic,
and apply the law of excluded middle: -/
lemma not_not : ¬¬P → P := by
  by_cases hP : P -- we case-split on `P ∨ ¬P`
  · intro h
    assumption
  · intro h
    exfalso
    exact h hP

/- The tactic `by_contra` just applies `not_not`: -/
example : ¬¬P → P := by
  intro hP
  by_contra hP'
  exact hP hP'

/- You can use `not_not` to prove the following lemma directly.
Alternatively, there are various tactics which use classical logic
and are useful here: -/
example : ¬(P → Q) → P ∧ ¬Q := by
  tauto
/- `tauto` can prove pretty much everything in this file so far. -/

/- `push_neg` simplifies negation statements by "pushing" the
negation as far inside the statement as possible: -/
example : ¬(P → Q) → P ∧ ¬Q := by
  push_neg
  intro hP
  assumption

/- We can also `push_neg` at a hypothesis: -/
example (P : α → Prop) (h : ¬∀ x, ¬P x) : ∃ x, P x := by
  push_neg at h
  assumption

/- And `push_neg` can also simplify inequalities: -/
example : ¬(∃ n : ℕ, ¬(3 < n) ∧ ¬(n ≤ 5)) := by
  push_neg
  intro n
  tauto

/- `contrapose` replaces a `p → q` goal with the contrapositive,
`¬q → ¬p`. `contrapose!` combines this with `push_neg`. -/
example : ¬(P → Q) → P ∧ ¬Q := by
  contrapose!
  intro hPQ
  assumption

/- Exercise: you can prove this without using classical logic if you're
careful. And then you can delete your proof and replace it with `tauto`. -/
example : ¬(P ↔ ¬P) := by
  sorry

/- More exercises. You can do them step by step or you can speedrun
them with the tactics in this section. -/
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry

variable (P : α → Prop)

example : ¬ (∃ x, ¬ P x) → (∀ x, P x) := by
  sorry

example : ¬ (∀ x, ¬ P x) → (∃ x, P x) := by
  sorry

/-
## Using library lemmas
-/

/-
So far we've just applied local hypotheses, but applying or
deconstructing lemmas from the library works in just the same way.
Let's demonstrate this by proving that every nonzero element of a
finite integral domain has an inverse:
-/
example (K : Type) [CommRing K] [IsDomain K] [Finite K]
    (x : K) (hx : x ≠ 0) : ∃ y, x * y = 1 := by
/- `set` (or `let`) is like `have` but for data. -/
  set f : K → K := by
    intro y
    exact x * y
  have hf : Function.Injective f := by
    intro y z hyz
    apply mul_left_cancel₀ hx
    exact hyz
  rcases Finite.surjective_of_injective hf 1 with ⟨y, hy⟩
  use y

/-
## Sets

Given a type `α`, `Set α` is the type of "subsets" of `α`. It's defined
to mean `α → Prop` - i.e. the type of predicates on `α`. To express a
particular set, we can use familiar notation:
-/

def Primes : Set ℕ :=
  { p | 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p }

def IsPrime (p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

example : IsPrime = Primes := by
  rfl

example (x : ℕ) : IsPrime x ↔ x ∈ Primes := by
  rfl

/- You can also express a set with prescribed elements: -/
def mySet : Set ℕ := {1, 2, 3, 4}

/-
Let's prove some facts about sets. We state some lemmas below which are
all true by definition, so a lot of the time you don't really need to use them,
but you can if you like. Remember that they're `↔` statements, so you can
`rw` them. -/

lemma not_mem_def {S : Set α} (x : α) : x ∉ S ↔ ¬(x ∈ S) := by rfl

lemma subset_def {S T : Set α} : S ⊆ T ↔ ∀ x, x ∈ S → x ∈ T := by rfl

lemma ssubset_def {S T : Set α} :
    (S ⊂ T) ↔ (S ⊆ T ∧ ¬T ⊆ S) := by rfl

lemma mem_compl_def {S : Set α} (x : α) :
    x ∈ Sᶜ ↔ x ∉ S := by rfl

lemma mem_inter_def {S T : Set α} (x : α) :
    x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T := by rfl

lemma mem_union_def {S T : Set α} (x : α) :
    x ∈ S ∪ T ↔ x ∈ S ∨ x ∈ T := by rfl

lemma mem_diff_def {S T : Set α} (x : α) :
    x ∈ S \ T ↔ x ∈ S ∧ x ∉ T := by rfl

lemma mem_image_def {α β : Type} {f : α → β} {S : Set α} (x : β) :
    x ∈ f '' S ↔ ∃ y ∈ S, f y = x := by rfl

lemma mem_preimage_def {α β : Type} {f : α → β} {S : Set β} (x : α) :
    x ∈ f ⁻¹' S ↔ f x ∈ S := by rfl

lemma mem_singleton_def {x y : α} :
    x ∈ ({y} : Set α) ↔ x = y := by
  rfl

lemma mem_empty_def {x : α} : x ∈ (∅ : Set α) ↔ False := by
  rfl

lemma mem_univ_iff {x : α} : x ∈ Set.univ ↔ True := by
  rfl

/- Note that the `ext` tactic allows you to prove 2 sets are
equal by proving they have the same elements: -/
example {S T : Set α} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := by
  ext x
  exact h x

/- The `ext` tactic also allows you to prove 2 functions are equal
by checking they're the same on every element: -/
example {f g : α → β} (h : ∀ x, f x = g x) : f = g := by
  ext x
  exact h x

/- The other direction can be useful too. -/
lemma ext_iff {S T : Set α} :
    S = T ↔ ∀ x, x ∈ S ↔ x ∈ T := by
  constructor
  · intro h x
    rw [h]
  · intro h
    ext x
    exact h x

/- Exercises -/
section
variable {α β : Type} {f : α → β} {S T U : Set α}

lemma inter_union_distrib_left : S ∩ (T ∪ U) = S ∩ T ∪ S ∩ U := by
  sorry

lemma union_diff_inter : (S ∪ T) \ (S ∩ T) = S \ T ∪ T \ S := by
  sorry

lemma image_subset_iff {T : Set β} : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  sorry

lemma image_eq_empty_iff : f '' S = ∅ ↔ S = ∅ := by
  sorry

lemma image_singleton {x : α} : f '' {x} = {f x} := by
  sorry

lemma image_union : f '' (S ∪ T) = f '' S ∪ f '' T := by
  sorry

lemma image_diff_of_injective (hf : Injective f) :
    f '' (S \ T) = f '' S \ f '' T := by
  sorry

lemma image_inter_of_injective (hf : Injective f) :
    f '' (S ∩ T) = f '' S ∩ f '' T := by
  sorry

lemma image_inter_preimage {T : Set β} :
    f '' (S ∩ f ⁻¹' T) = f '' S ∩ T := by
  sorry

lemma compl_compl : Sᶜᶜ = S := by
  sorry

lemma compl_compl_inter_compl :
    (Sᶜ ∩ Tᶜ)ᶜ = S ∪ T := by
  sorry

lemma const_apply {x : α} {y : β} :
    Function.const α y x = y := rfl

/- Hint: the `trivial` tactic can prove the goal `True`. -/
lemma exists_eq_const_of_preimage_singleton
    (h : ∃ b : β, True) {f : α → β}
    (hf : ∀ b : β, f ⁻¹' {b} = ∅ ∨ f ⁻¹' {b} = Set.univ) :
    ∃ b, f = Function.const α b := by
    sorry

/-
Here's something Timothy Gowers tweeted recently.
-/
section
variable {α β : Type} (f : α → β)

def Bijective : Prop := Injective f ∧ Surjective f

example : Bijective f ↔ ∀ S : Set α, (f '' S)ᶜ =  f '' Sᶜ := by
  sorry
