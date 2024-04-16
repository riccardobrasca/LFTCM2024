import Mathlib.GroupTheory.Commutator
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped Pointwise


/-!
Day 1 - Morning, Basics (Fundamentals) (Alex)
========================================

Welcome!

This is the first session of Lean for the Curious Mathematician 2024.

The goal of the session is to get you up to speed with the basics of proof assistants
like Lean, so that you can start learning by doing, working on things you are
interested in with help from others over the rest of the week. There are many experts on
Lean and proof assistants more generally in the room, so don't be afraid to ask questions!
Also during this presentation, feel free to ask questions at any time.

What is a proof assistant?
-------------------------
A piece of software that lets the user express mathematical objects and arguments in a language
that the computer can handle and interact with in a rigorous way.
This process is called formalisation.
Here is an example of a formalized statement:
-/

/-- The polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of an elementary abelian
2-group of doubling constant at most $K$, then $A$ can be covered by at most $2K^{12}$ cosets of
a subgroup of cardinality at most $|A|$. -/
theorem PFR_conjecture {G : Type*} [AddCommGroup G] {A : Set G} [Finite A] {K : ℝ} [Countable G]
    (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :

  ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c < 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by sorry

/-
Motivation:
-----------
- There is something satisfying about finding and writing a good clean proof that can be included
  in a large library and be available and useful to others to build on and modify
- Formal proofs can be inspectable by readers without interaction (who can interactively choose how
  much detail they wish to see and what the current context is)
- These tools can in some cases be used to automate routine arguments without compromising
  mathematical rigour.
- Alternatively checking correctness of large, complicated, and novel proofs (cf. Liquid Tensor
  Experiment, Kepler conjecture) or of mathematical software
- Enabling tooling around searching for mathematical results, re-applying proofs in new contexts
  and understanding
- Machine learning on existing formalised mathematics could lead to tools that can suggest new
  statements and/or proofs to us, or at the very least let use do formalised mathematics without
  compromising human readability
We'd like to have as many of these benefits as possible, but without sacrificing what is good about
human mathematical interaction, but we are not there yet!

So our aim this week is to add another tool to your toolbox as a curious mathematician, that we
think could be relevant to how mathematics is done in the future.

Let's go!
--------

We will learn to create proofs using tactics, short commands that let us describe a certain steps of
proofs and modify an interactive context showing our current state (what we are assuming, what we
know so far, and what remains to be proved).

In this session we will cover how to express three styles of proof in Lean,
These operate on the goal (the statement we are trying to prove) by changing it to a different goal,
or set of goals, hopefully in a way that makes progress towards the full proof.
The three techniques (tactics) we will cover are
- rewriting (replacing parts of the goal) - `rw` or `rewrite`
- backwards reasoning (reducing the goal to statements that imply it) - `apply`
- forwards reasoning (adding new consequences of our original assumptions to the context)

There will be some variations on the above (and indeed other commands that do multiple rewriting or reasoning
steps for you), but these are the most fundamental.


In the real world our proofs use a mix of many different styles of reasoning all at once, but for
learning how to use it is helpful to emphasise the different nature of these types of proof.
-/

/-- An example of a proof by rewriting

**Rewriting** is where we change our goal (or a part of it) to something equal (or logically
equivalent) in order to make progress.

Here the commutator of two elements of a group is denoted by `⁅g, h⁆`
and is defined to be `g * h * g⁻¹ * h⁻¹`.  -/

lemma inv_commutator {G : Type} [Group G] (g h : G) : ⁅g, h⁆⁻¹ = ⁅h, g⁆ := by
  rw [commutatorElement_def]
  rw [commutatorElement_def]
  rw [mul_inv_rev]
  rw [mul_inv_rev]
  rw [mul_inv_rev]
  rw [inv_inv]
  rw [inv_inv]
  rw [mul_assoc]
  rw [mul_assoc]
  -- later we will learn tactics for doing these things in few or 1 step

/-
Names
-----

All of the fundamental tactics I'm showing are low-tech, they generally require the user to find
and say the name of the lemma they want to use. There are several ways to make this easier:
There are helper tactics that will suggest moves you may want to make to you
(try adding a ?, e.g. `rw?`, `apply?`), though after a while learning the naming convention of the
library you are using will help you spend less time thinking about the boring parts of your proof.
You may find the following websites useful when finding lemmas you want to use:
- https://loogle.lean-lang.org/
- https://leanprover-community.github.io/mathlib4_docs/
- https://www.moogle.ai/
We can also ctrl+click on the name of a definition to find the file it is in, and start exploring. -/


/-
**Backwards reasoning** is where we chain implications backwards, deducing what we want to prove
from a combination of other statements (potentially even stronger ones).

A classic example of this is proving that a function defined as a combination of others has some
property, e.g. continuous, differentiable, locally constant, etc.
we do this by reasoning backwards, deconstructing the definition of the function down to its
constituent pieces.
For example we might start by applying the fact that a sum of two continuous functions is continuous.  -/

open Real

example : Continuous (fun x ↦ (sin (x ^ 2)) ^ 3 + cos (5 * x)) := by
  -- apply?
  apply Continuous.add
  apply Continuous.pow
  apply Continuous.comp continuous_sin
  apply continuous_pow
  apply Continuous.comp continuous_cos
  apply Continuous.mul
  apply continuous_const
  apply continuous_id


/-
But this is obvious!
Any mathematician worth their salt knows that such a function is continuous just by looking at it,
its a composition of polynomials and things polynomial in `cos` and `sin`.

Mathlib has tactics for automatically doing some such reasoning chains, but don't use it for the
exercises!  -/

example : Continuous (fun x ↦ (sin (x ^ 2)) ^ 3 + cos (5 * x)) := by
  sorry

/-
**Forwards reasoning** is where we chain implications forwards, deducing new facts from what we
already know eventually reaching our goal.
This can sometimes be more verbose than backwards reasoning, but is often more natural.

Let's do the same example again with forwards reasoning.  -/

lemma myCoolFunction_continuous : Continuous (fun x ↦ (sin (x ^ 2)) ^ 3 + cos (5 * x)) := by
  have : Continuous (fun (x : ℝ) ↦ x) := by exact continuous_id' -- by exact? type
  have : Continuous (fun (x : ℝ) ↦ 5 * x) := by exact continuous_mul_left 5
  have h_rhs : Continuous (fun (x : ℝ) ↦ cos (5 * x)) := Continuous.comp' continuous_cos this
  have h_lhs : Continuous (fun (x : ℝ) ↦ sin (x ^ 2) ^ 3) := by
    have h_sq : Continuous (fun (x : ℝ) ↦ x ^ 2) := by exact continuous_pow 2
    have : Continuous (fun (x : ℝ) ↦ sin x) := by exact continuous_sin
    have h_sin3 : Continuous (fun (x : ℝ) ↦ (sin x) ^ 3) := by exact Continuous.pow this 3
    have : Continuous (fun (x : ℝ) ↦ sin (x ^ 2) ^ 3) := by exact Continuous.comp' h_sin3 h_sq
    exact this -- or assumption
  exact Continuous.add h_lhs h_rhs


/-
Some differences between rewriting and applying:
- Rewriting can take place almost anywhere in the goal, but apply generally has to match the
  conclusion of the goal you are trying to prove e.g. if you are trying to prove an "and" statement,
  you'll need to split it in to two goals before trying to `apply` a lemma that will
  affect only one part.
- Sometimes many rewrites are possible using the same lemma, and specifying more of
  the arguments will help, `rw [mul_assoc b a c]` instead of  `rw [mul_assoc a b c]`.
-/

/-
What is actually happening here?
-------------------------------

The commands (tactics) we write are translated by the software into a hard to read but very precise
low level proof, this is then checked for correctness by a component of the system called the kernel.
Tactics are a high level language for writing proofs that provide useful interactivity and allow us
to remain at a slightly higher level of abstraction, and the kernel is a low level language for
checking that what the tactics did resulted in a valid proof.

Lets see some examples of this: -/

#print myCoolFunction_continuous

#print inv_commutator
