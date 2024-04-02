/-
LFTCM 2024: Using Mathlib
-/

import Mathlib

/-!
## Tools for finding results in Mathlib:

+ [The undergrad list](https://leanprover-community.github.io/undergrad.html)
  gives some sense of what is available in Mathlib, but it's not exhaustive.
+ [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)
  is great reference, but you either need to know where to look, or what things are
  named. To help with naming, you can reference the
  [naming conventions](https://leanprover-community.github.io/mathlib_docs/naming.html).
+ [Loogle](https://loogle.lean-lang.org) is useful if you know something about the types appearing
  in the statement.
+ [Moogle](https://moogle.ai) is useful if you only know the natural language phrasing.
+ [Zulip](https://leanprover.zulipchat.com‌/) in the `Is there code for X?` stream is a good place
  to ask for help.
+ The `exact?` tactic, when the theorem in question is definitely there, but you don't know the name.
-/

/-!  ### Example 1: the squart of the square root of a non-negative real number is itself.  -/

example (x : ℝ) : x.sqrt ^ 2 = x := by
  -- exact? -- fails very slowly, we forgot a hypothesis
  sorry

example (x : ℝ) (hx : 0 ≤ x) : x.sqrt ^ 2 = x := by
  exact? says exact Real.sq_sqrt hx

open scoped Real in
example : Real.sqrt π ^ 2 = π := by
  apply Real.sq_sqrt
  exact? says exact Real.pi_nonneg

/-
We can search for this with Loogle as well in the following ways:

* [`sqrt, ?x ^ 2`](https://loogle.lean-lang.org/?q=sqrt%2C+%3Fx+%5E+2)
  returns "unknown identifier `sqrt`", so we should use `Real.sqrt` instead.
+ [`Real.sqrt`](https://loogle.lean-lang.org/?q=Real.sqrt) 252 hits, our result is #37
+ [`Real.sqrt, ?x ^ 2`](https://loogle.lean-lang.org/?q=Real.sqrt%2C+%3Fx+%5E+2)
  returns all theorems involving `Real.sqrt` and `?x ^ 2`, but many more besides the one we want
+ [`⊢ Real.sqrt ?x ^ 2 = ?x`](https://loogle.lean-lang.org/?q=⊢+Real.sqrt+%3Fx+%5E+2+%3D+%3Fx)
  returns a result with this type in the conclusion, the only hit is the result we want.

Or using Moogle:
  [`The square of the square root of a real number is itself.`](https://www.moogle.ai/search/raw?q=The%20square%20of%20the%20square%20root%20of%20a%20real%20number%20is%20itself)
-/

-- maybe we needed a variant
example (x : ℝ) (hx : 0 ≤ x) : x.sqrt * x.sqrt = x := by
  exact? says exact Real.mul_self_sqrt hx

-- `Real.sqrt` is not the only phrasing! Maybe we actually wanted this instead.
open NNReal in -- note: the `sqrt` below is `NNReal.sqrt`.
example (x : ℝ≥0) : sqrt x ^ 2 = x := by
  exact? says exact sq_sqrt x

/-! ### Example 2: first isomorphism theorem for groups

How to find the first isomorphism theorem for groups.

With moogle: `first isomorphism theorem for groups`
  https://www.moogle.ai/search/raw?q=first%20isomorphism%20theorem%20for%20groups
  Somewhat far down the list is:
  [QuotientAddGroup.quotientKerEquivRange](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/QuotientGroup.html#QuotientAddGroup.quotientKerEquivRange)

With loogle:

+ [`⊢ ?G ⧸ ?H ≃* ?K`](https://loogle.lean-lang.org/?q=⊢+%3FG+⧸+%3FH+≃*+%3FK) the third hit is:
  [`QuotientGroup.quotientKerEquivRange`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/QuotientGroup.html#QuotientGroup.quotientKerEquivRange)
+ [`⊢ ?G ⧸ ker ?φ ≃* ?K`](https://loogle.lean-lang.org/?q=⊢+%3FG+⧸+ker+%3Fφ+≃*+%3FK) results in
  "unknown identifier `ker`".
+ [`⊢ ?G ⧸ MonoidHom.ker ?φ ≃* ?K`](https://loogle.lean-lang.org/?q=⊢+%3FG+⧸+MonoidHom.ker+%3Fφ+≃*+%3FK)
  Gives several related results that we maybe want including the first isomorphism theorem.

Note: In Mathlib things are often stated in maximal generality, or at least we often strive for this.
As such there is no `GroupHom` type, because we can simply use `MonoidHom` everywhere.
-/
#check MonoidHom
#check QuotientGroup.quotientKerEquivRange

-- `ZMod` found with Moogle: [`​Type of integers modulo n`](https://www.moogle.ai/search/raw?q=Type%20of%20integers%20modulo%20n)
-- easily found with loogle: `⊢ ℤ →+ ?a`
example (n : ℕ) : ℤ →+ (ZMod n) := Int.castAddHom (ZMod n)
-- easily found with loogle: `⊢ ℤ →+* ?a`
example (n : ℕ) : ℤ →+* (ZMod n) := Int.castRingHom (ZMod n)

-- normally you wouldn't create data inside a `by` block, but let's ignore that for now.
noncomputable example (n : ℕ) : ℤ ⧸ (Int.castAddHom (ZMod n)).ker ≃+ (ZMod n) := by
  apply QuotientAddGroup.quotientKerEquivOfSurjective
  intro x
  use x.valMinAbs -- easily found with Loogle: `⊢ ZMod ?n → ℤ`
  simp

/-! ### Example 3: ​If the number of vectors exceeds the dimension, the set is linearly dependent

Moogle [​If the number of vectors exceeds the dimension, the set is linearly dependent](https://www.moogle.ai/search/raw?q=If%20the%20number%20of%20vectors%20exceeds%20the%20dimension%2C%20the%20set%20is%20linearly%20dependent)

* almost no useful results, except we do know that `LinearIndependent` exists, but that
  `LinearDependent` does not seem to.
* closest result is: `exists_linearIndependent_cons_of_lt_rank`
* also has: `linearIndependent_iff_card_eq_finrank_span`

We realize that Mathlib talks about `rank` and `finrank`, but not `dimension`.
-/
#check LinearIndependent
#check Module.rank
#check FiniteDimensional.finrank
#check linearIndependent_iff_card_eq_finrank_span

-- One attempted formalization, actually invalid unless we add that `V` is finite-dimensional
-- Because `FiniteDimensional.finrank` takes the junk value `0` if `V` is not finite-dimensional.
example {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] {b : ι → V} (h : FiniteDimensional.finrank K V < Fintype.card ι) :
    ¬ LinearIndependent K b :=
  sorry

-- a possible formalization, but a bit tricky because `h` is a statement about `Cardinal`s and we
-- have to deal with finite dimensionality. Also, `b` is only a *finite* set of vectors.
example {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] {b : ι → V}
    (h : Module.rank K V < Fintype.card ι) :
    ¬ LinearIndependent K b := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  apply ne_of_gt
  have : Set.finrank K (Set.range b) ≤ Module.rank K V := by
    rw [Set.finrank]
    have : FiniteDimensional K (Submodule.span K (Set.range b)) := by
      apply FiniteDimensional.span_of_finite K
      exact? says exact Set.finite_range b
    simp? says simp only [finrank_eq_rank, ge_iff_le]
    exact? says exact rank_submodule_le (Submodule.span K (Set.range b))
  exact_mod_cast this.trans_lt h

/-
Let's keep looking.

Loogle: [`LinearIndependent, Module.rank`](https://loogle.lean-lang.org/?q=LinearIndependent%2C+Module.rank)

This yields things like:

-/
#check cardinal_le_rank_of_linearIndependent -- deprecated in favor of ...
#check LinearIndependent.cardinal_le_rank
#check le_rank_iff_exists_linearIndependent_finset
#check le_rank_iff_exists_linearIndependent

-- another formalization, this time not requiring finitely many vectors
example {R : Type u} {M : Type w} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial R]
    {ι : Type w} {v : ι → M} (h : Module.rank R M < Cardinal.mk ι) : ¬ LinearIndependent R v := by
  contrapose h
  simp_all
  exact? says exact LinearIndependent.cardinal_le_rank h

-- an alternate proof of the same fact
example {R : Type u} {M : Type w} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial R]
    {ι : Type w} {v : ι → M} (h : Module.rank R M < Cardinal.mk ι) : ¬ LinearIndependent R v := by
  apply mt LinearIndependent.cardinal_le_rank
  exact? says exact not_le_of_gt h

/- Searching the Mathlib docs for `linearindependent le finrank` yields the following as the
third hit. Note: when searching the documentation, prefer lowercase do not add `_` or `.`. Using
lowercase will match case-insensitively. The search matches substrings. -/
#check LinearIndependent.fintype_card_le_finrank

lemma foo {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M] [StrongRankCondition R]
    [Module.Finite R M] {ι : Type u_1} [Fintype ι] {b : ι → M}
    (h : FiniteDimensional.finrank R M < Fintype.card ι) :
    ¬ LinearIndependent R b := by
  contrapose h
  simp_all
  exact? says exact LinearIndependent.fintype_card_le_finrank h

-- If a set in `ℝⁿ` has more than `n` vectors, then it is linearly dependent.
example (n : ℕ) (s : Finset (Fin n → ℝ)) (h : s.card > n) :
    ¬ LinearIndependent ℝ ((↑) : s → Fin n → ℝ) := by
  contrapose h
  simp_all
  have := h.finset_card_le_finrank -- this is slightly different than the one we found above!
  simpa

-- Given three specific vectors in `ℝ²`, they are linearly dependent.
example : ¬ LinearIndependent ℝ (![![1, 0], ![1, 1], ![0, 1]] : Fin 3 → (Fin 2 → ℝ)) := by
  apply foo
  simp

/-
Finally, we may have the idea to search for hypotheses of the form `rank < card` or `finrank < card`,
Searching the docs for this yields:
-/

#check FiniteDimensional.exists_relation_sum_zero_pos_coefficient_of_finrank_succ_lt_card
#check Module.exists_nontrivial_relation_of_finrank_lt_card
#check Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card

#eval 0

/-! ### Example 4: Moogle wins first hit!  -/

-- the transition matrix between orthonormal bases is unitary
#check OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
-- ​The category of modules is Abelian
#check ModuleCat.abelian
-- every natural number is the sum of four squares
#check Nat.sum_four_squares
-- open mapping theorem
#check ContinuousLinearMap.isOpenMap
-- closed graph theorem
#check LinearMap.continuous_of_isClosed_graph
-- Hahn Banach extension theorem
#check exists_extension_of_le_sublinear
#check Real.exists_extension_norm_eq
-- Hahn Banach separation theorem
#check geometric_hahn_banach_open
#check geometric_hahn_banach_compact_closed
#check ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem
-- sandwich theorem
#check tendsto_of_tendsto_of_tendsto_of_le_of_le

/-! ### Example 5: challenges

+ Binet's formula for the `n`-th fibonacci number
  Moogle: `n-th fibonacci number` or `Binet's formula`. the latter succeeds if you scroll down
  far enough, you get `Real.coe_fib_eq`
  Loogle: [`Nat.fib, Real.sqrt`](https://loogle.lean-lang.org/?q=Nat.fib%2C+Real.sqrt) works

* Weierstrass `M`-test: Suppose that `f : ℕ → α → E` is a sequence of functions from a set `α` to a
  normed space `E`, and that `M : ℕ → ℝ` is a sequence of nonnegative real numbers such that
  `∑' n, M n` is finite. If `∀ n x, ∥f n x∥ ≤ M n`, then `∑' n, f n` converges absolutely and
  uniformly on `α`.

  Moogle: [weierstrass M-test](https://www.moogle.ai/search/raw?q=weierstrass%20M-test) no luck

  keywords? series converges, uniform convergence, absolute convergence

  Moogle: [series converges](https://www.moogle.ai/search/raw?q=series%20converges), the hit
  [`Summable.tendsto_cofinite_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/Group.html#Summable.tendsto_cofinite_zero)
  gives us some hints about how Mathlib phrases things.
  `Summable`, `Filter.Tendsto`, `tsum`, `tsum_def`

  Moogle: [unifrom convergence](https://www.moogle.ai/search/raw?q=uniform%20convergence)
  first few hits are garbage, but `tendstoUniformlyOn_singleton_iff_tendsto` seems to tell us
  that Mathlib calls uniform convergence `TendstoUniformlyOn`.

  Loogle: [`tsum, TendsToUniformlyOn`](https://loogle.lean-lang.org/?q=tsum%2C+TendstoUniformlyOn)

* The operator norm between normed spaces is the supremum of the norms taken over the image of the
  unit ball.
  Moogle: [operator norm is the supremum over the unit ball](https://www.moogle.ai/search/raw?q=operator%20norm%20is%20the%20supremum%20over%20the%20unit%20ball)
  This is the fifth hit, but it is somewhat misleading, because that's not generally how you want
  to use the operator norm in Mathlib. The operator norm is defined as the infimum of the
  constants `c` such that `0 ≤ c` and `∥f x∥ ≤ c * ∥x∥` for all `x`. Treating it as the supremum is
  harder to work with, and requires more hypotheses (e.g., `DenselyNormedField`).

* Borel-Cantelli lemma:

  Moogle: [Borel-Cantelli lemma](https://www.moogle.ai/search/raw?q=Borel-Cantelli%20lemma)
  succeeds with `MeasureTheory.measure_limsup_eq_zero`, but it's pretty far down the list.

  Moogle: [​borel cantelli lemma](https://www.moogle.ai/search/raw?q=borel%20cantelli%20lemma)
  fails, sometimes Moogle is finicky

  Loogle: [`measure, limsup, 0`](https://loogle.lean-lang.org/?q=measure%2C+limsup%2C+0)
  suggests the correction:
  Loogle: [`measure, Filter.limsup, 0`](https://loogle.lean-lang.org/?q=measure%2C+Filter.limsup%2C+0)
  This returns no results, but it's deceptive because `measure` has nothing to do with
  `MeasureTheory.measure`

  Loogle: [`MeasureTheory.Measure, Filter.limsup, 0`](https://loogle.lean-lang.org/?q=MeasureTheory.Measure%2C+Filter.limsup%2C+0)
  first hit!

* Euler's totient theorem

  Moogle: [Euler's totient theorem](https://www.moogle.ai/search/raw?q=Euler%27s%20totient%20theorem)
  fourth hit is `ZMod.pow_totient`, which is the result we want.

* A *Dedekind domain* is an integral domain satisfying one of several equivalent conditions
  including:

  1. Noetherian, integrally closed, and has Krull dimension at most one
  2. Every nonzero proper ideal factors into a product of prime ideals

  In Mathlib, the first of these is the definition of `IsDedekindDomain`. So, where is the
  result that a Dedekind domain satisfies property (2)?
  Mooogle: [`​In a dedekind domain, every nonzero proper ideal is a product of prime factors`](https://www.moogle.ai/search/raw?q=In%20a%20dedekind%20domain%2C%20every%20nonzero%20proper%20ideal%20is%20a%20product%20of%20prime%20factors)
  doesn't seem to find it, although it does find:
-/
#check IsDedekindDomain.quotientEquivPiOfProdEq
/-
To understand why we can't find this result, it helps to realize that the ideals of a commutative
ring form a semiring, and just like for `ℕ`, it makes sense to talk about unique factorization.
From this vantage point, one can rephrase condition (2) as: if `R` is a Dedekind domain, then
`Ideal R` is a unique factorization monoid. This is the statement that we are looking for. Since
`UniqueFactorizationMonoid` is a class, Lean should be able to infer automatically that `Ideal R` is
a unique factorization monoid if `R` is a Dedekind domain, assuming the instance exists. Let's see
if this is true. We can use the `#synth` command to ask Lean to synthesize the instance.
-/
section DedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

#synth UniqueFactorizationMonoid (Ideal R) -- Ideal.uniqueFactorizationMonoid

#check Ideal.uniqueFactorizationMonoid -- does this have an extraneous `IsDomain` hypothesis?

-- we can also do it with `infer_instance`
example : UniqueFactorizationMonoid (Ideal R) := by
  infer_instance

end DedekindDomain

/-! ### Example 6: how to phrase it in Mathlib?

1. `E` is a banach space over `𝕜`
2. `A` is an algebra over the commutative ring `R`.
3. `A` is a non-unital algebra over the commutative ring `R`.
4. `s` is a finite subset of `X : Type*`.
5. `X` is a finite type.
6. Providing a bijection between `X` and `Y`.
7. The set `{n : ℕ | 0 ≤ n}` is all of `ℕ`.

Answers:
1. `variable {𝕜 E : Type*} [NormedAddCommGroup E] [NormedField 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E]`
2. `variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]`
3. `variable {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]`
4. `variable {X : Type*} {s : Finset X}` or `variable {X : Type*} {s : Set X} [Set.Finite s]`
   The former is for sets which are structurally finite, the latter is for sets which are provably finite.
5. `variable {X : Type*} [Fintype X]` or `variable {X : Type*} [Finite X]`
   The former is for types which are structurally finite, the latter is for types which are provably finite.
6. This depends on whether `X` and `Y` are types or sets. If they are types, then a bijection is a
   term of `X ≃ Y` (This is `Equiv`), and here you must specify the inverse function. If you only
   want to say a function is bijective, then `Function.Bijective` is the relevant predicate.
   You can construct (noncomputably) an `Equiv` from a `Function.Bijective` using
   `Equiv.ofBijective`.

   If they are subsets of some types, then either `PEquiv` or `PartialEquiv` would be used to give
   a bijection along with its inverse, and `Set.BijOn` is used to state that a function is maps one
   set bijectively onto another.
7. `{n : ℕ | 0 ≤ n} = Set.univ` (note that `{n : ℕ | 0 ≤ n} = ℕ` doesn't make sense in Lean, because
   `ℕ : Type`, so it does not have type `Set ℕ` and so it does not make sense to ask if these are
   equal).
-/

/-! ### Example 7: induction principles

Many mathematicians are accustomed to using induction on the natural numbers, but in Lean, there
are many other types for which induction is possible, and in general it is easier to apply these
induction principles than to finagle the statement into one about the natural numbers.

For instance, to prove a predicate `P : Set α → Prop` holds for all finite subsets of `α`,
mathematicians would normally do induction on the cardinality. However, in Lean, we can use
`Set.Finite.induction_on`, which says that if `P ∅` holds, and whenever `P s` holds for a finite
subset `s`, then `P ({a} ∪ s)` holds for any `a : α` not in `s`.

There are a variety of such induction principles in Mathlib, and they are often more convenient
to work with.

For example if a predicate `P` holds for all elements of a set `s` in a semiring `R`, and it holds
for `0`, `1`, and is preserved by addition and multiplication, then it holds for all elements of
`Subsemiring.closure s` (the subsemiring generated by `s`).
-/
#check Subsemiring.closure_induction'

-- This is not the shortest proof, but it just shows how you can use the induction principle.
-- you shouldn't necessarily be able to follow the proof very easily.
example (x : ℚ) (hx : x ∈ Subsemiring.closure {(5 : ℚ)}) : ∃ n : ℕ, x = n := by
  induction hx using Subsemiring.closure_induction' with
  | mem x hx =>
    simp only [Set.mem_singleton_iff] at hx
    use 5
    exact_mod_cast hx
  | zero => use 0; rfl
  | one => use 1; rfl
  | add x hx y hy hx' hy' =>
    obtain ⟨n, rfl⟩ := hx'
    obtain ⟨m, rfl⟩ := hy'
    use n + m
    exact_mod_cast rfl
  | mul x hx y hy hx' hy' =>
    obtain ⟨n, rfl⟩ := hx'
    obtain ⟨m, rfl⟩ := hy'
    use n * m
    exact_mod_cast rfl

-- a nonempty finite set in `ℕ` has a maximum element
-- you shouldn't necessarily be able to follow the proof very easily.
example (s : Set ℕ) (hs : s.Finite) (h_non : s.Nonempty) : ∃ x ∈ s, ∀ y ∈ s, y ≤ x := by
  revert h_non
  refine hs.induction_on ?empty ?insert -- in this case the `induction` tactic didn't work.
  case empty => simp
  case insert =>
    intro x s hxs _ ih
    by_cases h : s.Nonempty
    · obtain ⟨z, hz_mem, hz⟩ := ih h
      rintro -
      use max x z
      simp only [Set.mem_insert_iff, max_eq_left_iff, le_max_iff, forall_eq_or_imp, le_refl,
        true_or, true_and]
      constructor
      · obtain (h' | h') := le_total z x <;> simp_all
      · peel hz with a ha _
        exact Or.inr this
    · rintro -
      use x
      rw [Set.not_nonempty_iff_eq_empty] at h
      simp_all


/-! ### Example 8: Using `#help`

The `#help` command can provide you information about tactics, attributes, and commands in Lean,
and several other things besides, although sometimes the information provided here is relatively
sparse.
-/
#help tactic ring
#help tactic peel
#help tactic ext

#help attr simps
#help attr ext


/-! ### Example 9: Sometimes it's actually missing, even simple things

Let's find:
1. the intersection of intervals `[a, b]` and `[c, d]` is another closed interval.
2. that `(a, b) ∩ (c, ∞)` is an open finite interval.

How does lean even call these intervals?
+ Moogle: [closed interval intersection](https://www.moogle.ai/search/raw?q=closed%20interval)
  yields as th second hit [`Set.Icc`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Intervals/Basic.html#Set.Icc)
  where we also find `Set.Ioo`, `Set.Ioc`, `Set.Ioi`, etc.

For (1), we try:
+ Loogle: [Set.Icc ?a ?b ∩ Set.Icc ?c ?d](https://loogle.lean-lang.org/?q=Set.Icc+%3Fa+%3Fb+∩+Set.Icc+%3Fc+%3Fd)
  success! `Set.Icc a₁ b₁ ∩ Set.Icc a₂ b₂ = Set.Icc (a₁ ⊔ a₂) (b₁ ⊓ b₂)`
-/
#check Set.Icc_inter_Icc
/-
For (2), we try
+ Loogle: [Set.Ioo ?a ?b ∩ Set.Ioi ?c](https://loogle.lean-lang.org/?q=Set.Ioo+%3Fa+%3Fb+∩+Set.Ioi+%3Fc)
  no hits. :(
+ Loogle: [Set.Ioi, Inter.inter, Set.Ioo](https://loogle.lean-lang.org/?q=Set.Ioi%2C+Inter.inter%2C+Set.Ioo)
  two results, neither the one we want.
+ Is there code for X?: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Ioo_inter_Ioi/near/426780505
  we just don't have this result. (You can create a PR if you want! Although since we have so many
  people, maybe claim it on Zulip first so that we don't get 10 PRs of the same thing.)
-/

/-! ### Exercise 10: Audience questions

What are some things you would like to find in Mathlib?
-/

/-
Things to find:

-/

/-! ### Exercises -/

-- 1. Find statements of the first isomorphism theorem for rings and for modules.
-- 2. Find the Bolzano-Weierstrass theorem.
-- 3. Find the extreme value theorem.
-- 4. Find the intermediate value theorem. Can you prove:
example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (ha : f a < 0) (hb : 0 < f b) :
    ∃ c, f c = 0 := by
  have : 0 ∈ Set.Icc (f a) (f b) := by
    simp only [Set.mem_Icc]
    exact ⟨ha.le, hb.le⟩


  sorry
