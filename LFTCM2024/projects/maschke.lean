import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.CategoryTheory.Simple
import Mathlib.RepresentationTheory.Maschke

set_option autoImplicit false

open Classical

universe u v

variable (G : Type u) [Group G] [Fintype G]
variable (k : Type u) [Field k] -- if we leave CommRing and then add to a lemma the assumption
  --[Field k], the invertibility assumption below cannot be found
variable [Invertible (Fintype.card G : k)]

variable (V : Type u) [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
variable [IsScalarTower k (MonoidAlgebra k G) V]

def IsIrreducible : Prop :=
  ∀ W : Submodule (MonoidAlgebra k G) V, W ≠ ⊤ → W = ⊥

lemma IsIrreducible_bot : IsIrreducible G k (⊥ : Submodule (MonoidAlgebra k G) V ):= by sorry

-- structure IrreducibleRep extends Module (MonoidAlgebra k G) V where
--   isIrred : IsIrreducible G k V

open DirectSum FiniteDimensional

structure MaschkeDecomposition where
  ι : Type
  fin_ι : Finite ι
  W : ι → Submodule (MonoidAlgebra k G) V
  irred : ∀ i : ι, IsIrreducible G k (W i)
  -- should probably use : ∀ i : ι, CategoryTheory.Simple (W i)
  equiv_sum : DirectSum.IsInternal W
  -- equiv_sum : V ≃ₗ[MonoidAlgebra k G] (⨁ (i : ι), W i)

#help tactic induction

-- fd is probably useless
theorem foo (fd : FiniteDimensional k V) (d :ℕ) (hd : d = FiniteDimensional.finrank k V) :
    Nonempty (MaschkeDecomposition G k V) := by
  induction' d with n hn generalizing V
  · constructor
    use PUnit
    · exact Finite.of_fintype _
    · exact fun x => ⊥
    · exact fun _ => IsIrreducible_bot _ _ _
    · suffices V = (⊥ : Submodule k V) by
        sorry
      simp_all only [gt_iff_lt, Nat.zero_eq, Submodule.mem_bot]
      sorry
  · obtain ⟨x, hx⟩ := (finrank_pos_iff_exists_ne_zero).mp (hd ▸ Nat.succ_pos')
    obtain ⟨W, hW⟩ := MonoidAlgebra.Submodule.exists_isCompl (k := k) (G := G) (V := V)
      (Submodule.span _ {x})
    have rank_W_n : finrank k W = n := by sorry
    have rank_W_fin : FiniteDimensional k W := by sorry
    specialize hn W rank_W_fin rank_W_n.symm
    sorry


      -- apply Nat.sy
      -- exact hd ▸ Nat.succ_pos'
      -- apply Nat.succ_pos

    -- · let a := (DirectSum.id.{0,v} V).symm
    --   fconstructor
    --   · use a
    --   · sorry--use (DirectSum.id V)
      -- · sorry
      -- simp at hd
      -- replace hd := hd.symm
      -- rw [FiniteDimensional.finrank_zero_iff] at hd

      -- have := @Submodule.finrank_eq_zero k V _ _ _ _ _ _ ⊤ _
      -- simp at hd
      -- erw [← hd] at this
      -- rw finrank_eq_rank
