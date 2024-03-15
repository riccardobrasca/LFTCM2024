import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

open Matrix MatrixGroups SpecialLinearGroup

/-Lets play with some matrices. Firstly, lets construct some. The
![![a, b], ![c, d]] notation makes the 2x2 matrix with top row a b and bottom row c d -/

def S' : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1 ; 1, 0]

def T' : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1 ; 0, 1]

/-Next lets compute some determinants. In general doing things explicitly can be a bit fiddly, but
for 2x2 matrices its nice enough.-/

lemma S'_det : S'.det = 1 := by
  apply Matrix.det_fin_two_of

lemma T'_det : T'.det = 1 := by sorry


/- We can now define them as elements of SL(2, ℤ), which consists of a pair ⟨M, M_Det⟩ where
M is a matrix and M_Det is a proof that the determinant of M is 1. To get back the matrix, you can use
the .1 notation e.g. S.1 = S' -/
def S : SL(2, ℤ) := ⟨S', S'_det⟩

def T : SL(2, ℤ) := ⟨T', T'_det⟩

/-The inverse of a matrix in SL(2, ℤ) is defined in terms of the adjucate-/

example : (S⁻¹).1 = (adjugate ↑S) := by exact rfl

/-Lets check what the inverse is as a matrix, the key is to first open up what the inverse is
like above, and then use `adjugate_fin_two` which tells you what the adjugate of a 2x2 matrix is.

After this, one way to proceed is to turn this into a case-by-case proof, using ext i j together with
fin_cases i and fin_cases j. Since its a 2x2 matrix, this is not too bad.-/

theorem coe_T_inv : (T⁻¹).1 = !![1, -1 ; 0, 1] := by
  sorry


lemma T'_pow (n : ℤ) : (T ^ n).1 = !![1, n; 0, 1] := by
  induction' n using Int.induction_on with n h n h
  · sorry
  · sorry
  · sorry
