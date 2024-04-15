import LeanCourse.Project.Demazure
import LeanCourse.Project.DemazureAux
import LeanCourse.Project.DemazureAuxRelations

noncomputable section
open MvPolynomial

namespace Demazure

variable {n : ℕ} (n_pos : n > 0) (n_gt_1 : n > 1)

/- Now we prove the relations for the actual Demazure operator on polynomials.
There isn't a lot of math going on here, we just take the results from DemAux and
translate them to Demazure-/

-- Demazure operator has order two
lemma demazure_order_two : ∀ (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ),
  Demazure i (Demazure i p) = 0 := by
  intro i p
  apply eq_zero_of_mk'_zero.mp
  simp[Demazure]
  rw[← demazure_definitions_equivalent]
  rw[← demazure_definitions_equivalent]

  exact demaux_order_two i (mk' p)

-- Demazure operators with adjacent indices have a braid relation
lemma demazure_commutes_adjacent (i : Fin n) (h : i + 1 < n) : ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  (Demazure i ∘ Demazure ⟨i+1, h⟩ ∘ Demazure i) p = (Demazure ⟨i+1, h⟩ ∘ Demazure i ∘ Demazure ⟨i+1, h⟩) p := by
  intro p
  simp[Demazure]
  apply eq_of_eq_mk'.mp
  repeat rw[← demazure_definitions_equivalent]
  apply demaux_commutes_adjacent

-- Demazure operators with non-adjacent indices commute
lemma demazure_commutes_non_adjacent (i j : Fin n)  (h : |(i.val : ℤ ) - j.val| > 1) : ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  (Demazure i ∘ Demazure j) p = (Demazure j ∘ Demazure i) p := by
  intro p
  simp[Demazure]
  apply eq_of_eq_mk'.mp
  repeat rw[← demazure_definitions_equivalent]
  apply demaux_commutes_non_adjacent
  exact h

-- Relation between demazure operator and multiplication by non-adjacent monomials
lemma demazure_mul_monomial_non_adjacent (i j : Fin n) (h : |(i.val : ℤ ) - j.val| > 1) : ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  Demazure i (p * X (Fin.castSucc j)) = (Demazure i p) * (X (Fin.castSucc j)) := by
  intro p
  simp[Demazure]
  apply eq_of_eq_mk'.mp
  repeat rw[← demazure_definitions_equivalent]
  rw[← mk'_mul]
  rw[← mk'_mul]
  rw[← demazure_definitions_equivalent]
  rw[mk'_mul]
  apply demaux_mul_monomial_non_adjacent i j h

-- Relation between demazure operator and multiplication by adjacent monomial
lemma demazure_mul_monomial_adjacent (i : Fin n) (h : i + 1 < n) : ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  (Demazure i (p * X (Fin.castSucc i))) = (Demazure i p) * (X (Fin.succ i)) + p := by
  intro p
  simp[Demazure]
  apply eq_of_eq_mk'.mp

  rw[mk'_add]
  rw[← mk'_mul]

  repeat rw[← demazure_definitions_equivalent]
  apply demaux_mul_monomial_adjacent i h


-- Symmetric polynomials act as scalars wrt Demazure operators
lemma demazure_mul_symm (i : Fin n) (g f : MvPolynomial (Fin (n + 1)) ℂ) (h : MvPolynomial.IsSymmetric g) :
 Demazure i (g*f) = g*(Demazure i f) := by
  simp[Demazure]
  rw[← eq_of_eq_mk']
  rw[← demazure_definitions_equivalent]
  rw [← mk'_mul]
  rw [← mk'_mul]
  rw[← demazure_definitions_equivalent]

  have : IsSymmetric (mk' g) := by
    simp[IsSymmetric]
    use (to_frac g)
    simp[to_frac]
    constructor
    rfl
    exact h

  exact demaux_mul_symm i (mk' g) (mk' f) this

/- This enables to define the Demazure operator as a linear map over the ring of
symmetric polynomials, the main result of this project -/
def Dem (i : Fin n) : LinearMap (RingHom.id (MvPolynomial.symmetricSubalgebra (Fin (n + 1)) ℂ))
 (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial (Fin (n + 1)) ℂ) where
  toFun := DemazureFun i
  map_add' := demazure_map_add i
  map_smul' := by
    intro r x
    simp
    let p : MvPolynomial (Fin (n + 1)) ℂ := r
    have wah : p = r := by rfl
    have h : MvPolynomial.IsSymmetric p := by
      apply (MvPolynomial.mem_symmetricSubalgebra p).mp
      rw[wah]
      exact SetLike.coe_mem r
    exact demazure_mul_symm i p x h
