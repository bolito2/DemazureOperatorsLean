import DemazureOperators.DemazureRelations
import DemazureOperators.Matsumoto
import DemazureOperators.Demazure

open Demazure CoxeterSystem
noncomputable section

variable {n : ℕ}
def M := CoxeterMatrix.Aₙ n
def cs := (@M n).toCoxeterSystem

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

lemma one_le_M : ∀ i j : Fin n, 1 ≤ M i j := by
  intro i j
  simp[M, CoxeterMatrix.Aₙ]
  by_cases h1 : i = j
  repeat
    by_cases h2 : j.val + 1 = i.val ∨ i.val + 1 = j
    repeat simp [h1, h2]

lemma braidWord_ne_nil : ∀ (i j : Fin n), braidWord M i j ≠ [] := by
  intro i j
  simp[braidWord]
  suffices M i j ≠ 0 from by
    intro h
    apply this
    rw[← length_alternatingWord i j (M i j)]
    exact List.length_eq_zero.mpr h

  have h := one_le_M i j
  linarith

def DemazureOfWord (l : List (Fin n)) : LinearMap (RingHom.id ℂ) (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial (Fin (n + 1)) ℂ) :=
  match l with
  | [] => LinearMap.id
  | i :: l => LinearMap.comp (Demazure i) (DemazureOfWord l)


theorem demazure_of_braidMove (l : List (Fin n)) (bm : cs.BraidMove) :
DemazureOfWord l = DemazureOfWord (cs.apply_braidMove bm l) := by
  revert bm
  induction l with
  | nil =>
    rintro ⟨i, j, p⟩
    simp[DemazureOfWord, apply_braidMove]
    rw[apply_braidMove.eq_def]
    simp[braidWord_ne_nil]

    match p with
    | 0 => simp[DemazureOfWord]
    | p + 1 => simp[DemazureOfWord]

  | cons i' l ih =>
    rintro ⟨i, j, p⟩

    match p with
    | 0 => sorry
    | p + 1 =>
      simp[DemazureOfWord, apply_braidMove]
      simp[LinearMap.comp, Function.comp]
      apply congr_arg
      rw[ih ⟨i, j, p⟩]


theorem DemazureOfWord_eq_equivalentWord (l l' : List (Fin n)) (h_eq : π l = π l') (hr : cs.IsReduced l) (hr' : cs.IsReduced l') :
  DemazureOfWord l = DemazureOfWord l' := by

  sorry
