import DemazureOperators.DemazureRelations
import DemazureOperators.Matsumoto
import DemazureOperators.Demazure

import Mathlib.Data.Int.Range

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

lemma demazureOfWord_append (l l' : List (Fin n)) : DemazureOfWord (l ++ l') = LinearMap.comp (DemazureOfWord l) (DemazureOfWord l') := by
  induction l with
  | nil => simp[DemazureOfWord]
  | cons i l ih => simp[DemazureOfWord, ih, LinearMap.comp_assoc]

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
    | 0 =>
      simp[apply_braidMove]
      by_cases h : List.take (M.M i j) (i' :: l) = braidWord M i j
      · simp[h]
        nth_rewrite 1 [← List.take_append_drop (M.M i j) (i' :: l)]
        rw[demazureOfWord_append]
        rw[demazureOfWord_append]
        suffices DemazureOfWord (List.take (M.M i j) (i' :: l)) = DemazureOfWord (braidWord M j i) from by
          rw[this]
        rw[h]

        simp[braidWord]
        by_cases h_eq : i = j
        · simp[h_eq]

        by_cases h_adjacent : j.succ = i.castSucc ∨ i.succ = j.castSucc
        · have j_ne_i : ¬ j = i := by
            intro h
            rw[h] at h_eq
            contradiction
          have h_adjacent' : i.succ = j.castSucc ∨ j.succ = i.castSucc := by
            rcases h_adjacent with h1 | h2
            · right
              simp[h1]
            · left
              simp[h2]
          simp[M, CoxeterMatrix.Aₙ, j_ne_i, h_eq, h_adjacent, h_adjacent']
          simp[alternatingWord, DemazureOfWord, Demazure, LinearMap.comp, Function.comp]

          rcases h_adjacent with h1 | h2
          · have hj : j.val + 1 < n := by
              rw[h1]
              simp

            have h1' : ⟨j.val + 1, hj⟩  = i := by
              apply Fin.ext
              simp[h1]
            rw[← h1']
            funext p
            exact demazure_commutes_adjacent j hj p
          · have hi : i.val + 1 < n := by
              rw[h2]
              simp

            have h2' : ⟨i.val + 1, hi⟩ = j := by
              apply Fin.ext
              simp[h2]
            rw[← h2']
            funext p
            exact Eq.symm (demazure_commutes_adjacent i hi p)
        · have j_ne_i : ¬ j = i := by
            intro h
            rw[h] at h_eq
            contradiction

          have h_adjacent' : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
            intro h_contra
            apply h_adjacent

            rcases h_contra with h1 | h2
            · right
              simp[h1]
            · left
              simp[h2]

          simp[M, CoxeterMatrix.Aₙ, h_eq, j_ne_i, h_adjacent, h_adjacent']
          simp[alternatingWord, DemazureOfWord, Demazure, LinearMap.comp, Function.comp]

          funext p
          apply demazure_commutes_non_adjacent i j
          simp[NonAdjacent]
          constructor
          · exact h_eq
          constructor
          ·


          | 1 => sorry
          | 2 => sorry



    | p + 1 =>
      simp[DemazureOfWord, apply_braidMove]
      simp[LinearMap.comp, Function.comp]
      apply congr_arg
      rw[ih ⟨i, j, p⟩]


theorem DemazureOfWord_eq_equivalentWord (l l' : List (Fin n)) (h_eq : π l = π l') (hr : cs.IsReduced l) (hr' : cs.IsReduced l') :
  DemazureOfWord l = DemazureOfWord l' := by

  sorry
