import DemazureOperators.DemazureRelations
import DemazureOperators.Matsumoto
import DemazureOperators.Demazure
import DemazureOperators.SymmetricGroup

import Mathlib.Data.Int.Range

set_option quotPrecheck false

open Demazure CoxeterSystem
noncomputable section

variable {n : ℕ}
def Symm (n : ℕ) := CoxeterSystem.S_cox n

instance : MatsumotoCondition (Symm n) := instOfMatsumotoReady n

local prefix:100 "s" => (Symm n).simple
local prefix:100 "π" => (Symm n).wordProd
local prefix:100 "len" => (Symm n).length

lemma one_le_M : ∀ i j : Fin n, 1 ≤ M n i j := by
  intro i j
  simp[M, CoxeterMatrix.Aₙ]
  by_cases h1 : i = j
  repeat
    by_cases h2 : j.val + 1 = i.val ∨ i.val + 1 = j
    repeat simp [h1, h2]

lemma braidWord_ne_nil : ∀ (i j : Fin n), braidWord (M n) i j ≠ [] := by
  intro i j
  simp[braidWord]
  suffices M n i j ≠ 0 from by
    intro h
    apply this
    rw[← length_alternatingWord i j (M n i j)]
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

theorem demazure_of_braidMove (l : List (Fin n)) (bm : (Symm n).BraidMove) :
DemazureOfWord l = DemazureOfWord ((Symm n).apply_braidMove bm l) := by
  revert bm
  induction l with
  | nil =>
    rintro ⟨i, j, p⟩
    simp[DemazureOfWord, apply_braidMove]
    rw[apply_braidMove.eq_def]
    simp[braidWord_ne_nil]

    match p with
    | 0 => simp[DemazureOfWord]
    | _ + 1 => simp[DemazureOfWord]

  | cons i' l ih =>
    rintro ⟨i, j, p⟩

    match p with
    | 0 =>
      simp[apply_braidMove]
      by_cases h : List.take (M n i j) (i' :: l) = braidWord (M n) i j
      · simp[h]
        nth_rewrite 1 [← List.take_append_drop (M n i j) (i' :: l)]
        rw[demazureOfWord_append]
        rw[demazureOfWord_append]
        suffices DemazureOfWord (List.take (M n i j) (i' :: l)) = DemazureOfWord (braidWord (M n) j i) from by
          rw[this]
        rw[h]

        simp[braidWord]
        by_cases h_eq : i = j
        · simp[h_eq]

        by_cases h_adjacent : NonAdjacent i j
        · have j_ne_i : ¬ j = i := by
            intro h
            rw[h] at h_eq
            contradiction

          rcases h_adjacent with ⟨_, h2, h3, _⟩
          simp at h2 h3

          have h2' := not_imp_not.mpr Fin.eq_of_val_eq h2
          have h3' := not_imp_not.mpr Fin.eq_of_val_eq h3

          simp at h2' h3'

          simp[M, CoxeterMatrix.Aₙ, h_eq, j_ne_i, h2', h3', Ne.symm h2', Ne.symm h3']
          simp[alternatingWord, DemazureOfWord, Demazure, LinearMap.comp, Function.comp]

          funext p
          apply demazure_commutes_non_adjacent i j
          simp[NonAdjacent]
          constructor
          · exact h_eq
          constructor
          · exact h2
          constructor
          · exact h3
          exact h_eq

        · have j_ne_i : ¬ j = i := by
            intro h
            rw[h] at h_eq
            contradiction
          have h_adjacent' : j.val + 1 = i.val ∨ i.val + 1 = j.val := by
            rw[NonAdjacent] at h_adjacent
            simp at h_adjacent
            by_contra h_contra
            simp at h_contra
            rcases h_contra with ⟨h1, h2⟩
            apply h_eq
            apply h_adjacent h_eq
            intro h_fin
            apply h1
            apply Eq.symm
            apply Fin.val_eq_of_eq h_fin

            intro h_fin
            apply h2
            apply Fin.val_eq_of_eq h_fin


          simp[M, CoxeterMatrix.Aₙ, j_ne_i, h_eq, h_adjacent', Or.comm.mp h_adjacent']
          simp[alternatingWord, DemazureOfWord, Demazure, LinearMap.comp, Function.comp]

          rcases h_adjacent' with h1 | h2
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
      · simp[h]
    | p + 1 =>
      simp[DemazureOfWord, apply_braidMove]
      simp[LinearMap.comp, Function.comp]
      apply congr_arg
      rw[ih ⟨i, j, p⟩]

lemma demazure_of_braidMoveSequence (l : List (Fin n)) (bms : List (Symm n).BraidMove) :
DemazureOfWord l = DemazureOfWord ((Symm n).apply_braidMoveSequence bms l) := by
  induction bms with
  | nil =>
    simp[apply_braidMoveSequence]
  | cons bm bms ih =>
    rw[apply_braidMoveSequence]
    rw[← demazure_of_braidMove ((Symm n).apply_braidMoveSequence bms l) bm]
    exact ih

theorem DemazureOfWord_eq_equivalentWord (l l' : List (Fin n)) (h_eq : π l = π l') (hr : (Symm n).IsReduced l) (hr' : (Symm n).IsReduced l') :
  DemazureOfWord l = DemazureOfWord l' := by

  suffices ∃ (bms : List (Symm n).BraidMove), (Symm n).apply_braidMoveSequence bms l = l' from by
    rcases this with ⟨bms, h⟩
    rw[← h]
    exact demazure_of_braidMoveSequence l bms

  exact (Symm n).matsumoto_reduced l l' hr hr' h_eq

def DemazureOfProd (w : S (n + 1)) : LinearMap (RingHom.id ℂ) (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial (Fin (n + 1)) ℂ) :=
  DemazureOfWord (Classical.choose ((Symm n).exists_reduced_word' w))
