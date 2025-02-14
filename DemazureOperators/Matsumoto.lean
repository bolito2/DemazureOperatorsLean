import DemazureOperators.StrongExchange
import Init.Data.List.Erase

set_option linter.unusedSectionVars false

namespace CoxeterSystem
noncomputable section

variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

instance : DecidableEq W := Classical.typeDecidableEq W

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "len" => cs.length

class MatsumotoCondition where
  one_le_M : ∀ i j : B, 1 ≤ M i j
  alternatingWords_ne_one : ∀ (i j : B) (_ : i ≠ j) (p : ℕ) (_ : 0 < p) (_ : p < M i j), (s i * s j) ^ p ≠ 1

structure NilMove (cs : CoxeterSystem M W) where
  i : B
  p : ℕ
structure BraidMove (cs : CoxeterSystem M W) where
  i : B
  j : B
  p : ℕ

inductive CoxeterMove(cs : CoxeterSystem M W) where
| nil : cs.NilMove → cs.CoxeterMove
| braid : cs.BraidMove → cs.CoxeterMove

def apply_nilMove (nm : cs.NilMove) (l : List B) : List B :=
  match nm with
  | NilMove.mk i p =>
    match p with
    | 0 =>
      if l.take 2 = [i, i] then
        l.drop 2
      else
        l
    | p + 1 =>
      match l with
      | [] => []
      | h::t => h :: apply_nilMove (NilMove.mk i p) t

def apply_braidMove (bm : cs.BraidMove) (l : List B) : List B :=
  match bm with
  | BraidMove.mk i j p =>
    match p with
    | 0 =>
      if l.take (M i j) = braidWord M i j then
        braidWord M j i ++ l.drop (M i j)
      else
        l
    | p + 1 =>
      match l with
      | [] => []
      | h::t => h :: apply_braidMove (BraidMove.mk i j p) t

def apply_coxeterMove (cm : cs.CoxeterMove) (l : List B) : List B :=
  match cm with
  | CoxeterMove.nil nm => cs.apply_nilMove nm l
  | CoxeterMove.braid bm => cs.apply_braidMove bm l

theorem nilMove_wordProd (nm : cs.NilMove) (l : List B) : π (cs.apply_nilMove nm l) = π l := by
  rcases nm with ⟨i, p⟩
  match p with
  | 0 =>
    simp[apply_nilMove]
    by_cases h : l.take 2 = [i, i]
    · simp[h]
      have h' : l = l.take 2 ++ l.drop 2 := by simp
      nth_rewrite 2 [h']
      rw[wordProd_append]
      rw[h]
      simp
      convert_to cs.wordProd ([i] ++ [i]) = 1
      rw[wordProd_append]
      simp
    · simp[h]
  | p + 1 =>
    match l with
    | [] => simp[apply_nilMove]
    | h::t =>
      simp[apply_nilMove, wordProd_cons]
      exact nilMove_wordProd (NilMove.mk i p) t

theorem braidMove_wordProd (bm : cs.BraidMove) (l : List B) : π (cs.apply_braidMove bm l) = π l := by
  rcases bm with ⟨i, j, p⟩
  match p with
    | 0 =>
      simp[apply_braidMove]
      by_cases h : List.take (M.M i j) l = braidWord M i j
      · simp[h]
        have h' : l = l.take (M.M i j) ++ l.drop (M.M i j) := by simp
        nth_rewrite 2 [h']
        repeat rw[wordProd_append]
        rw[h]
        simp[wordProd_braidWord_eq]
      · simp[h]
    | p + 1 =>
      match l with
      | [] => simp[apply_braidMove]
      | h::t =>
        simp[apply_braidMove, wordProd_cons]
        exact braidMove_wordProd (BraidMove.mk i j p) t

theorem coxeterMove_wordProd (cm : cs.CoxeterMove) (l : List B) : π (cs.apply_coxeterMove cm l) = π l := by
  cases cm with
  | nil nm => exact cs.nilMove_wordProd nm l
  | braid bm => exact cs.braidMove_wordProd bm l

def apply_coxeterMove_sequence (cms : List (cs.CoxeterMove)) (l : List B) : List B :=
  List.foldr (cs.apply_coxeterMove) l cms

example (nm : cs.NilMove) : cs.CoxeterMove := CoxeterMove.nil nm

def apply_braidMoveSequence (bms : List (cs.BraidMove)) (l : List B) : List B :=
  match bms with
  | [] => l
  | bm :: bms' => cs.apply_braidMove bm (apply_braidMoveSequence bms' l)

lemma apply_braidMoveSequence_cons (bm : cs.BraidMove) (bms : List (cs.BraidMove)) (l : List B) :
  cs.apply_braidMoveSequence (bm :: bms) l = cs.apply_braidMove bm (cs.apply_braidMoveSequence bms l) := by
  simp[apply_braidMoveSequence]

lemma cons_of_length_succ {α : Type} (l : List α) {p : ℕ} (h : l.length = p + 1) :
  ∃ (a : α) (t : List α), l = a :: t ∧ t.length = p := by
  cases l with
  | nil =>
    simp at h
  | cons a t =>
    simp at h
    use a, t

def shift_braidMove (bm : cs.BraidMove) : cs.BraidMove :=
  match bm with
  | BraidMove.mk i j p => BraidMove.mk i j (p + 1)

lemma braidMove_cons (bm : cs.BraidMove) (l : List B) (a : B) :
  a :: cs.apply_braidMove bm l = cs.apply_braidMove (cs.shift_braidMove bm) (a :: l) := by
  rcases bm with ⟨i, j, p⟩
  simp[shift_braidMove, apply_braidMove]

lemma braidMoveSequence_cons (bms : List (cs.BraidMove)) (l : List B) (a : B) :
  a :: cs.apply_braidMoveSequence bms l = cs.apply_braidMoveSequence (List.map cs.shift_braidMove bms) (a :: l) := by
  induction bms with
    | nil =>
       simp[apply_braidMoveSequence]
    | cons bm bms ih =>
      rw[apply_braidMoveSequence]
      rw[cs.braidMove_cons bm]
      simp[apply_braidMoveSequence] at ih
      rw[ih]
      simp[apply_braidMoveSequence_cons]

theorem isReduced_cons (a : B) (l : List B) : cs.IsReduced (a :: l) → cs.IsReduced l := by
  intro h
  have h' : l = (a::l).drop 1 := by simp
  rw[h']
  apply cs.isReduced_drop h

lemma leftDescent_of_cons (i : B) (l : List B) (hr : cs.IsReduced (i :: l)) : cs.IsLeftDescent (π (i :: l)) i := by
  apply cs.isLeftDescent_iff.mpr
  rw[hr]
  simp[wordProd_cons]
  rw[← IsReduced]
  apply cs.isReduced_cons i l hr

lemma leftInversion_of_cons (i : B) (l : List B) (hr : cs.IsReduced (i :: l)) : cs.IsLeftInversion (π (i :: l)) (s i) :=
  (cs.isLeftInversion_simple_iff_isLeftDescent (π (i :: l)) i).mpr (cs.leftDescent_of_cons i l hr)

theorem alternatingWord_succ_ne_alternatingWord_eraseIdx [MatsumotoCondition cs]
 (i j : B) (p : ℕ) (hp : p < M i j) (hij : i ≠ j) :
  ∀ (k : ℕ) (hk : k < p) ,π (alternatingWord i j (p + 1)) ≠ π (alternatingWord i j p).eraseIdx k := by
  revert i j

  induction p with
  | zero =>
    intro i j
    simp[alternatingWord, cs.wordProd_cons]
  | succ p ih =>
    intro i j hp hij k hk
    have hp' : p < M i j := by linarith
    have hp'' : p < M j i := by simp[M.symmetric]; exact hp'
    have zero_lt_p_succ : 0 < p + 1 := by linarith

    rw[alternatingWord_succ]
    nth_rewrite 2 [alternatingWord_succ]
    simp

    by_cases h_erase : k < (alternatingWord j i p).length
    · rw[List.eraseIdx_append_of_lt_length h_erase [j]]
      intro h_contra
      simp[cs.wordProd_append] at h_contra

      have hij' : j ≠ i := by
        intro h
        apply hij
        rw[h]
      have h_erase' : k < p := by simp at h_erase; exact h_erase

      apply ih j i hp'' hij' k h_erase' h_contra

    · have h_erase' : (alternatingWord j i p).length ≤ k := by
        apply Nat.le_of_not_lt
        exact h_erase

      rw[List.eraseIdx_append_of_length_le h_erase' [j]]
      have h_erase_k : [j].eraseIdx (k - (alternatingWord j i p).length) = [] := by
        apply List.eraseIdx_eq_nil.mpr
        right
        simp
        apply Nat.sub_eq_zero_iff_le.mpr
        linarith

      rw[h_erase_k]
      simp
      intro h_contra

      have : cs.wordProd (alternatingWord j i (p + 1) ++ [j]) = cs.wordProd (alternatingWord i j (p + 2)) := by
        simp[alternatingWord_succ]

      rw[this] at h_contra
      simp[prod_alternatingWord_eq_mul_pow] at h_contra
      by_cases p_even : Even p
      · have p_even' : Even (p + 2) := by
          apply Nat.even_add.mpr
          simp
          exact p_even
        simp[p_even, p_even'] at h_contra
        apply mul_inv_eq_one.mpr at h_contra
        rw[← inv_pow (s j * s i) (p/2)] at h_contra
        simp at h_contra
        rw[← pow_add] at h_contra
        have : p / 2 + 1 + p / 2 = p + 1 := by
          have : 2 * (p / 2) = p := Nat.two_mul_div_two_of_even p_even
          ring
          simp[mul_comm, this]
        rw[this] at h_contra

        apply MatsumotoCondition.alternatingWords_ne_one i j hij (p + 1) zero_lt_p_succ _ h_contra
        linarith

      · have p_odd : ¬ Even (p + 2) := by
          intro h
          apply Nat.even_add.mp at h
          simp[h] at p_even

        simp[p_even, p_odd] at h_contra
        apply (@mul_left_cancel_iff _ _ _ (s j) _ _).mpr at h_contra

        simp at h_contra
        rw[← mul_assoc] at h_contra
        let p_succ := p / 2 + 1
        have p_succ_ne_zero : p_succ ≠ 0 := by
          apply Nat.succ_ne_zero
        have : (p / 2) = p_succ - 1 := by
          simp[p_succ]
        rw[this] at h_contra
        rw[mul_pow_sub_one p_succ_ne_zero (s j * s i)] at h_contra

        simp[p_succ] at h_contra
        apply mul_inv_eq_one.mpr at h_contra
        rw[← inv_pow (s j * s i) (p/2 + 1)] at h_contra
        simp at h_contra
        rw[← pow_add] at h_contra

        have : p / 2 + 1 + (p / 2 + 1) = p + 1 := by
          ring
          convert_to 1 + 1 + p / 2 * 2 = p + 1
          rw[add_comm]
          simp at p_even
          rw[add_assoc]
          rw[Nat.one_add_div_two_mul_two_of_odd p_even]
          ring
        rw[this] at h_contra

        apply MatsumotoCondition.alternatingWords_ne_one i j hij (p + 1) zero_lt_p_succ _ h_contra
        linarith

lemma prefix_braidWord_aux [MatsumotoCondition cs]
(w : W) (l l' : List B) (i j : B) (i_ne_j : i ≠ j) (hil : π (i :: l) = w) (hjl' : π (j :: l') = w)
 (hr : cs.IsReduced (i :: l)) (hr' : cs.IsReduced (j :: l')) :
 ∀ (p : ℕ) (_ : p ≤ M i j), ∃ t : List B, π (alternatingWord i j p ++ t) = w ∧ cs.IsReduced (alternatingWord i j p ++ t) := by
  intro p
  induction p with
  | zero =>
    intro _
    simp[alternatingWord]
    use i :: l
  | succ p ih =>
    intro hp
    have hp' : p ≤ M i j := by linarith
    have hp'' : p < M i j := by linarith
    rcases ih hp' with ⟨t, ht, htr⟩
    rw[← ht]

    rw[alternatingWord_succ']
    by_cases p_even : Even p
    · simp[p_even]
      simp[cs.wordProd_cons]

      suffices ∃ k : Fin t.length, s j * cs.wordProd (alternatingWord i j p ++ t) =
      cs.wordProd (alternatingWord i j p ++ (t.eraseIdx k)) from by
        rcases this with ⟨k, hk⟩
        use (t.eraseIdx k)

        have hw :
          cs.simple j * cs.wordProd (alternatingWord i j p ++ t.eraseIdx k) =
          cs.wordProd (alternatingWord i j p ++ t)
        := by
          rw[← hk]
          simp[cs.wordProd_cons]

        constructor
        · exact hw
        · simp[IsReduced]
          simp[IsReduced] at htr
          rw[cs.wordProd_cons]
          rw[hw]
          rw[htr]
          rw[List.length_eraseIdx_of_lt k.2]
          simp[add_assoc]

          have : 1 ≤ t.length := by
            apply Nat.le_of_not_lt
            intro h'
            rw[Nat.lt_one_iff] at h'
            rw[h'] at k
            have wah := k.2
            linarith

          rw[Nat.sub_add_cancel this]


      have h_left_inversion_j : cs.IsLeftInversion (cs.wordProd (alternatingWord i j p ++ t)) (s j) := by
        rw[ht, ← hjl']
        apply cs.leftInversion_of_cons j l' hr'

      rcases cs.strongExchangeProperty (alternatingWord i j p ++ t) ⟨s j, cs.isReflection_simple j ⟩ h_left_inversion_j with ⟨k, hk⟩

      by_cases k_lt_len : k < p
      · exfalso
        have k_lt_len' : k < (alternatingWord i j p).length := by simp[k_lt_len]
        rw[List.eraseIdx_append_of_lt_length k_lt_len' t] at hk

        simp[cs.wordProd_append] at hk
        rw[← mul_assoc] at hk
        rw[mul_right_cancel_iff] at hk
        rw[← wordProd_cons] at hk
        have : j :: alternatingWord i j p = alternatingWord i j (p + 1) := by simp[alternatingWord_succ', p_even]
        rw[this] at hk
        exact cs.alternatingWord_succ_ne_alternatingWord_eraseIdx i j p hp'' i_ne_j k k_lt_len hk

      · simp at k_lt_len
        rw[List.eraseIdx_append_of_length_le] at hk
        rw[hk]
        have : k - (alternatingWord i j p).length < t.length := by
          have kle := k.2
          simp at kle
          simp
          apply (Nat.sub_lt_iff_lt_add _).mpr kle
          exact k_lt_len

        use ⟨k - (alternatingWord i j p).length, this⟩
        simp[k_lt_len]

    · simp[p_even]
      simp[cs.wordProd_cons]

      suffices ∃ k : Fin t.length, s i * cs.wordProd (alternatingWord i j p ++ t) =
      cs.wordProd (alternatingWord i j p ++ (t.eraseIdx k)) from by
        rcases this with ⟨k, hk⟩
        use (t.eraseIdx k)
        have hw :  cs.simple i * cs.wordProd (alternatingWord i j p ++ t.eraseIdx k) = cs.wordProd (alternatingWord i j p ++ t) := by
          rw[← hk]
          simp[cs.wordProd_cons]
        constructor
        · exact hw
        · simp[IsReduced]
          simp[IsReduced] at htr
          rw[cs.wordProd_cons]
          rw[hw]
          rw[htr]
          rw[List.length_eraseIdx_of_lt k.2]
          simp[add_assoc]

          have : 1 ≤ t.length := by
            apply Nat.le_of_not_lt
            intro h'
            rw[Nat.lt_one_iff] at h'
            rw[h'] at k
            have wah := k.2
            linarith

          rw[Nat.sub_add_cancel this]

      have h_left_inversion_i : cs.IsLeftInversion (cs.wordProd (alternatingWord i j p ++ t)) (s i) := by
        rw[ht, ← hil]
        apply cs.leftInversion_of_cons i l hr

      rcases cs.strongExchangeProperty (alternatingWord i j p ++ t) ⟨s i, cs.isReflection_simple i ⟩ h_left_inversion_i with ⟨k, hk⟩

      by_cases k_lt_len : k < p
      · exfalso
        have k_lt_len' : k < (alternatingWord i j p).length := by simp[k_lt_len]
        rw[List.eraseIdx_append_of_lt_length k_lt_len' t] at hk

        simp[cs.wordProd_append] at hk
        rw[← mul_assoc] at hk
        rw[mul_right_cancel_iff] at hk
        rw[← wordProd_cons] at hk
        have : i :: alternatingWord i j p = alternatingWord i j (p + 1) := by simp[alternatingWord_succ', p_even]
        rw[this] at hk
        exact cs.alternatingWord_succ_ne_alternatingWord_eraseIdx i j p hp'' i_ne_j k k_lt_len hk
      · simp at k_lt_len
        rw[List.eraseIdx_append_of_length_le] at hk
        rw[hk]
        have : k - (alternatingWord i j p).length < t.length := by
          have kle := k.2
          simp at kle
          simp
          apply (Nat.sub_lt_iff_lt_add _).mpr kle
          exact k_lt_len

        use ⟨k - (alternatingWord i j p).length, this⟩
        simp[k_lt_len]


lemma prefix_braidWord [MatsumotoCondition cs] (l l' : List B) (i j : B) (i_ne_j : i ≠ j) (pi_eq : π (i :: l) = π (j :: l'))
(hr : cs.IsReduced (i :: l)) (hr' : cs.IsReduced (j :: l')) :
  ∃ t : List B, π (i :: l) = π (braidWord M i j ++ t) ∧ cs.IsReduced (braidWord M i j ++ t) := by
  have h : M i j ≤ M i j := by linarith
  have h' : π (j :: l') = π (i :: l) := Eq.symm pi_eq

  rcases cs.prefix_braidWord_aux (π (i :: l)) l l' i j i_ne_j rfl h' hr hr' (M i j) h with ⟨t, ht, htr⟩
  use t
  rw[braidWord]
  constructor
  · simp[ht]
  · exact htr

theorem apply_braidMove_sequence_append (bms bms' : List (cs.BraidMove)) (l : List B) :
  cs.apply_braidMoveSequence (bms ++ bms') l = cs.apply_braidMoveSequence bms (cs.apply_braidMoveSequence bms' l) := by
  induction bms with
  | nil =>
    simp[apply_braidMoveSequence]
  | cons bm bms ih =>
    simp[apply_braidMoveSequence]
    apply congr_arg
    exact ih

theorem concatenate_braidMove_sequences (l l' l'' : List B) (h : ∃ bms : List (cs.BraidMove), cs.apply_braidMoveSequence bms l = l')
  (h' : ∃ bms' : List (cs.BraidMove), cs.apply_braidMoveSequence bms' l' = l'') :
  ∃ bms'' : List (cs.BraidMove), cs.apply_braidMoveSequence bms'' l = l'' := by
  rcases h with ⟨bms, hbms⟩
  rcases h' with ⟨bms', hbms'⟩
  use bms' ++ bms
  simp[apply_braidMove_sequence_append]
  simp[hbms', hbms]

-- move to aux file
theorem isReduced_of_eq_length (l l' : List B) (h_len : l.length = l'.length) (h_eq : π l = π l')
   (hr : cs.IsReduced l) : cs.IsReduced l' := by
  simp[IsReduced]
  simp[IsReduced] at hr

  calc
    len π l' = len π l := by rw[h_eq]
    _ = l.length := by rw[hr]
    _ = l'.length := by rw[h_len]

theorem eq_length_of_isReduced (l l' : List B)
(h_eq : π l = π l') (hr : cs.IsReduced l) (hr' : cs.IsReduced l') :
    l.length = l'.length := by
  rw[IsReduced] at hr
  rw[IsReduced] at hr'

  calc l.length = len π l := by rw[hr]
    _ = len π l' := by rw[h_eq]
    _ = l'.length := by rw[hr']

lemma matsumoto_reduced_inductionStep_of_firstLetterEq (p : ℕ) (l_t l'_t : List B) (i : B)
(len_l_t_eq_p : l_t.length = p) (len_l'_t_eq_p : l'_t.length = p) (h_eq : π (i :: l_t) = π (i :: l'_t))
(l_reduced : cs.IsReduced (i :: l_t)) (l'_reduced : cs.IsReduced (i :: l'_t))
(ih: ∀ (l l' : List B),
  l.length = p →
    l'.length = p →
      cs.IsReduced l → cs.IsReduced l' → cs.wordProd l = cs.wordProd l' → ∃ bms, cs.apply_braidMoveSequence bms l = l'):
∃ bms, cs.apply_braidMoveSequence bms (i :: l_t) = i :: l'_t := by

  have htr : cs.IsReduced l_t := cs.isReduced_cons i l_t l_reduced
  have htr' : cs.IsReduced l'_t := cs.isReduced_cons i l'_t l'_reduced

  have h_prod : π l_t = π l'_t := by
    apply @mul_left_cancel _ _ _ (cs.simple i) _ _
    rw[← cs.wordProd_cons i l_t, ← cs.wordProd_cons i l'_t, h_eq]


  have ⟨bms, ih'⟩ := ih l_t l'_t len_l_t_eq_p len_l'_t_eq_p htr htr' h_prod

  apply (List.cons_inj_right i).mpr at ih'
  rw[← ih']
  rw[braidMoveSequence_cons]
  use (List.map cs.shift_braidMove bms)

theorem matsumoto_reduced_aux [MatsumotoCondition cs] (p : ℕ) (l l' : List B)
(len_l_eq_p : l.length = p) (len_l'_eq_p : l'.length = p)
(l_reduced : cs.IsReduced l) (l'_reduced : cs.IsReduced l') (h_eq : π l = π l') :
  ∃ bms : List (cs.BraidMove), cs.apply_braidMoveSequence bms l = l' := by

  revert l l'
  induction p with
  | zero =>
    intro l l' hl hl' _ _ _
    have h_len : l.length = l'.length := by rw[hl, hl']
    simp at h_len
    use []
    simp[apply_braidMoveSequence]
    apply List.length_eq_zero.mp at hl
    apply List.length_eq_zero.mp at hl'
    rw[hl, hl']
  | succ p ih =>
    intro l l' len_l_eq_p len_l'_eq_p l_reduced l'_reduced h_eq
    rcases cons_of_length_succ l len_l_eq_p with ⟨i, l_t, rfl, len_l_t_eq_p⟩
    rcases cons_of_length_succ l' len_l'_eq_p with ⟨j, l'_t, rfl, len_l'_t_eq_p⟩

    by_cases first_letter_eq : i = j
    · rw[first_letter_eq]
      rw[first_letter_eq] at h_eq
      rw[first_letter_eq] at l_reduced

      apply cs.matsumoto_reduced_inductionStep_of_firstLetterEq p l_t l'_t j len_l_t_eq_p len_l'_t_eq_p h_eq l_reduced l'_reduced
      exact ih

    · obtain ⟨m, hm⟩ : ∃ m : ℕ ,M i j = m + 1 := by
        use M i j - 1
        simp[MatsumotoCondition.one_le_M cs i j]

      have hm' : M j i = m + 1 := by
        simp[M.symmetric]
        exact hm

      by_cases m_even : Even m
      · have j_ne_i : j ≠ i := by
          simp[first_letter_eq]
          intro heq
          rw[heq] at first_letter_eq
          contradiction

        obtain ⟨b_tail, hb, b_reduced⟩ :=
          cs.prefix_braidWord l'_t l_t j i j_ne_i (Eq.symm h_eq) l'_reduced l_reduced

        have hb' : cs.wordProd (i :: l_t) = cs.wordProd (braidWord M j i ++ b_tail) := by
          rw[← hb]
          exact h_eq

        apply cs.concatenate_braidMove_sequences (i :: l_t) (braidWord M j i ++ b_tail) (j :: l'_t)

        have b_word_cons : (braidWord M j i ++ b_tail) = i :: (alternatingWord j i m ++ b_tail) := by
          simp[braidWord]
          rw[hm']
          simp[alternatingWord_succ']
          simp[m_even]

        rw[b_word_cons]

        have b_len_p : (alternatingWord j i m ++ b_tail).length = p := by
          suffices (braidWord M j i ++ b_tail).length = p + 1 from by
            simp[braidWord] at this
            rw[hm'] at this
            simp[alternatingWord]
            nth_rewrite 1 [add_comm] at this
            rw[← add_assoc] at this
            simp at this
            rw[← this]
            ring
          rw[← cs.eq_length_of_isReduced (i :: l_t) (braidWord M j i ++ b_tail) hb' l_reduced b_reduced]
          exact len_l_eq_p

        rw[b_word_cons] at hb'
        rw[b_word_cons] at b_reduced
        apply cs.matsumoto_reduced_inductionStep_of_firstLetterEq p l_t (alternatingWord j i m ++ b_tail) i len_l_t_eq_p b_len_p hb' l_reduced b_reduced ih

        apply cs.concatenate_braidMove_sequences (braidWord M j i ++ b_tail) (braidWord M i j ++ b_tail) (j :: l'_t)

        use [BraidMove.mk j i 0]
        simp[apply_braidMoveSequence]
        simp[apply_braidMove]

        simp[braidWord]
        rw[hm]
        rw[alternatingWord_succ']
        simp[m_even]

        have switch_braidWord : π (braidWord M j i ++ b_tail) = π (braidWord M i j ++ b_tail) := by
          simp[wordProd_append]
          rw[cs.wordProd_braidWord_eq j i]

        rw[switch_braidWord] at hb'
        have b_reduced' : cs.IsReduced (braidWord M i j ++ b_tail) := by
          apply cs.isReduced_of_eq_length (braidWord M j i ++ b_tail) (braidWord M i j ++ b_tail)
          simp[M.symmetric]
          exact switch_braidWord
          exact b_reduced

        have hb' : cs.wordProd (j :: l'_t) = cs.wordProd (braidWord M i j ++ b_tail) := by
          rw[← hb']
          exact Eq.symm h_eq

        have b_word_cons : (braidWord M i j ++ b_tail) = j :: (alternatingWord i j m ++ b_tail) := by
          simp[braidWord]
          rw[hm]
          simp[alternatingWord_succ']
          simp[m_even]

        have b_len_p : (alternatingWord i j m ++ b_tail).length = p := by
          suffices (braidWord M i j ++ b_tail).length = p + 1 from by
            simp[braidWord] at this
            rw[hm] at this
            simp[alternatingWord]
            nth_rewrite 1 [add_comm] at this
            rw[← add_assoc] at this
            simp at this
            rw[← this]
            ring
          rw[← cs.eq_length_of_isReduced (j :: l'_t) (braidWord M i j ++ b_tail) hb' l'_reduced b_reduced']
          exact len_l'_eq_p

        rw[b_word_cons] at hb'
        rw[b_word_cons] at b_reduced'

        apply cs.matsumoto_reduced_inductionStep_of_firstLetterEq p (alternatingWord i j m ++ b_tail)
          l'_t j b_len_p len_l'_t_eq_p (Eq.symm hb') b_reduced' l'_reduced ih

      · rcases cs.prefix_braidWord l_t l'_t i j first_letter_eq h_eq l_reduced l'_reduced with ⟨b_tail, hb, b_reduced⟩
        apply cs.concatenate_braidMove_sequences (i :: l_t) (braidWord M i j ++ b_tail) (j :: l'_t)

        simp[braidWord]
        rw[hm]
        rw[alternatingWord_succ']
        simp[m_even]

        have b_word_cons : (braidWord M i j ++ b_tail) = i :: (alternatingWord i j m ++ b_tail) := by
          simp[braidWord]
          rw[hm]
          simp[alternatingWord_succ']
          simp[m_even]

        have b_len_p : (alternatingWord i j m ++ b_tail).length = p := by
          suffices (braidWord M i j ++ b_tail).length = p + 1 from by
            simp[braidWord] at this
            rw[hm] at this
            simp[alternatingWord]
            nth_rewrite 1 [add_comm] at this
            rw[← add_assoc] at this
            simp at this
            rw[← this]
            ring
          rw[← cs.eq_length_of_isReduced (i :: l_t) (braidWord M i j ++ b_tail) hb l_reduced b_reduced]
          exact len_l_eq_p

        have i_tail_reduced : cs.IsReduced l_t := by
          apply cs.isReduced_cons i l_t l_reduced

        have aword_is_reduced : cs.IsReduced (alternatingWord i j m ++ b_tail) := by
          apply cs.isReduced_cons i ((alternatingWord i j m) ++ b_tail)
          rw[← b_word_cons]
          exact b_reduced

        have i_tail_eq_aword : π l_t = π (alternatingWord i j m ++ b_tail) := by
          rw[b_word_cons] at hb
          simp[wordProd_cons] at hb
          exact hb

        rcases ih l_t (alternatingWord i j m ++ b_tail) len_l_t_eq_p b_len_p i_tail_reduced aword_is_reduced i_tail_eq_aword with ⟨bms, ih'⟩

        use (List.map cs.shift_braidMove bms)

        rw[← braidMoveSequence_cons]
        suffices cs.apply_braidMoveSequence bms l_t = (alternatingWord i j m ++ b_tail) from by
          rw[this]
        exact ih'

        apply cs.concatenate_braidMove_sequences (braidWord M i j ++ b_tail) (braidWord M j i ++ b_tail) (j :: l'_t)

        use [BraidMove.mk i j 0]
        simp[apply_braidMoveSequence]
        simp[apply_braidMove]

        simp[braidWord]
        rw[hm']
        rw[alternatingWord_succ']
        simp[m_even]

        have b_word_cons : (braidWord M j i ++ b_tail) = j :: (alternatingWord j i m ++ b_tail) := by
          simp[braidWord]
          rw[hm']
          simp[alternatingWord_succ']
          simp[m_even]

        have switch_braidWord : π (braidWord M j i ++ b_tail) = π (braidWord M i j ++ b_tail) := by
          simp[wordProd_append]
          rw[cs.wordProd_braidWord_eq j i]

        have hb' : cs.wordProd (j :: l'_t) = cs.wordProd (braidWord M j i ++ b_tail) := by
          rw[switch_braidWord]
          rw[← hb]
          exact Eq.symm h_eq

        have b_reduced' : cs.IsReduced (braidWord M j i ++ b_tail) := by
          apply cs.isReduced_of_eq_length (braidWord M i j ++ b_tail) (braidWord M j i ++ b_tail)
          simp[M.symmetric]
          exact Eq.symm switch_braidWord
          exact b_reduced

        have b_len_p : (alternatingWord j i m ++ b_tail).length = p := by
          suffices (braidWord M j i ++ b_tail).length = p + 1 from by
            simp[braidWord] at this
            rw[hm'] at this
            simp[alternatingWord]
            nth_rewrite 1 [add_comm] at this
            rw[← add_assoc] at this
            simp at this
            rw[← this]
            ring
          rw[← cs.eq_length_of_isReduced (j :: l'_t) (braidWord M j i ++ b_tail) hb' l'_reduced b_reduced']
          exact len_l'_eq_p

        have j_tail_reduced : cs.IsReduced l'_t := by
          apply cs.isReduced_cons j l'_t l'_reduced

        have aword_is_reduced : cs.IsReduced (alternatingWord j i m ++ b_tail) := by
          apply cs.isReduced_cons j ((alternatingWord j i m) ++ b_tail)
          rw[← b_word_cons]
          exact b_reduced'

        have j_tail_eq_aword : π (alternatingWord j i m ++ b_tail) = π l'_t := by
          rw[b_word_cons] at hb'
          simp[wordProd_cons] at hb'
          exact Eq.symm hb'

        rcases ih (alternatingWord j i m ++ b_tail) l'_t b_len_p len_l'_t_eq_p aword_is_reduced j_tail_reduced j_tail_eq_aword with ⟨bms, ih'⟩

        use (List.map cs.shift_braidMove bms)
        rw[← braidMoveSequence_cons]
        suffices cs.apply_braidMoveSequence bms (alternatingWord j i m ++ b_tail) = l'_t from by
          rw[this]
        exact ih'


theorem matsumoto_reduced [MatsumotoCondition cs] (l l' : List B)
(hr : cs.IsReduced l) (hr' : cs.IsReduced l') (h : π l = π l') :
  ∃ bms : List (cs.BraidMove), cs.apply_braidMoveSequence bms l = l' := by
  apply cs.matsumoto_reduced_aux (l.length) l l' rfl _ hr hr' h
  calc
      l'.length = len (π l') := by
        rw[IsReduced] at hr'
        rw[← hr']
      _ = len (π l) := by rw[h]
      _ = l.length := by
        rw[IsReduced] at hr
        rw[← hr]
