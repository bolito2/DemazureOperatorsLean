import DemazureOperators.Coxeter

set_option linter.unusedSectionVars false

namespace CoxeterSystem

variable {B : Type}  [DecidableEq B]
variable {W : Type} [Group W] [DecidableEq W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

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
        braidWord M i j ++ l.drop (M i j)
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

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

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

def apply_braidMove_sequence (bms : List (cs.BraidMove)) (l : List B) : List B :=
  List.foldr (cs.apply_braidMove) l bms

lemma apply_braidMove_sequence_cons (bm : cs.BraidMove) (bms : List (cs.BraidMove)) (l : List B) :
  cs.apply_braidMove_sequence (bm :: bms) l = cs.apply_braidMove bm (cs.apply_braidMove_sequence bms l) := by
  simp[apply_braidMove_sequence]

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
  a :: cs.apply_braidMove_sequence bms l = cs.apply_braidMove_sequence (List.map cs.shift_braidMove bms) (a :: l) := by
  induction bms with
    | nil =>
       simp[apply_braidMove_sequence]
    | cons bm bms ih =>
      rw[apply_braidMove_sequence]
      rw[List.foldr_cons bms]
      rw[cs.braidMove_cons bm]
      rw[apply_braidMove_sequence] at ih
      rw[ih]
      simp[apply_braidMove_sequence_cons]

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

lemma leftInversion_of_cons (i : B) (l : List B) (hr : cs.IsReduced (i :: l)) : cs.IsLeftInversion (π (i :: l)) (s i) := by
  apply (cs.isLeftInversion_simple_iff_isLeftDescent (π (i :: l)) i).mpr (cs.leftDescent_of_cons i l hr)

theorem simple_injective (i j : B) (h : i ≠ j) : cs.simple i ≠ cs.simple j := by sorry

theorem contradiction_of_mul_simple_eq_one (i j : B) (h : i ≠ j) (h' : cs.simple i * cs.simple j = 1) : False := by
  apply cs.simple_injective i j h
  apply (@mul_left_cancel_iff _ _ _ (s i)).mp
  simp[h']

theorem alternatingWord_succ_ne_alternatingWord_eraseIdx (i j : B) (p : ℕ) (hp : p < M i j) (hij : i ≠ j) :
  ∀ (k : ℕ) (hk : k < p) ,π (alternatingWord i j (p + 1)) ≠ π (alternatingWord i j p).eraseIdx k := by sorry
  -- we need the permutation representation to prove this --

lemma prefix_braidWord_aux (w : W) (l l' : List B) (i j : B) (i_ne_j : i ≠ j) (hil : π (i :: l) = w) (hjl' : π (j :: l') = w)
 (hr : cs.IsReduced (i :: l)) (hr' : cs.IsReduced (j :: l')) :
 ∀ (p : ℕ) (h : p ≤ M i j), ∃ t : List B, π (alternatingWord i j p ++ t) = w ∧ cs.IsReduced (alternatingWord i j p ++ t) := by
  intro p
  induction p with
  | zero =>
    intro h
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
        have hw :  cs.simple j * cs.wordProd (alternatingWord i j p ++ t.eraseIdx k) = cs.wordProd (alternatingWord i j p ++ t) := by
          rw[← hk]
          simp[cs.wordProd_cons]
        constructor
        · exact hw
        · simp[IsReduced]
          simp[IsReduced] at htr
          rw[cs.wordProd_cons]
          rw[hw]
          rw[htr]
          rw[List.length_eraseIdx k.2]
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
          rw[List.length_eraseIdx k.2]
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


lemma prefix_braidWord (l l' : List B) (i j : B) (i_ne_j : i ≠ j) (pi_eq : π (i :: l) = π (j :: l'))
(hr : cs.IsReduced (i :: l)) (hr' : cs.IsReduced (j :: l')) :
  ∃ t : List B, π (i :: l) = π (braidWord M i j ++ t) ∧ cs.IsReduced (braidWord M i j ++ t) := by
  have h : M i j ≤ M i j := by linarith
  have h' : π (j :: l') = π (i :: l) := by rw[← pi_eq]

  rcases cs.prefix_braidWord_aux (π (i :: l)) l l' i j i_ne_j rfl h' hr hr' (M i j) h with ⟨t, ht, htr⟩
  use t
  rw[braidWord]
  constructor
  · simp[ht]
  · exact htr

theorem matsumoto_reduced_aux (p : ℕ) (l l' : List B) (hl : l.length = p) (hl' : l'.length = p)
(hr : cs.IsReduced l) (hr' : cs.IsReduced l') (h : π l = π l') :
  ∃ bms : List (cs.BraidMove), cs.apply_braidMove_sequence bms l = l' := by

  revert l l'
  induction p with
  | zero =>
    intro l l' hl hl' hr hr' h
    have h_len : l.length = l'.length := by rw[hl, hl']
    simp at h_len
    use []
    simp[apply_braidMove_sequence]
    apply List.length_eq_zero.mp at hl
    apply List.length_eq_zero.mp at hl'
    rw[hl, hl']
  | succ p ih =>
    intro l l' hl hl' hr hr' h
    rcases cons_of_length_succ l hl with ⟨i, t, rfl, ht⟩
    rcases cons_of_length_succ l' hl' with ⟨j, t', rfl, ht'⟩

    by_cases first_letter_eq : i = j
    · rw[first_letter_eq]
      have htr : cs.IsReduced t := by
        convert_to cs.IsReduced (List.drop 1 (i :: t))
        apply cs.isReduced_drop hr
      have htr' : cs.IsReduced t' := by
        convert_to cs.IsReduced (List.drop 1 (j :: t'))
        apply cs.isReduced_drop hr'

      have h_prod : π t = π t' := by
        apply @mul_left_cancel _ _ _ (cs.simple i) _ _
        rw[← cs.wordProd_cons i t, ← cs.wordProd_cons i t', h]
        rw[← first_letter_eq]

      have ih' := ih t t' ht ht' htr htr' h_prod
      rcases ih' with ⟨bms, ih'⟩
      apply (List.cons_inj_right j).mpr at ih'
      rw[← ih']
      rw[braidMoveSequence_cons]
      use (List.map cs.shift_braidMove bms)




theorem matsumoto_reduced (l l' : List B) (hr : cs.IsReduced l) (hr' : cs.IsReduced l') (h : π l = π l') :
  ∃ bms : List (cs.BraidMove), cs.apply_braidMove_sequence bms l = l' := by
  apply cs.matsumoto_reduced_aux (l.length) l l' rfl _ hr hr' h
  calc
      l'.length = ℓ (π l') := by
        rw[IsReduced] at hr'
        rw[← hr']
      _ = ℓ (π l) := by rw[h]
      _ = l.length := by
        rw[IsReduced] at hr
        rw[← hr]
