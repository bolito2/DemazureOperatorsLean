import DemazureOperators.Coxeter
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

lemma cons_of_length_succ {α : Type} (l : List α) {p : ℕ} (h : l.length = p + 1) :
  ∃ (a : α) (t : List α), l = a :: t ∧ t.length = p := by
  cases l with
  | nil =>
    simp at h
  | cons a t =>
    simp at h
    use a, t

theorem matsumoto_reduced_aux (p : ℕ) (l l' : List B) (hl : l.length = p) (hl' : l'.length = p)
(hr : cs.IsReduced l) (hr' : cs.IsReduced l') (h : π l = π l') :
  ∃ bms : List (cs.BraidMove), cs.apply_braidMove_sequence bms l = l' := by
  have h_len : l.length = l'.length := by rw[hl, hl']

  induction p with
  | zero =>
    simp at h_len
    use []
    simp[apply_braidMove_sequence]
    apply List.length_eq_zero.mp at hl
    apply List.length_eq_zero.mp at hl'
    rw[hl, hl']
  | succ p ih =>

    have ih' : ∃ (j : B) (t' : List B), l' = j :: t' := by
      match l' with
      | [] =>
        simp at h_len
      | j :: t' =>
        use j, t'
    rcases ih' with ⟨j, t', rfl⟩

    by_cases first_letter_eq : i = j
    · rw[first_letter_eq]
      simp[apply_braidMove_sequence]
      rw[List.foldr_cons t]

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
