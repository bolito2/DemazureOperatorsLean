import LeanCourse.Project.Demazure

set_option maxHeartbeats 10000000

noncomputable section
open MvPolynomial

namespace Demazure

variable {n : ℕ} (n_pos : n > 0) (n_gt_1 : n > 1)

/- We are going to define the Demazure operator acting on polynomial fractions. For this,
we first define a structure to represent these fractions, and then we will quotient it by
the proportionality equivalence relation -/

structure PolyFraction' (n : ℕ) where
  numerator : MvPolynomial (Fin (n + 1)) ℂ
  denominator : MvPolynomial (Fin (n + 1)) ℂ
  denominator_ne_zero : denominator ≠ 0


def r (n : ℕ) : PolyFraction' n → PolyFraction' n → Prop :=
  fun p q => p.numerator * q.denominator = q.numerator * p.denominator

lemma r_equiv : Equivalence (r n) := by
  constructor
  intro p
  simp[r]
  ring
  intro p q
  simp[r]
  ring
  intro h
  simp[h]
  intro x y z
  simp[r]
  intro h1 h2

  by_cases h3 : y.numerator = 0
  simp[h3, y.denominator_ne_zero] at h1
  simp[h3, y.denominator_ne_zero] at h2
  simp[h1, h2, h3]

  apply poly_cancel_left y.denominator_ne_zero
  apply poly_cancel_left h3
  ring
  rw[mul_assoc y.numerator]
  rw[mul_comm y.denominator x.numerator]
  rw[h1]
  rw[mul_comm y.numerator (y.numerator * x.denominator)]
  rw[mul_assoc]
  rw[h2]
  ring

instance s (n : ℕ) : Setoid (PolyFraction' n) where
  r := r n
  iseqv := r_equiv

-- The quotient ring and the canonical projections from fractions and polynomials
def PolyFraction (n : ℕ) := (Quotient (s n))

def mk (p : PolyFraction' n) : PolyFraction n := Quotient.mk (s n) p
def to_frac (p : MvPolynomial (Fin (n + 1)) ℂ) : PolyFraction' n := ⟨p, 1, one_ne_zero⟩
def mk' (p : MvPolynomial (Fin (n + 1)) ℂ) : PolyFraction n := mk ⟨p, 1, one_ne_zero⟩

instance has_equiv : HasEquiv (PolyFraction' n) := instHasEquiv

lemma equiv_r {a b : PolyFraction' n} : (r n) a b ↔ a ≈ b := by
  rfl

/- This lemmas enables us to compute the result of a lift of a function applied at a
 representant class.
  simp doesn't work here since it detects that complexity goes up, so we have to do it manually with rw[lift_r] -/
lemma lift_r {a: PolyFraction' n} {f : PolyFraction' n → PolyFraction' n}
{c :  ∀ (a₁ a₂ : PolyFraction' n), a₁ ≈ a₂ → (mk ∘ f) a₁ = (mk ∘ f) a₂} : Quotient.lift (mk ∘ f) c (mk a) = mk (f a) := by
  rfl
@[simp]
lemma lift2_r {a b : PolyFraction' n} {f : PolyFraction' n → PolyFraction' n → PolyFraction n}
{c :  ∀ (a₁ b₁ a₂ b₂ : PolyFraction' n), a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂} : Quotient.lift₂ f c (mk a) (mk b) = f a b := by
  rfl

/- Two projections are equal iff the representants are proportional -/
@[simp]
lemma mk_eq {a b : PolyFraction' n} : mk a = mk b ↔ a.numerator*b.denominator = a.denominator*b.numerator := by
  constructor
  intro h
  simp[mk] at h
  rw[Quotient.eq] at h
  rw[← equiv_r] at h
  simp[r] at h
  rw[h]
  ring
  simp[mk]
  intro h
  apply Quotient.sound
  rw[← equiv_r]
  simp[r]
  rw[h]
  ring

-- function to get a representant of a fraction
lemma get_polyfraction_rep (p : PolyFraction n) : ∃p' : PolyFraction' n, mk p' = p := by
    simp[mk]
    apply Quotient.exists_rep p

-- Basic operations of polynomial functions
def add' {n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction' n :=
  fun p q => ⟨p.numerator * q.denominator + q.numerator * p.denominator, p.denominator * q.denominator, mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero⟩

def add_mk {n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction n :=
  fun p q => mk (add' p q)

lemma add'_s {n : ℕ} : ∀ a₁ b₁ a₂ b₂ : PolyFraction' n, a₁ ≈ a₂ → b₁ ≈ b₂ → add_mk a₁ b₁ = add_mk a₂ b₂ := by
  intro a1 b1 a2 b2
  intro h1 h2
  simp[add_mk, add']
  ring
  rw[← equiv_r] at h1
  rw[← equiv_r] at h2
  simp[r] at h1
  simp[r] at h2

  rw[mul_comm a1.numerator]
  rw[mul_assoc b1.denominator]
  rw[h1]

  rw[mul_comm b1.numerator]
  rw[mul_assoc a1.denominator]
  rw[mul_comm b1.numerator]
  rw[mul_assoc a1.denominator]
  rw[mul_assoc a2.denominator]
  rw[h2]
  ring

def add : PolyFraction n → PolyFraction n → PolyFraction n :=
  fun p q ↦ Quotient.lift₂ (add_mk) (add'_s) p q

-- Enable use of + notation
instance addition : Add (PolyFraction n) := ⟨add⟩
instance addition' : Add (PolyFraction' n) := ⟨add'⟩

def sub' {n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction n :=
  fun p q ↦ mk ⟨p.numerator * q.denominator - q.numerator * p.denominator, p.denominator * q.denominator, mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero⟩

lemma sub'_s {n : ℕ} : ∀ a₁ b₁ a₂ b₂ : PolyFraction' n, a₁ ≈ a₂ → b₁ ≈ b₂ → (sub' a₁ b₁) = (sub' a₂ b₂) := by
  intro a1 b1 a2 b2
  intro h1 h2
  simp[sub']
  ring
  rw[← equiv_r] at h1
  rw[← equiv_r] at h2
  simp[r] at h1
  simp[r] at h2

  rw[mul_comm a1.numerator]
  rw[mul_assoc b1.denominator]
  rw[h1]

  rw[mul_comm b1.numerator]
  rw[mul_assoc a1.denominator]
  rw[mul_comm b1.numerator]
  rw[mul_assoc a1.denominator]
  rw[mul_assoc a2.denominator]
  rw[h2]
  ring

def sub : PolyFraction n → PolyFraction n → PolyFraction n :=
  fun p q ↦ Quotient.lift₂ (sub') (sub'_s) p q

-- Enable use of * notation
def mul'{n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction' n :=
  fun p q => ⟨p.numerator * q.numerator, p.denominator * q.denominator, mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero⟩

def mul_mk {n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction n :=
  fun p q => mk (mul' p q)

lemma mul'_s {n : ℕ} : ∀ a₁ b₁ a₂ b₂ : PolyFraction' n, a₁ ≈ a₂ → b₁ ≈ b₂ → (mul_mk a₁ b₁) = (mul_mk a₂ b₂) := by
  intro a1 b1 a2 b2
  intro h1 h2
  simp[mul_mk, mul']
  ring
  rw[← equiv_r] at h1
  rw[← equiv_r] at h2
  simp[r] at h1
  simp[r] at h2

  rw[mul_comm a1.numerator]
  rw[mul_assoc b1.numerator]
  rw[h1]

  rw[mul_comm b1.numerator]
  rw[mul_assoc (a2.numerator * a1.denominator)]
  rw[h2]
  ring

def mul : PolyFraction n → PolyFraction n → PolyFraction n :=
  fun p q ↦ Quotient.lift₂ (mul_mk) (mul'_s) p q

-- Enable use of * notation
instance multiplication' : Mul (PolyFraction' n) := ⟨mul'⟩
instance multiplication : Mul (PolyFraction n) := ⟨mul⟩

@[simp]
def one' : PolyFraction' n where
  numerator := 1
  denominator := 1
  denominator_ne_zero := one_ne_zero

def one : PolyFraction n := mk one'

@[simp]
def zero' : PolyFraction' n where
  numerator := 0
  denominator := 1
  denominator_ne_zero := one_ne_zero

def zero : PolyFraction n := mk zero'

def neg' (p : PolyFraction' n) : PolyFraction' n :=
  ⟨-p.numerator, p.denominator, p.denominator_ne_zero⟩

def neg_mk (p : PolyFraction' n) : PolyFraction n := mk (neg' p)

lemma neg_s (n : ℕ) : ∀ (a₁ a₂ : PolyFraction' n), a₁ ≈ a₂ → (neg_mk a₁) = (neg_mk a₂) := by
  intro a1 a2
  intro h
  simp[neg_mk, neg']
  ring
  rw[← equiv_r] at h
  simp[r] at h
  rw[h]
  ring

def neg (p : PolyFraction n) : PolyFraction n := Quotient.lift neg_mk (neg_s n) p

-- some basic properties of these operations
@[simp]
lemma add_comm (p q : PolyFraction n) : add p q = add q p := by
  rcases get_polyfraction_rep p with ⟨p', hp⟩
  rcases get_polyfraction_rep q with ⟨q', hq⟩
  simp[add]
  rw[← hp]
  rw[← hq]
  simp[lift2_r]
  simp[add_mk, add']
  ring

@[simp]
lemma add_assoc (p q r : PolyFraction n) : add (add p q) r = add p (add q r) := by
  rcases get_polyfraction_rep p with ⟨p', hp⟩
  rcases get_polyfraction_rep q with ⟨q', hq⟩
  rcases get_polyfraction_rep r with ⟨r', hr⟩
  rw[← hp]
  rw[← hq]
  rw[← hr]

  have hpq : (add (mk p') (mk q')) = mk (add' p' q') := by
    simp[add, add_mk]

  have hqr : (add (mk q') (mk r')) = mk (add' q' r') := by
    simp[add, add_mk]

  rw[hpq, hqr]
  simp[add, lift2_r]
  simp[add']
  apply Quotient.sound
  apply equiv_r.mp
  simp[Demazure.r, add']
  ring

-- We don't prove that it is a ring since we don't need all the properties for our use

/- We directly define the Demazure operator on fractions (even though we proved that
the result is a polynomial, for the proofs it's better to keep the result as a fraction)-/
def DemAux' (i : Fin n) : PolyFraction' n →  PolyFraction' n := fun p =>
   ⟨
    p.numerator * (SwapVariables (Fin.castSucc i) (Fin.succ i) p.denominator) - (SwapVariables (Fin.castSucc i) (Fin.succ i) p.numerator) * p.denominator,
    p.denominator * (SwapVariables (Fin.castSucc i) (Fin.succ i) p.denominator) * (X (Fin.castSucc i) - X (Fin.succ i)),
    mul_ne_zero (mul_ne_zero p.denominator_ne_zero (swap_variables_ne_zero (Fin.castSucc i) (Fin.succ i) p.denominator p.denominator_ne_zero)) (wario i)
    ⟩

lemma DemAux_well_defined (i : Fin n) : ∀ (p q : PolyFraction' n) (h : p ≈ q), ((mk ∘ DemAux' i) p) = ((mk ∘ DemAux' i) q) := by
  intro p q h
  simp[DemAux']
  rw[← equiv_r] at h
  simp[r] at h
  ring
  rw[mul_comm p.numerator]
  rw[mul_assoc (SwapVariablesFun (Fin.castSucc i) (Fin.succ i) p.denominator)]
  rw[h]

  rw[mul_comm (SwapVariablesFun (Fin.castSucc i) (Fin.succ i) p.numerator)]
  rw[mul_assoc p.denominator]
  rw[mul_comm (SwapVariablesFun (Fin.castSucc i) (Fin.succ i) p.numerator)]
  rw[mul_assoc p.denominator]
  rw[mul_assoc q.denominator]
  rw[← swap_variables_mul]
  rw[h]

  simp[swap_variables_mul]
  ring

-- Define the Demazure operator on the quotient
def DemAux (i : Fin n) (p : PolyFraction n) : PolyFraction n :=
  Quotient.lift (mk ∘ (DemAux' i)) (DemAux_well_defined i) p

/- This definition is equivalent to the direct one on the polynomial ring-/
lemma demazure_definitions_equivalent' : ∀ i : Fin n, ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  mk (DemAux' i (to_frac p)) = mk' (DemazureFun i p) := by
  intro i p
  simp[mk']
  simp[DemAux', to_frac]

  have h : DemazureDenominator i * ((DemazureNumerator i p) /ₘ (DemazureDenominator i)) = DemazureNumerator i p := demazure_division_exact' i p

  apply (SwapVariables (Fin.castSucc i) (0 : Fin (n + 1))).injective
  apply (MvPolynomial.finSuccEquiv ℂ n).injective

  have h2 : DemazureNumerator i p =  (MvPolynomial.finSuccEquiv ℂ n)
    ((SwapVariables (Fin.castSucc i) 0) (p - SwapVariablesFun (Fin.castSucc i) (Fin.succ i) p)) := by
    simp [DemazureNumerator]


  rw[← h2]
  rw[← h]
  simp [SwapVariables]
  rw[swap_variables_none (fin_succ_ne_fin_castSucc i) (Fin.succ_ne_zero i)]
  simp

  have h3 : DemazureDenominator i = Polynomial.X - Polynomial.C (X i) := by
    simp [DemazureDenominator]

  rw[← h3]
  rw[← poly_mul_cancel (demazure_denominator_ne_zero i)]
  simp[DemazureFun]
  have h4 {q : MvPolynomial (Fin (n + 1)) ℂ } : eval₂ (RingHom.comp Polynomial.C C) (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (X k)) i)
    q = (MvPolynomial.finSuccEquiv ℂ n) q := by
    simp
  rw[h4]
  nth_rewrite 1 [← AlgEquiv.coe_apply_coe_coe_symm_apply (finSuccEquiv ℂ n) (DemazureNumerator i p /ₘ DemazureDenominator i)]
  rfl

lemma demazure_definitions_equivalent : ∀ i : Fin n, ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  DemAux i (mk' p) = mk' (DemazureFun i p) := by
  intro i p
  rw[mk']
  simp[DemAux]
  rw[lift_r]
  rw[← demazure_definitions_equivalent' i p]
  rfl

/- We can prove equalities in the ring of polynomials by reducing to the polynomial fraction case.
This sets the strategy for proving properties of the Demazure operator:

Prove them for DemAux (in DemazureAuxRelations.lean) and then use these lemmas and the equivalence of both operators
to get the result for Demazure (in DemazureRelations.lean).-/
lemma eq_zero_of_mk'_zero {p : MvPolynomial (Fin (n + 1)) ℂ} : mk' p = zero ↔ p = 0 := by
  constructor
  intro h
  simp[mk', zero] at h
  exact h
  intro h
  simp[h, mk', zero]

lemma eq_of_eq_mk' {p q : MvPolynomial (Fin (n + 1)) ℂ} : mk' p = mk' q ↔ p = q := by
  constructor
  intro h
  simp[mk'] at h
  exact h
  intro h
  simp[h]


/- Some lemmas for interplay between mk and add -/
@[simp]
lemma simp_add {p q : PolyFraction n} : p + q = add p q := rfl

lemma mk_add {p q : PolyFraction' n} :  ((mk p) : PolyFraction n) + mk q = mk (p + q) := by
  have h1 : p+q = add' p q := by rfl
  have h2 : mk p + mk q = add (mk p) (mk q) := by rfl

  simp[add, add_mk, add', h1, h2]

lemma mk'_add : ∀ (p q : MvPolynomial (Fin (n + 1)) ℂ), mk' (p + q) = mk' p + mk' q := by
  simp[mk', mk_add, add, add_mk, add']

@[simp]
lemma simp_mul' {p q : PolyFraction' n} : p * q = ⟨p.numerator * q.numerator, p.denominator * q.denominator, mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero⟩ := rfl

@[simp]
lemma simp_mul {p q : PolyFraction n} : p * q = mul p q := rfl

lemma mk_mul {p q : PolyFraction' n} :  ((mk p) : PolyFraction n) * mk q = mk (p * q) := by
  have h1 : p*q = mul' p q := by rfl
  have h2 : mk p * mk q = mul (mk p) (mk q) := by rfl

  simp[mul, mul_mk, mul']

lemma mk'_mul {p q : MvPolynomial (Fin (n + 1)) ℂ} :  mk' p * mk' q = mk' (p * q) := by
  simp[mk', mul_mk, mul', mul]
