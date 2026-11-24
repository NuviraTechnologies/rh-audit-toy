/-
  Toy.lean: a small model of the patterns in the audit paper.
  It uses the four "decorative" patterns the paper describes, and still proves a
  TRUE theorem, because the real work is done by one honest lemma.
  Plain Lean 4 core, no Mathlib.
-/

/-- The quantity we care about: 1 + 3 + 5 + ... (the first n odd numbers). -/
def sumOdd : Nat → Nat
  | 0     => 0
  | n + 1 => sumOdd n + (2 * n + 1)

/-- The "genuine" answer we compare against, like the paper's shaTrue / genuine shaLen. -/
def trueLen (n : Nat) : Nat := n * n

/-! ### (a) An impressively named predicate that is just `True` (like `anyGeometry`) -/

/-- Sounds deep. Says nothing: it is true of every number by definition. -/
def DeepArithmeticGeometry (_n : Nat) : Prop := True

/-- A "generic" lemma: it works for ANY predicate G, so it never looks inside G.
    The predicate is carried along, not used ("carried, not spent"). -/
theorem carry_geometry (G : Nat → Prop) (hG : ∀ n, G n)
    (P : Nat → Prop) (hP : ∀ n, P n) : ∀ n, G n ∧ P n :=
  fun n => ⟨hG n, hP n⟩

/-! ### (b) A "computed" length that is simply set to the true value (like `adapt` / `sha_eq`) -/

structure LengthRecord (n : Nat) where
  len    : Nat              -- supposedly "computed" by some machinery
  len_eq : len = trueLen n  -- the proof obligation tying it to the genuine value

/-- The construction just assigns the genuine value, so the equation is `rfl`.
    "Set equal, then proved equal": no computation happens here. -/
def adaptRecord (n : Nat) : LengthRecord n where
  len    := trueLen n
  len_eq := rfl

/-! ### (c) A toy "example record" that discharges a nonemptiness requirement (like `exampleRecord`) -/

/-- The framework asks that a record exists for every n. The example supplies one. -/
theorem record_nonempty (n : Nat) : Nonempty (LengthRecord n) := ⟨adaptRecord n⟩

/-! ### (d) A grand name around weak content (like `OpenImageCondition`) -/

/-- Named after a famous conjecture. Its only field is the fact 1 + 1 = 2. -/
structure RiemannStyleCertificate : Prop where
  content : 1 + 1 = 2

theorem certificate_holds : RiemannStyleCertificate := ⟨rfl⟩

/-! ### The one honest lemma that does the real work -/

/-- Genuine induction: the sum of the first n odd numbers is n². -/
theorem sumOdd_eq (n : Nat) : sumOdd n = trueLen n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumOdd, trueLen] at *
    rw [ih, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega

/-! ### The "framework": takes every decorative input, and the honest one -/

theorem framework
    (G : Nat → Prop) (hG : ∀ n, G n)              -- (a) geometry hypothesis
    (_cert : RiemannStyleCertificate)              -- (d) grand certificate
    (hne : ∀ n, Nonempty (LengthRecord n))         -- (c) nonemptiness requirement
    (honest : ∀ n, sumOdd n = trueLen n) :         -- the real input
    ∀ n, sumOdd n = n * n := by
  intro n
  obtain ⟨r⟩ := hne n                     -- open the record...
  have h := (carry_geometry G hG _ honest n).2
  -- rewrite through the record's equation: true, but only because len := trueLen
  rw [← r.len_eq] at h
  rw [h, r.len_eq]
  rfl

/-- The grand-named main theorem, assembled from all the pieces. -/
theorem GrandOddSquareTheorem : ∀ n, sumOdd n = n * n :=
  framework DeepArithmeticGeometry (fun _ => trivial) certificate_holds
    record_nonempty sumOdd_eq

#print axioms GrandOddSquareTheorem

-- Sanity check by evaluation: 1+3+5+7+9 = 25.
#eval sumOdd 5
