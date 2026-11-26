import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m1_flat_np_to_st_np

open Turing

/-! ## Tape `nth` lemmas for `Turing.Tape` -/

private lemma nth_zero {Γ : Type} [Inhabited Γ] (T : Tape Γ) :
    T.nth 0 = T.head := rfl

private lemma nth_write {Γ : Type} [Inhabited Γ] (T : Tape Γ) (b : Γ) (z : ℤ) :
    (T.write b).nth z = if z = 0 then b else T.nth z := by
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

private lemma nth_move_left {Γ : Type} [Inhabited Γ] (T : Tape Γ) (z : ℤ) :
    (T.move Dir.left).nth z = T.nth (z - 1) := by
  rcases T with ⟨a, L, R⟩
  cases z with
  | ofNat n =>
    cases n with
    | zero =>
      show L.head = L.nth 0
      exact (ListBlank.nth_zero L).symm
    | succ k =>
      show (ListBlank.cons a R).nth k = _
      cases k with
      | zero =>
        rw [ListBlank.nth_zero, ListBlank.head_cons]; rfl
      | succ m =>
        rw [ListBlank.nth_succ, ListBlank.tail_cons]
        have h : (Int.ofNat (m + 1 + 1)) - 1 = Int.ofNat (m + 1) := by
          change ((m + 2 : ℕ) : ℤ) - 1 = ((m + 1 : ℕ) : ℤ); omega
        rw [h]; rfl
  | negSucc n =>
    show L.tail.nth n = L.nth (n + 1)
    exact (ListBlank.nth_succ L n).symm

private lemma nth_move_right {Γ : Type} [Inhabited Γ] (T : Tape Γ) (z : ℤ) :
    (T.move Dir.right).nth z = T.nth (z + 1) := by
  rcases T with ⟨a, L, R⟩
  cases z with
  | ofNat n =>
    cases n with
    | zero =>
      show R.head = R.nth 0
      exact (ListBlank.nth_zero R).symm
    | succ k =>
      show R.tail.nth k = R.nth (k + 1)
      exact (ListBlank.nth_succ R k).symm
  | negSucc n =>
    cases n with
    | zero =>
      show (ListBlank.cons a L).nth 0 = a
      rw [ListBlank.nth_zero, ListBlank.head_cons]
    | succ m =>
      show (ListBlank.cons a L).nth (m + 1) = L.nth m
      rw [ListBlank.nth_succ, ListBlank.tail_cons]

private lemma right₀_nth_eq_nth {Γ : Type} [Inhabited Γ] (T : Tape Γ) (i : ℕ) :
    T.right₀.nth i = T.nth (i : ℤ) := by
  rcases T with ⟨a, L, R⟩
  cases i with
  | zero =>
    show (ListBlank.cons a R).nth 0 = a
    rw [ListBlank.nth_zero, ListBlank.head_cons]
  | succ k =>
    show (ListBlank.cons a R).nth (k + 1) = R.nth k
    rw [ListBlank.nth_succ, ListBlank.tail_cons]

private lemma nth_mk₁ {Γ : Type} [Inhabited Γ] (l : List Γ) (z : ℤ) :
    (Tape.mk₁ l).nth z =
      match z with
      | Int.ofNat n => l.getD n default
      | Int.negSucc _ => default := by
  cases z with
  | ofNat n =>
    cases l with
    | nil =>
      cases n with
      | zero => rfl
      | succ k =>
        show (ListBlank.mk ([] : List Γ)).nth k = default
        rw [ListBlank.nth_mk]; rfl
    | cons a rest =>
      cases n with
      | zero => rfl
      | succ k =>
        show (ListBlank.mk rest).nth k = rest.getD k default
        rw [ListBlank.nth_mk]
        simp [List.getI, List.getD_eq_getElem?_getD]
  | negSucc n =>
    show (ListBlank.mk ([] : List Γ)).nth n = default
    rw [ListBlank.nth_mk]; rfl

/-! ## Step-reachability helper for `TM0` -/

private def Reaches {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (δ : TM0.Machine Γ Λ) (c₁ c₂ : TM0.Cfg Γ Λ) (k : ℕ) : Prop :=
  (flip bind (TM0.step δ))^[k] (some c₁) = some c₂

private lemma reaches_step {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (δ : TM0.Machine Γ Λ) {c₁ c₂ : TM0.Cfg Γ Λ}
    (h : TM0.step δ c₁ = some c₂) : Reaches δ c₁ c₂ 1 := by
  unfold Reaches; simp [flip, h]

private lemma reaches_trans {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (δ : TM0.Machine Γ Λ) {c₁ c₂ c₃ : TM0.Cfg Γ Λ} {k₁ k₂ : ℕ}
    (h1 : Reaches δ c₁ c₂ k₁) (h2 : Reaches δ c₂ c₃ k₂) :
    Reaches δ c₁ c₃ (k₁ + k₂) := by
  unfold Reaches at h1 h2 ⊢
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

private lemma step_write {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (δ : TM0.Machine Γ Λ) (q q' : Λ) (T : Tape Γ) (b : Γ)
    (h : δ q T.head = some (q', TM0.Stmt.write b)) :
    TM0.step δ ⟨q, T⟩ = some ⟨q', T.write b⟩ := by
  simp [TM0.step, h]

private lemma step_move {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (δ : TM0.Machine Γ Λ) (q q' : Λ) (T : Tape Γ) (d : Dir)
    (h : δ q T.head = some (q', TM0.Stmt.move d)) :
    TM0.step δ ⟨q, T⟩ = some ⟨q', T.move d⟩ := by
  simp [TM0.step, h]

/-! ## Simulation alphabet and states for pair verifiers -/

inductive SimSym (N : ℕ) : Type where
  | blank
  | inpSym (s : Bool ⊕ Bool)
  | outBit (b : Bool)
  | leftWall
  | cell (v : Fin N)
  | frontier
  deriving DecidableEq

instance (N : ℕ) : Inhabited (SimSym N) := ⟨SimSym.blank⟩

instance (N : ℕ) : Fintype (SimSym N) :=
  Fintype.ofEquiv (Unit ⊕ (Bool ⊕ Bool) ⊕ Bool ⊕ Unit ⊕ Fin N ⊕ Unit)
    { toFun := fun
        | .inl () => .blank
        | .inr (.inl s) => .inpSym s
        | .inr (.inr (.inl b)) => .outBit b
        | .inr (.inr (.inr (.inl ()))) => .leftWall
        | .inr (.inr (.inr (.inr (.inl v)))) => .cell v
        | .inr (.inr (.inr (.inr (.inr ())))) => .frontier
      invFun := fun
        | .blank => .inl ()
        | .inpSym s => .inr (.inl s)
        | .outBit b => .inr (.inr (.inl b))
        | .leftWall => .inr (.inr (.inr (.inl ())))
        | .cell v => .inr (.inr (.inr (.inr (.inl v))))
        | .frontier => .inr (.inr (.inr (.inr (.inr ()))))
      left_inv := by rintro (_ | _ | _ | _ | _ | _) <;> rfl
      right_inv := by rintro (_ | _ | _ | _ | _ | _) <;> rfl }

inductive SimState (S N : ℕ) : Type where
  | initLeft
  | initWriteWall
  | initBack0
  | init1Write (carry : Fin N)
  | init1Move (nextCarry : Fin N)
  | init2Move (d1 d2 : Fin N)
  | init2Write (d1 d2 : Fin N)
  | initEnd2Move (d2 : Fin N)
  | initEnd2Write (d2 : Fin N)
  | initEnd0Move
  | initEnd0Write
  | initEnd3Move
  | initEnd3Write
  | initEndFMove
  | initEndFWrite
  | initRewind
  | sim (q : Fin S)
  | frontMoveR (q' : Fin S) (d : TMMove)
  | frontWriteF (q' : Fin S) (d : TMMove)
  | frontMoveL (q' : Fin S) (d : TMMove)
  | doMove (q' : Fin S) (d : TMMove)
  | checkLeftWall (q' : Fin S)
  | outMoveR
  | outWriteBlank
  | outMoveL
  | halt
  deriving DecidableEq

instance (S N : ℕ) : Inhabited (SimState S N) := ⟨SimState.initLeft⟩

private def tmMoveEquiv : TMMove ≃ Fin 3 where
  toFun := fun | .Lmove => 0 | .Rmove => 1 | .Nmove => 2
  invFun := fun | ⟨0, _⟩ => .Lmove | ⟨1, _⟩ => .Rmove | ⟨2, _⟩ => .Nmove
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro ⟨i, hi⟩; interval_cases i <;> rfl

instance (S N : ℕ) : Fintype (SimState S N) :=
  Fintype.ofEquiv
    (Fin 14 ⊕ Fin N ⊕ Fin N ⊕ (Fin N × Fin N) ⊕ (Fin N × Fin N) ⊕ Fin N ⊕ Fin N ⊕
      Fin S ⊕ (Fin S × Fin 3) ⊕ (Fin S × Fin 3) ⊕ (Fin S × Fin 3) ⊕ (Fin S × Fin 3) ⊕ Fin S)
    { toFun := fun
        | .inl ⟨0, _⟩ => .initLeft
        | .inl ⟨1, _⟩ => .initWriteWall
        | .inl ⟨2, _⟩ => .initBack0
        | .inl ⟨3, _⟩ => .initEnd0Move
        | .inl ⟨4, _⟩ => .initEnd0Write
        | .inl ⟨5, _⟩ => .initEnd3Move
        | .inl ⟨6, _⟩ => .initEnd3Write
        | .inl ⟨7, _⟩ => .initEndFMove
        | .inl ⟨8, _⟩ => .initEndFWrite
        | .inl ⟨9, _⟩ => .initRewind
        | .inl ⟨10, _⟩ => .outMoveR
        | .inl ⟨11, _⟩ => .outWriteBlank
        | .inl ⟨12, _⟩ => .outMoveL
        | .inl ⟨13, _⟩ => .halt
        | .inl ⟨_ + 14, h⟩ => absurd h (by omega)
        | .inr (.inl c) => .init1Write c
        | .inr (.inr (.inl c)) => .init1Move c
        | .inr (.inr (.inr (.inl (a, b)))) => .init2Move a b
        | .inr (.inr (.inr (.inr (.inl (a, b))))) => .init2Write a b
        | .inr (.inr (.inr (.inr (.inr (.inl c))))) => .initEnd2Move c
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl c)))))) => .initEnd2Write c
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl q))))))) => .sim q
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (q, m))))))))) =>
            .frontMoveR q (tmMoveEquiv.symm m)
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (q, m)))))))))) =>
            .frontWriteF q (tmMoveEquiv.symm m)
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (q, m))))))))))) =>
            .frontMoveL q (tmMoveEquiv.symm m)
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (q, m)))))))))))) =>
            .doMove q (tmMoveEquiv.symm m)
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr q))))))))))) =>
            .checkLeftWall q
      invFun := fun
        | .initLeft => .inl 0
        | .initWriteWall => .inl 1
        | .initBack0 => .inl 2
        | .initEnd0Move => .inl 3
        | .initEnd0Write => .inl 4
        | .initEnd3Move => .inl 5
        | .initEnd3Write => .inl 6
        | .initEndFMove => .inl 7
        | .initEndFWrite => .inl 8
        | .initRewind => .inl 9
        | .outMoveR => .inl 10
        | .outWriteBlank => .inl 11
        | .outMoveL => .inl 12
        | .halt => .inl 13
        | .init1Write c => .inr (.inl c)
        | .init1Move c => .inr (.inr (.inl c))
        | .init2Move a b => .inr (.inr (.inr (.inl (a, b))))
        | .init2Write a b => .inr (.inr (.inr (.inr (.inl (a, b)))))
        | .initEnd2Move c => .inr (.inr (.inr (.inr (.inr (.inl c)))))
        | .initEnd2Write c => .inr (.inr (.inr (.inr (.inr (.inr (.inl c))))))
        | .sim q => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl q)))))))
        | .frontMoveR q d => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (q, tmMoveEquiv d)))))))))
        | .frontWriteF q d => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (q, tmMoveEquiv d))))))))))
        | .frontMoveL q d => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (q, tmMoveEquiv d)))))))))))
        | .doMove q d => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (q, tmMoveEquiv d))))))))))))
        | .checkLeftWall q => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr q)))))))))))
      left_inv := by
        rintro (⟨i, hi⟩ | c | c | ⟨a, b⟩ | ⟨a, b⟩ | c | c | q | ⟨q, m⟩ | ⟨q, m⟩ | ⟨q, m⟩ | ⟨q, m⟩ | q)
        · interval_cases i <;> rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · simp
        · simp
        · simp
        · simp
        · rfl
      right_inv := by
        intro st
        cases st <;> simp }

/-! ## Transition function for simulating a 1-tape `FlatTM` pair verifier -/

private def simDelta (M : FlatTM) (acc : ℕ) (hvalid : validFlatTM M) :
    TM0.Machine (SimSym (max M.sig 4)) (SimState M.states (max M.sig 4)) :=
  let N := max M.sig 4
  have h4 : 4 ≤ N := le_max_right _ _
  let c0 : Fin N := ⟨0, by omega⟩
  let c1 : Fin N := ⟨1, by omega⟩
  let c2 : Fin N := ⟨2, by omega⟩
  let c3 : Fin N := ⟨3, by omega⟩
  let qStart : Fin M.states := ⟨M.start, hvalid.1⟩
  fun st sym =>
    match st with
    | .initLeft => some (.initWriteWall, .move .left)
    | .initWriteWall => some (.initBack0, .write .leftWall)
    | .initBack0 => some (.init1Write c3, .move .right)
    | .init1Write carry =>
      match sym with
      | .inpSym (.inl b) => some (.init1Move (if b then c2 else c1), .write (.cell carry))
      | .inpSym (.inr b) => some (.init2Move c0 (if b then c2 else c1), .write (.cell carry))
      | _ => some (.initEnd2Move c0, .write (.cell carry))
    | .init1Move nextCarry => some (.init1Write nextCarry, .move .right)
    | .init2Move d1 d2 => some (.init2Write d1 d2, .move .right)
    | .init2Write d1 d2 =>
      match sym with
      | .inpSym (.inr b) => some (.init2Move d2 (if b then c2 else c1), .write (.cell d1))
      | _ => some (.initEnd2Move d2, .write (.cell d1))
    | .initEnd2Move d2 => some (.initEnd2Write d2, .move .right)
    | .initEnd2Write d2 => some (.initEnd0Move, .write (.cell d2))
    | .initEnd0Move => some (.initEnd0Write, .move .right)
    | .initEnd0Write => some (.initEnd3Move, .write (.cell c0))
    | .initEnd3Move => some (.initEnd3Write, .move .right)
    | .initEnd3Write => some (.initEndFMove, .write (.cell c3))
    | .initEndFMove => some (.initEndFWrite, .move .right)
    | .initEndFWrite => some (.initRewind, .write .frontier)
    | .initRewind =>
      match sym with
      | .leftWall => some (.sim qStart, .move .right)
      | _ => some (.initRewind, .move .left)
    | .sim q =>
      if M.halt.getD q.val false then
        some (.outMoveR, .write (.outBit (q.val == acc)))
      else
        let cur : Option ℕ :=
          match sym with
          | .cell v => some v.val
          | _ => none
        match M.trans.find? (fun e => e.src_state == q.val && decide (e.src_tape_vals = [cur])) with
        | none => some (.outMoveR, .write (.outBit (q.val == acc)))
        | some e =>
          let q' : Fin M.states := if h : e.dst_state < M.states then ⟨e.dst_state, h⟩ else q
          let w : Option ℕ := e.dst_write_vals.headD none
          let d : TMMove := e.move_dirs.headD .Nmove
          match w with
          | none => some (.doMove q' d, .write sym)
          | some v =>
            let vf : Fin N := if h : v < N then ⟨v, h⟩ else c0
            match sym with
            | .cell _ => some (.doMove q' d, .write (.cell vf))
            | .frontier => some (.frontMoveR q' d, .write (.cell vf))
            | _ => some (.doMove q' d, .write sym)
    | .frontMoveR q' d => some (.frontWriteF q' d, .move .right)
    | .frontWriteF q' d => some (.frontMoveL q' d, .write .frontier)
    | .frontMoveL q' d => some (.doMove q' d, .move .left)
    | .doMove q' d =>
      match d with
      | .Nmove => some (.sim q', .write sym)
      | .Rmove => some (.sim q', .move .right)
      | .Lmove => some (.checkLeftWall q', .move .left)
    | .checkLeftWall q' =>
      match sym with
      | .leftWall => some (.sim q', .move .right)
      | _ => some (.sim q', .write sym)
    | .outMoveR => some (.outWriteBlank, .move .right)
    | .outWriteBlank => some (.outMoveL, .write .blank)
    | .outMoveL => some (.halt, .move .left)
    | .halt => none

private def simMachine (M : FlatTM) (acc : ℕ) (hvalid : validFlatTM M) :
    PvsNP.SingleTape.Machine (Bool ⊕ Bool) Bool where
  Γ := SimSym (max M.sig 4)
  Λ := SimState M.states (max M.sig 4)
  inp := SimSym.inpSym
  out := SimSym.outBit
  inp_injective := fun _ _ h => SimSym.inpSym.inj h
  out_injective := fun _ _ h => SimSym.outBit.inj h
  inp_ne_blank := fun _ h => by cases h
  out_ne_blank := fun _ h => by cases h
  δ := simDelta M acc hvalid

/-! ## Tape invariant -/

private def TapeMatch (N : ℕ) (T : Tape (SimSym N)) (head : ℕ) (right : List ℕ) : Prop :=
  (∀ k : ℤ, k < -1 → T.nth (k - head) = SimSym.blank) ∧
  T.nth (-1 - head) = SimSym.leftWall ∧
  (∀ (i : ℕ) (hi : i < right.length),
    ∃ hlt : right[i] < N, T.nth ((i : ℤ) - head) = SimSym.cell ⟨right[i], hlt⟩) ∧
  T.nth ((right.length : ℤ) - head) = SimSym.frontier ∧
  (∀ i : ℕ, right.length < i → T.nth ((i : ℤ) - head) = SimSym.blank)

private lemma tapeMatch_head_lt {N : ℕ} {T : Tape (SimSym N)} {head : ℕ} {right : List ℕ}
    (h : TapeMatch N T head right) (hlt : head < right.length) :
    ∃ hv : right[head] < N, T.head = SimSym.cell ⟨right[head], hv⟩ := by
  obtain ⟨hv, heq⟩ := h.2.2.1 head hlt
  refine ⟨hv, ?_⟩
  have hz : ((head : ℤ) - head) = 0 := by omega
  rw [hz, nth_zero] at heq
  exact heq

private lemma tapeMatch_head_eq {N : ℕ} {T : Tape (SimSym N)} {head : ℕ} {right : List ℕ}
    (h : TapeMatch N T head right) (heq : head = right.length) :
    T.head = SimSym.frontier := by
  have h1 := h.2.2.2.1
  have hz : ((right.length : ℤ) - head) = 0 := by omega
  rw [hz, nth_zero] at h1
  exact h1

private lemma tapeMatch_head_gt {N : ℕ} {T : Tape (SimSym N)} {head : ℕ} {right : List ℕ}
    (h : TapeMatch N T head right) (hgt : right.length < head) :
    T.head = SimSym.blank := by
  have h1 := h.2.2.2.2 head hgt
  have hz : ((head : ℤ) - head) = 0 := by omega
  rw [hz, nth_zero] at h1
  exact h1

private lemma tapeMatch_move_right {N : ℕ} {T : Tape (SimSym N)} {head : ℕ} {right : List ℕ}
    (h : TapeMatch N T head right) :
    TapeMatch N (T.move Dir.right) (head + 1) right := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun k hk => ?_, ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · rw [nth_move_right, show k - (head + 1 : ℕ) + 1 = k - head by omega]; exact h1 k hk
  · rw [nth_move_right, show (-1 : ℤ) - (head + 1 : ℕ) + 1 = -1 - head by omega]; exact h2
  · obtain ⟨hv, heq⟩ := h3 i hi
    refine ⟨hv, ?_⟩
    rw [nth_move_right, show (i : ℤ) - (head + 1 : ℕ) + 1 = (i : ℤ) - head by omega]; exact heq
  · rw [nth_move_right, show (right.length : ℤ) - (head + 1 : ℕ) + 1 = (right.length : ℤ) - head by omega]
    exact h4
  · rw [nth_move_right, show (i : ℤ) - (head + 1 : ℕ) + 1 = (i : ℤ) - head by omega]; exact h5 i hi

private lemma tapeMatch_move_left {N : ℕ} {T : Tape (SimSym N)} {head : ℕ} {right : List ℕ}
    (h : TapeMatch N T (head + 1) right) :
    TapeMatch N (T.move Dir.left) head right := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun k hk => ?_, ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · rw [nth_move_left, show k - head - 1 = k - (head + 1 : ℕ) by omega]; exact h1 k hk
  · rw [nth_move_left, show (-1 : ℤ) - head - 1 = -1 - (head + 1 : ℕ) by omega]; exact h2
  · obtain ⟨hv, heq⟩ := h3 i hi
    refine ⟨hv, ?_⟩
    rw [nth_move_left, show (i : ℤ) - head - 1 = (i : ℤ) - (head + 1 : ℕ) by omega]; exact heq
  · rw [nth_move_left, show (right.length : ℤ) - head - 1 = (right.length : ℤ) - (head + 1 : ℕ) by omega]
    exact h4
  · rw [nth_move_left, show (i : ℤ) - head - 1 = (i : ℤ) - (head + 1 : ℕ) by omega]; exact h5 i hi

private lemma tapeMatch_write_in_range {N : ℕ} {T : Tape (SimSym N)} {head : ℕ} {right : List ℕ}
    (h : TapeMatch N T head right) (hlt : head < right.length) (v : Fin N) :
    TapeMatch N (T.write (.cell v)) head (right.take head ++ v.val :: right.drop (head + 1)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hlen : (right.take head ++ v.val :: right.drop (head + 1)).length = right.length := by
    simp [List.length_take, List.length_drop]; omega
  refine ⟨fun k hk => ?_, ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · rw [nth_write, if_neg (by omega)]; exact h1 k hk
  · rw [nth_write, if_neg (by omega)]; exact h2
  · by_cases hieq : i = head
    · subst hieq
      have hget : (right.take i ++ v.val :: right.drop (i + 1))[i] = v.val := by
        rw [List.getElem_append_right (by simp)]
        simp [List.length_take, Nat.le_of_lt hlt]
      refine ⟨by rw [hget]; exact v.isLt, ?_⟩
      rw [nth_write, if_pos (by omega)]
      congr 1; exact Fin.ext hget.symm
    · have hi' : i < right.length := by omega
      have hget : (right.take head ++ v.val :: right.drop (head + 1))[i] = right[i] := by
        by_cases hlti : i < head
        · rw [List.getElem_append_left (by simp; omega), List.getElem_take]
        · have hgt : head < i := by omega
          rw [List.getElem_append_right (by simp; omega)]
          have hltake : (right.take head).length = head := by simp; omega
          have hsub : i - (right.take head).length = (i - head - 1) + 1 := by omega
          simp only [hsub, List.getElem_cons_succ, List.getElem_drop]
          congr 1; omega
      obtain ⟨hv, heq⟩ := h3 i hi'
      refine ⟨by rw [hget]; exact hv, ?_⟩
      rw [nth_write, if_neg (by omega), heq]
      congr 1; exact Fin.ext hget.symm
  · rw [hlen, nth_write, if_neg (by omega)]; exact h4
  · rw [hlen] at hi; rw [nth_write, if_neg (by omega)]; exact h5 i hi

private lemma tapeMatch_write_frontier {N : ℕ} {T : Tape (SimSym N)} {right : List ℕ}
    (h : TapeMatch N T right.length right) (v : Fin N) :
    TapeMatch N ((((T.write (.cell v)).move .right).write .frontier).move .left)
      right.length (right ++ [v.val]) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hstep : ∀ z : ℤ,
      ((((T.write (.cell v)).move .right).write .frontier).move .left).nth z =
        if z = 1 then .frontier else if z = 0 then .cell v else T.nth z := by
    intro z
    rw [nth_move_left, nth_write]
    by_cases hz1 : z = 1
    · subst hz1; simp
    · rw [if_neg (by omega), if_neg hz1, nth_move_right, show z - 1 + 1 = z by omega, nth_write]
  have hlen : (right ++ [v.val]).length = right.length + 1 := by simp
  refine ⟨fun k hk => ?_, ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · rw [hstep, if_neg (by omega), if_neg (by omega)]; exact h1 k hk
  · rw [hstep, if_neg (by omega), if_neg (by omega)]; exact h2
  · rw [hlen] at hi
    by_cases hilt : i < right.length
    · have hget : (right ++ [v.val])[i] = right[i] := List.getElem_append_left hilt
      obtain ⟨hv, heq⟩ := h3 i hilt
      refine ⟨by rw [hget]; exact hv, ?_⟩
      rw [hstep, if_neg (by omega), if_neg (by omega), heq]
      congr 1; exact Fin.ext hget.symm
    · have hieq : i = right.length := by omega
      subst hieq
      have hget : (right ++ [v.val])[right.length] = v.val := by simp
      refine ⟨by rw [hget]; exact v.isLt, ?_⟩
      rw [hstep, if_neg (by omega), if_pos (by omega)]
      congr 1; exact Fin.ext hget.symm
  · rw [hlen, hstep, if_pos (by omega)]
  · rw [hlen] at hi
    rw [hstep, if_neg (by omega), if_neg (by omega)]; exact h5 i (by omega)

/-! ## Phase 1: Init (`encodePair (x, c)` → `TapeMatch` of `pairTape x c` at head 0) -/

private lemma init_rewind_loop (M : FlatTM) (acc : ℕ) (hvalid : validFlatTM M)
    (right : List ℕ) :
    ∀ (head : ℕ) (T : Tape (SimSym (max M.sig 4))),
      TapeMatch (max M.sig 4) T head right →
      ∃ T', Reaches (simDelta M acc hvalid) ⟨.initRewind, T⟩ ⟨.sim ⟨M.start, hvalid.1⟩, T'⟩ (head + 2) ∧
        TapeMatch (max M.sig 4) T' 0 right := by
  intro head
  induction head with
  | zero =>
    intro T hT
    have hnotW : T.head ≠ SimSym.leftWall := by
      cases right with
      | nil => rw [tapeMatch_head_eq hT rfl]; intro h; cases h
      | cons r rs =>
        obtain ⟨_, heq⟩ := tapeMatch_head_lt hT (by simp)
        rw [heq]; intro h; cases h
    have hstep1 : TM0.step (simDelta M acc hvalid) ⟨.initRewind, T⟩ = some ⟨.initRewind, T.move .left⟩ := by
      apply step_move; unfold simDelta
      cases hhd : T.head with
      | leftWall => exact absurd hhd hnotW
      | _ => rfl
    have hwall : (T.move .left).head = SimSym.leftWall := by
      rw [← nth_zero, nth_move_left]; simpa using hT.2.1
    have hstep2 : TM0.step (simDelta M acc hvalid) ⟨.initRewind, T.move .left⟩ =
        some ⟨.sim ⟨M.start, hvalid.1⟩, (T.move .left).move .right⟩ := by
      apply step_move; simp [simDelta, hwall]
    have h12 : Reaches (simDelta M acc hvalid) ⟨.initRewind, T⟩
        ⟨.sim ⟨M.start, hvalid.1⟩, (T.move .left).move .right⟩ (0 + 2) := by
      show Reaches _ _ _ (1 + 1)
      exact reaches_trans _ (reaches_step _ hstep1) (reaches_step _ hstep2)
    refine ⟨(T.move .left).move .right, h12, ?_⟩
    have hsame : ∀ z : ℤ, ((T.move .left).move .right).nth z = T.nth z := by
      intro z; rw [nth_move_right, nth_move_left]; congr 1; omega
    obtain ⟨h1, h2, h3, h4, h5⟩ := hT
    exact ⟨fun k hk => by rw [hsame]; exact h1 k hk, by rw [hsame]; exact h2,
      fun i hi => by obtain ⟨hv, heq⟩ := h3 i hi; exact ⟨hv, by rw [hsame]; exact heq⟩,
      by rw [hsame]; exact h4, fun i hi => by rw [hsame]; exact h5 i hi⟩
  | succ k ih =>
    intro T hT
    have hnotW : T.head ≠ SimSym.leftWall := by
      rcases lt_trichotomy (k + 1) right.length with hlt | heq | hgt
      · obtain ⟨_, hhd⟩ := tapeMatch_head_lt hT hlt; rw [hhd]; intro h; cases h
      · rw [tapeMatch_head_eq hT heq]; intro h; cases h
      · rw [tapeMatch_head_gt hT hgt]; intro h; cases h
    have hstep1 : TM0.step (simDelta M acc hvalid) ⟨.initRewind, T⟩ = some ⟨.initRewind, T.move .left⟩ := by
      apply step_move; unfold simDelta
      cases hhd : T.head with
      | leftWall => exact absurd hhd hnotW
      | _ => rfl
    obtain ⟨T', hreach, hT'⟩ := ih (T.move .left) (tapeMatch_move_left hT)
    refine ⟨T', ?_, hT'⟩
    have htot := reaches_trans _ (reaches_step _ hstep1) hreach
    have hcnt : 1 + (k + 2) = k + 1 + 2 := by omega
    rwa [hcnt] at htot

private def InitShiftInv (N : ℕ) (T : Tape (SimSym N)) (pos : ℕ)
    (written : List ℕ) (rem : List (Bool ⊕ Bool)) : Prop :=
  written.length = pos ∧
  (∀ k : ℤ, k < -1 → T.nth (k - pos) = SimSym.blank) ∧
  T.nth (-1 - pos) = SimSym.leftWall ∧
  (∀ (i : ℕ) (hi : i < written.length),
    ∃ hv : written[i] < N, T.nth ((i : ℤ) - pos) = SimSym.cell ⟨written[i], hv⟩) ∧
  (∀ (j : ℕ) (hj : j < rem.length), T.nth (j : ℤ) = SimSym.inpSym rem[j]) ∧
  (∀ j : ℕ, rem.length ≤ j → T.nth (j : ℤ) = SimSym.blank)

private def InitDoneInv (N : ℕ) (T : Tape (SimSym N)) (pos : ℕ) (written : List ℕ) : Prop :=
  written.length = pos + 1 ∧
  (∀ k : ℤ, k < -1 → T.nth (k - pos) = SimSym.blank) ∧
  T.nth (-1 - pos) = SimSym.leftWall ∧
  (∀ (i : ℕ) (hi : i < written.length),
    ∃ hv : written[i] < N, T.nth ((i : ℤ) - pos) = SimSym.cell ⟨written[i], hv⟩) ∧
  (∀ j : ℕ, 1 ≤ j → T.nth (j : ℤ) = SimSym.blank)

private lemma initShiftInv_step {N : ℕ} {T : Tape (SimSym N)} {written : List ℕ}
    {s : Bool ⊕ Bool} {rem : List (Bool ⊕ Bool)} (w : Fin N)
    (hInv : InitShiftInv N T written.length written (s :: rem)) :
    InitShiftInv N ((T.write (.cell w)).move .right)
      (written ++ [w.val]).length (written ++ [w.val]) rem := by
  obtain ⟨_, h1, h2, h3, h4, h5⟩ := hInv
  have hlen : (written ++ [w.val]).length = written.length + 1 := by simp
  refine ⟨rfl, fun k hk => ?_, ?_, fun i hi => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [hlen, nth_move_right, nth_write, if_neg (by omega),
      show k - (written.length + 1 : ℕ) + 1 = k - written.length by omega]
    exact h1 k hk
  · rw [hlen, nth_move_right, nth_write, if_neg (by omega),
      show (-1 : ℤ) - (written.length + 1 : ℕ) + 1 = -1 - written.length by omega]
    exact h2
  · rw [hlen] at hi ⊢
    rw [nth_move_right, show (i : ℤ) - (written.length + 1 : ℕ) + 1 = (i : ℤ) - written.length by omega]
    by_cases hilt : i < written.length
    · have hget : (written ++ [w.val])[i] = written[i] := List.getElem_append_left hilt
      obtain ⟨hv, heq⟩ := h3 i hilt
      refine ⟨by rw [hget]; exact hv, ?_⟩
      rw [nth_write, if_neg (by omega), heq]
      congr 1; exact Fin.ext hget.symm
    · have hieq : i = written.length := by omega
      subst hieq
      have hget : (written ++ [w.val])[written.length] = w.val := by simp
      refine ⟨by rw [hget]; exact w.isLt, ?_⟩
      rw [nth_write, if_pos (by omega)]
      congr 1; exact Fin.ext hget.symm
  · rw [nth_move_right, nth_write, if_neg (by omega)]
    have := h4 (j + 1) (by simp; omega)
    simpa using this
  · rw [nth_move_right, nth_write, if_neg (by omega)]
    have := h5 (j + 1) (by simp; omega)
    simpa using this

private lemma initDoneInv_of_write_blank {N : ℕ} {T : Tape (SimSym N)} {written : List ℕ}
    (w : Fin N) (hInv : InitShiftInv N T written.length written []) :
    InitDoneInv N (T.write (.cell w)) written.length (written ++ [w.val]) := by
  obtain ⟨_, h1, h2, h3, _, h5⟩ := hInv
  refine ⟨by simp, fun k hk => ?_, ?_, fun i hi => ?_, fun j hj => ?_⟩
  · rw [nth_write, if_neg (by omega)]; exact h1 k hk
  · rw [nth_write, if_neg (by omega)]; exact h2
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases hilt : i < written.length
    · have hget : (written ++ [w.val])[i] = written[i] := List.getElem_append_left hilt
      obtain ⟨hv, heq⟩ := h3 i hilt
      refine ⟨by rw [hget]; exact hv, ?_⟩
      rw [nth_write, if_neg (by omega), heq]
      congr 1; exact Fin.ext hget.symm
    · have hieq : i = written.length := by omega
      subst hieq
      have hget : (written ++ [w.val])[written.length] = w.val := by simp
      refine ⟨by rw [hget]; exact w.isLt, ?_⟩
      rw [nth_write, if_pos (by omega)]
      congr 1; exact Fin.ext hget.symm
  · rw [nth_write, if_neg (by omega)]; exact h5 j (by simp)

private lemma init2_loop (M : FlatTM) (acc : ℕ) (hvalid : validFlatTM M) :
    ∀ (rem : List Bool) (written : List ℕ) (d1 d2 : Fin (max M.sig 4))
      (T : Tape (SimSym (max M.sig 4))),
      InitShiftInv (max M.sig 4) T written.length written (rem.map Sum.inr) →
      ∃ (dLast : Fin (max M.sig 4)) (T' : Tape (SimSym (max M.sig 4))),
        Reaches (simDelta M acc hvalid) ⟨.init2Write d1 d2, T⟩
          ⟨.initEnd2Move dLast, T'⟩ (2 * rem.length + 1) ∧
        InitDoneInv (max M.sig 4) T' (written.length + rem.length)
          ((written ++ d1.val :: d2.val :: CookLevin.symbolsOf rem).dropLast) ∧
        (written ++ d1.val :: d2.val :: CookLevin.symbolsOf rem) =
          (written ++ d1.val :: d2.val :: CookLevin.symbolsOf rem).dropLast ++ [dLast.val] := by
  intro rem
  induction rem with
  | nil =>
    intro written d1 d2 T hInv
    have hhd : T.head = SimSym.blank := by
      rw [← nth_zero]; exact hInv.2.2.2.2.2 0 (by simp)
    have hs : TM0.step (simDelta M acc hvalid) ⟨.init2Write d1 d2, T⟩ =
        some ⟨.initEnd2Move d2, T.write (.cell d1)⟩ := by
      apply step_write; simp [simDelta, hhd]
    refine ⟨d2, T.write (.cell d1), reaches_step _ hs, ?_, ?_⟩
    · have hdl : (written ++ d1.val :: d2.val :: CookLevin.symbolsOf []).dropLast = written ++ [d1.val] := by
        simp [CookLevin.symbolsOf, List.dropLast_append_of_ne_nil]
      rw [hdl]; simpa using initDoneInv_of_write_blank d1 hInv
    · simp [CookLevin.symbolsOf, List.dropLast_append_of_ne_nil, List.append_assoc]
  | cons b bs ih =>
    intro written d1 d2 T hInv
    have hhd : T.head = SimSym.inpSym (.inr b) := by
      rw [← nth_zero]
      have := hInv.2.2.2.2.1 0 (by simp)
      simpa using this
    let d3 : Fin (max M.sig 4) := if b then ⟨2, by omega⟩ else ⟨1, by omega⟩
    have hs1 : TM0.step (simDelta M acc hvalid) ⟨.init2Write d1 d2, T⟩ =
        some ⟨.init2Move d2 d3, T.write (.cell d1)⟩ := by
      apply step_write; simp [simDelta, hhd, d3]
    have hs2 : TM0.step (simDelta M acc hvalid) ⟨.init2Move d2 d3, T.write (.cell d1)⟩ =
        some ⟨.init2Write d2 d3, (T.write (.cell d1)).move .right⟩ :=
      step_move _ _ _ _ _ rfl
    have hInv' := initShiftInv_step d1 hInv
    obtain ⟨dLast, T', hr, hDone, hEq⟩ := ih (written ++ [d1.val]) d2 d3 _ hInv'
    have hd3Val : d3.val = (if b then 2 else 1) := by cases b <;> rfl
    have hlist : (written ++ [d1.val]) ++ d2.val :: d3.val :: CookLevin.symbolsOf bs =
        written ++ d1.val :: d2.val :: CookLevin.symbolsOf (b :: bs) := by
      simp [CookLevin.symbolsOf, hd3Val, List.append_assoc]
    have hpos : (written ++ [d1.val]).length + bs.length = written.length + (b :: bs).length := by
      simp; omega
    refine ⟨dLast, T', ?_, ?_, ?_⟩
    · have htot := reaches_trans _ (reaches_trans _ (reaches_step _ hs1) (reaches_step _ hs2)) hr
      have hcnt : 1 + 1 + (2 * bs.length + 1) = 2 * (b :: bs).length + 1 := by simp; omega
      rwa [hcnt] at htot
    · rwa [hlist, hpos] at hDone
    · rwa [hlist] at hEq

private lemma init1_loop (M : FlatTM) (acc : ℕ) (hvalid : validFlatTM M) (c : List Bool) :
    ∀ (rem : List Bool) (written : List ℕ) (carry : Fin (max M.sig 4))
      (T : Tape (SimSym (max M.sig 4))),
      InitShiftInv (max M.sig 4) T written.length written (rem.map Sum.inl ++ c.map Sum.inr) →
      ∃ (dLast : Fin (max M.sig 4)) (T' : Tape (SimSym (max M.sig 4))),
        Reaches (simDelta M acc hvalid) ⟨.init1Write carry, T⟩
          ⟨.initEnd2Move dLast, T'⟩ (2 * (rem.length + c.length) + 1) ∧
        InitDoneInv (max M.sig 4) T' (written.length + rem.length + c.length)
          ((written ++ carry.val :: CookLevin.symbolsOf rem ++ [0] ++ CookLevin.symbolsOf c).dropLast) ∧
        (written ++ carry.val :: CookLevin.symbolsOf rem ++ [0] ++ CookLevin.symbolsOf c) =
          (written ++ carry.val :: CookLevin.symbolsOf rem ++ [0] ++ CookLevin.symbolsOf c).dropLast ++ [dLast.val] := by
  intro rem
  induction rem with
  | nil =>
    intro written carry T hInv
    cases c with
    | nil =>
      have hhd : T.head = SimSym.blank := by
        rw [← nth_zero]; exact hInv.2.2.2.2.2 0 (by simp)
      have hs : TM0.step (simDelta M acc hvalid) ⟨.init1Write carry, T⟩ =
          some ⟨.initEnd2Move ⟨0, by omega⟩, T.write (.cell carry)⟩ := by
        apply step_write; simp [simDelta, hhd]
      refine ⟨⟨0, by omega⟩, T.write (.cell carry), reaches_step _ hs, ?_, ?_⟩
      · have hdl : (written ++ carry.val :: CookLevin.symbolsOf [] ++ [0] ++ CookLevin.symbolsOf []).dropLast =
            written ++ [carry.val] := by
          simp [CookLevin.symbolsOf, List.dropLast_append_of_ne_nil]
        rw [hdl]; simpa using initDoneInv_of_write_blank carry (by simpa using hInv)
      · simp [CookLevin.symbolsOf, List.dropLast_append_of_ne_nil, List.append_assoc]
    | cons b0 bs =>
      have hhd : T.head = SimSym.inpSym (.inr b0) := by
        rw [← nth_zero]
        have := hInv.2.2.2.2.1 0 (by simp)
        simpa using this
      let c0 : Fin (max M.sig 4) := ⟨0, by omega⟩
      let cb : Fin (max M.sig 4) := if b0 then ⟨2, by omega⟩ else ⟨1, by omega⟩
      have hs1 : TM0.step (simDelta M acc hvalid) ⟨.init1Write carry, T⟩ =
          some ⟨.init2Move c0 cb, T.write (.cell carry)⟩ := by
        apply step_write; simp [simDelta, hhd, c0, cb]
      have hs2 : TM0.step (simDelta M acc hvalid) ⟨.init2Move c0 cb, T.write (.cell carry)⟩ =
          some ⟨.init2Write c0 cb, (T.write (.cell carry)).move .right⟩ :=
        step_move _ _ _ _ _ rfl
      have hInv' := initShiftInv_step carry (by simpa using hInv)
      obtain ⟨dLast, T', hr, hDone, hEq⟩ := init2_loop M acc hvalid bs (written ++ [carry.val]) c0 cb _ hInv'
      have hcbVal : cb.val = (if b0 then 2 else 1) := by cases b0 <;> rfl
      have hlist : (written ++ [carry.val]) ++ c0.val :: cb.val :: CookLevin.symbolsOf bs =
          written ++ carry.val :: CookLevin.symbolsOf [] ++ [0] ++ CookLevin.symbolsOf (b0 :: bs) := by
        simp [CookLevin.symbolsOf, c0, hcbVal, List.append_assoc]
      have hpos : (written ++ [carry.val]).length + bs.length =
          written.length + ([] : List Bool).length + (b0 :: bs).length := by simp; omega
      refine ⟨dLast, T', ?_, ?_, ?_⟩
      · have htot := reaches_trans _ (reaches_trans _ (reaches_step _ hs1) (reaches_step _ hs2)) hr
        have hcnt : 1 + 1 + (2 * bs.length + 1) = 2 * (([] : List Bool).length + (b0 :: bs).length) + 1 := by
          simp; omega
        rwa [hcnt] at htot
      · rwa [hlist, hpos] at hDone
      · rwa [hlist] at hEq
  | cons a as ih =>
    intro written carry T hInv
    have hhd : T.head = SimSym.inpSym (.inl a) := by
      rw [← nth_zero]
      have := hInv.2.2.2.2.1 0 (by simp)
      simpa using this
    let nextC : Fin (max M.sig 4) := if a then ⟨2, by omega⟩ else ⟨1, by omega⟩
    have hs1 : TM0.step (simDelta M acc hvalid) ⟨.init1Write carry, T⟩ =
        some ⟨.init1Move nextC, T.write (.cell carry)⟩ := by
      apply step_write; simp [simDelta, hhd, nextC]
    have hs2 : TM0.step (simDelta M acc hvalid) ⟨.init1Move nextC, T.write (.cell carry)⟩ =
        some ⟨.init1Write nextC, (T.write (.cell carry)).move .right⟩ :=
      step_move _ _ _ _ _ rfl
    have hInv' := initShiftInv_step carry (by simpa using hInv)
    obtain ⟨dLast, T', hr, hDone, hEq⟩ := ih (written ++ [carry.val]) nextC _ hInv'
    have hnextVal : nextC.val = (if a then 2 else 1) := by cases a <;> rfl
    have hlist : (written ++ [carry.val]) ++ nextC.val :: CookLevin.symbolsOf as ++ [0] ++ CookLevin.symbolsOf c =
        written ++ carry.val :: CookLevin.symbolsOf (a :: as) ++ [0] ++ CookLevin.symbolsOf c := by
      simp [CookLevin.symbolsOf, hnextVal, List.append_assoc]
    have hpos : (written ++ [carry.val]).length + as.length + c.length =
        written.length + (a :: as).length + c.length := by simp; omega
    refine ⟨dLast, T', ?_, ?_, ?_⟩
    · have htot := reaches_trans _ (reaches_trans _ (reaches_step _ hs1) (reaches_step _ hs2)) hr
      have hcnt : 1 + 1 + (2 * (as.length + c.length) + 1) =
          2 * ((a :: as).length + c.length) + 1 := by simp; omega
      rwa [hcnt] at htot
    · rwa [hlist, hpos] at hDone
    · rwa [hlist] at hEq

private lemma phase1_init (M : FlatTM) (acc : ℕ) (hvalid : validFlatTM M) (x c : List Bool) :
    ∃ T', Reaches (simDelta M acc hvalid)
        ⟨SimState.initLeft, Tape.mk₁ ((PvsNP.encodePair (x, c)).map SimSym.inpSym)⟩
        ⟨SimState.sim ⟨M.start, hvalid.1⟩, T'⟩ (3 * (x.length + c.length) + 18) ∧
      TapeMatch (max M.sig 4) T' 0 (CookLevin.pairTape x c) := by
  let N := max M.sig 4
  have henc : PvsNP.encodePair (x, c) = x.map Sum.inl ++ c.map Sum.inr := rfl
  let T0 : Tape (SimSym N) := Tape.mk₁ ((PvsNP.encodePair (x, c)).map SimSym.inpSym)
  show ∃ T', Reaches (simDelta M acc hvalid) ⟨SimState.initLeft, T0⟩ _ _ ∧ _
  have hs1 : TM0.step (simDelta M acc hvalid) ⟨.initLeft, T0⟩ = some ⟨.initWriteWall, T0.move .left⟩ :=
    step_move _ _ _ _ _ rfl
  have hs2 : TM0.step (simDelta M acc hvalid) ⟨.initWriteWall, T0.move .left⟩ =
      some ⟨.initBack0, (T0.move .left).write .leftWall⟩ :=
    step_write _ _ _ _ _ rfl
  let T1 := ((T0.move .left).write .leftWall).move .right
  have hs3 : TM0.step (simDelta M acc hvalid) ⟨.initBack0, (T0.move .left).write .leftWall⟩ =
      some ⟨.init1Write ⟨3, by omega⟩, T1⟩ :=
    step_move _ _ _ _ _ rfl
  have hT1_nth : ∀ z : ℤ, T1.nth z = if z = -1 then .leftWall else T0.nth z := by
    intro z
    simp only [T1, nth_move_right, nth_write]
    by_cases hz : z = -1
    · subst hz; simp
    · rw [if_neg (by omega), if_neg hz, nth_move_left, show z + 1 - 1 = z by omega]
  have hInv0 : InitShiftInv N T1 0 [] (x.map Sum.inl ++ c.map Sum.inr) := by
    refine ⟨rfl, fun k hk => ?_, ?_, fun i hi => by simp at hi, fun j hj => ?_, fun j hj => ?_⟩
    · rw [hT1_nth, if_neg (by omega), nth_mk₁]
      cases hk' : k - (0 : ℕ) with
      | ofNat n =>
        have h0 : (0 : ℤ) ≤ Int.ofNat n := Int.ofNat_nonneg n
        omega
      | negSucc _ => rfl
    · rw [hT1_nth, if_pos (by omega)]
    · rw [hT1_nth, if_neg (by omega)]
      simp only [T0, henc, nth_mk₁, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
    · rw [hT1_nth, if_neg (by omega)]
      simp only [T0, henc, nth_mk₁]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp at hj ⊢; omega)]
      rfl
  obtain ⟨dLast, T2, hrShift, hDone, hPreEq⟩ := init1_loop M acc hvalid c x [] ⟨3, by omega⟩ T1 hInv0
  -- Append dLast, 0, 3, frontier (8 steps)
  let T3 := T2.move .right
  let T4 := T3.write (.cell dLast)
  let T5 := T4.move .right
  let T6 := T5.write (.cell ⟨0, by omega⟩)
  let T7 := T6.move .right
  let T8 := T7.write (.cell ⟨3, by omega⟩)
  let T9 := T8.move .right
  let T10 := T9.write .frontier
  have ha1 : TM0.step (simDelta M acc hvalid) ⟨.initEnd2Move dLast, T2⟩ = some ⟨.initEnd2Write dLast, T3⟩ :=
    step_move _ _ _ _ _ rfl
  have ha2 : TM0.step (simDelta M acc hvalid) ⟨.initEnd2Write dLast, T3⟩ = some ⟨.initEnd0Move, T4⟩ :=
    step_write _ _ _ _ _ rfl
  have ha3 : TM0.step (simDelta M acc hvalid) ⟨.initEnd0Move, T4⟩ = some ⟨.initEnd0Write, T5⟩ :=
    step_move _ _ _ _ _ rfl
  have ha4 : TM0.step (simDelta M acc hvalid) ⟨.initEnd0Write, T5⟩ = some ⟨.initEnd3Move, T6⟩ :=
    step_write _ _ _ _ _ rfl
  have ha5 : TM0.step (simDelta M acc hvalid) ⟨.initEnd3Move, T6⟩ = some ⟨.initEnd3Write, T7⟩ :=
    step_move _ _ _ _ _ rfl
  have ha6 : TM0.step (simDelta M acc hvalid) ⟨.initEnd3Write, T7⟩ = some ⟨.initEndFMove, T8⟩ :=
    step_write _ _ _ _ _ rfl
  have ha7 : TM0.step (simDelta M acc hvalid) ⟨.initEndFMove, T8⟩ = some ⟨.initEndFWrite, T9⟩ :=
    step_move _ _ _ _ _ rfl
  have ha8 : TM0.step (simDelta M acc hvalid) ⟨.initEndFWrite, T9⟩ = some ⟨.initRewind, T10⟩ :=
    step_write _ _ _ _ _ rfl
  have hT10_nth : ∀ z : ℤ, T10.nth z =
      if z = 0 then .frontier
      else if z = -1 then .cell ⟨3, by omega⟩
      else if z = -2 then .cell ⟨0, by omega⟩
      else if z = -3 then .cell dLast
      else T2.nth (z + 4) := by
    intro z
    simp only [T10, T9, T8, T7, T6, T5, T4, T3, nth_write, nth_move_right]
    by_cases h0 : z = 0
    · subst h0; simp
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : z = -1
      · subst h1; simp
      · rw [if_neg (by omega), if_neg h1]
        by_cases h2 : z = -2
        · subst h2; simp
        · rw [if_neg (by omega), if_neg h2]
          by_cases h3 : z = -3
          · subst h3; simp
          · rw [if_neg (by omega), if_neg h3]; congr 1; omega
  let pre := [] ++ 3 :: CookLevin.symbolsOf x ++ [0] ++ CookLevin.symbolsOf c
  have hpreLen : pre.length = x.length + c.length + 2 := by
    simp [pre, CookLevin.symbolsOf]; omega
  have hpairEq : CookLevin.pairTape x c = pre ++ [0, 3] := by
    simp [CookLevin.pairTape, pre, List.append_assoc]
  have hpairLen : (CookLevin.pairTape x c).length = x.length + c.length + 4 := by
    rw [hpairEq]; simp [hpreLen]
  have hTM10 : TapeMatch N T10 (x.length + c.length + 4) (CookLevin.pairTape x c) := by
    obtain ⟨hdlLen, h1, h2, h3, h5⟩ := hDone
    simp only [List.length_nil, Nat.zero_add] at hdlLen h1 h2 h3
    have hdlPre : pre.dropLast.length = x.length + c.length + 1 := by
      simpa [pre] using hdlLen
    have hpairSplit : CookLevin.pairTape x c = pre.dropLast ++ (dLast.val :: [0, 3]) := by
      rw [hpairEq]
      have hpe : pre = pre.dropLast ++ [dLast.val] := hPreEq
      rw [hpe]
      simp [List.append_assoc]
    refine ⟨fun k hk => ?_, ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
    · rw [hT10_nth, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [show k - (x.length + c.length + 4 : ℕ) + 4 = k - (x.length + c.length : ℕ) by omega]
      exact h1 k hk
    · rw [hT10_nth, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [show (-1 : ℤ) - (x.length + c.length + 4 : ℕ) + 4 = -1 - (x.length + c.length : ℕ) by omega]
      exact h2
    · rw [hpairLen] at hi
      by_cases hi1 : i < x.length + c.length + 1
      · have hget : (CookLevin.pairTape x c)[i] = pre.dropLast[i]'(by omega) := by
          simp only [hpairSplit]
          exact List.getElem_append_left (by omega)
        obtain ⟨hv, heq⟩ := h3 i (by omega)
        refine ⟨by rw [hget]; exact hv, ?_⟩
        rw [hT10_nth, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        rw [show (i : ℤ) - (x.length + c.length + 4 : ℕ) + 4 = (i : ℤ) - (x.length + c.length : ℕ) by omega, heq]
        congr 1; exact Fin.ext hget.symm
      · by_cases hi2 : i = x.length + c.length + 1
        · subst hi2
          have hget : (CookLevin.pairTape x c)[x.length + c.length + 1] = dLast.val := by
            simp only [hpairSplit]
            rw [List.getElem_append_right (by omega)]
            simp [hdlPre]
          refine ⟨by rw [hget]; exact dLast.isLt, ?_⟩
          rw [hT10_nth, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          congr 1; exact Fin.ext hget.symm
        · by_cases hi3 : i = x.length + c.length + 2
          · subst hi3
            have hget : (CookLevin.pairTape x c)[x.length + c.length + 2] = 0 := by
              simp only [hpairEq]
              rw [List.getElem_append_right (by omega)]
              simp [hpreLen]
            refine ⟨by rw [hget]; omega, ?_⟩
            rw [hT10_nth, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
            congr 1; exact Fin.ext hget.symm
          · have hi4 : i = x.length + c.length + 3 := by omega
            subst hi4
            have hget : (CookLevin.pairTape x c)[x.length + c.length + 3] = 3 := by
              simp only [hpairEq]
              rw [List.getElem_append_right (by omega)]
              simp [hpreLen]
            refine ⟨by rw [hget]; omega, ?_⟩
            rw [hT10_nth, if_neg (by omega), if_pos (by omega)]
            congr 1; exact Fin.ext hget.symm
    · rw [hpairLen, hT10_nth, if_pos (by omega)]
    · rw [hpairLen] at hi
      rw [hT10_nth, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have := h5 (i - (x.length + c.length)) (by omega)
      simpa [show ((i - (x.length + c.length) : ℕ) : ℤ) = (i : ℤ) - (x.length + c.length + 4 : ℕ) + 4 by omega] using this
  obtain ⟨T', hrRew, hTM'⟩ := init_rewind_loop M acc hvalid (CookLevin.pairTape x c)
    (x.length + c.length + 4) T10 hTM10
  refine ⟨T', ?_, hTM'⟩
  have hrPre : Reaches (simDelta M acc hvalid) ⟨.initLeft, T0⟩ ⟨.init1Write ⟨3, by omega⟩, T1⟩ 3 :=
    reaches_trans _ (reaches_trans _ (reaches_step _ hs1) (reaches_step _ hs2)) (reaches_step _ hs3)
  have hrEnd : Reaches (simDelta M acc hvalid) ⟨.initEnd2Move dLast, T2⟩ ⟨.initRewind, T10⟩ 8 :=
    reaches_trans _
      (reaches_trans _ (reaches_trans _ (reaches_step _ ha1) (reaches_step _ ha2))
        (reaches_trans _ (reaches_step _ ha3) (reaches_step _ ha4)))
      (reaches_trans _ (reaches_trans _ (reaches_step _ ha5) (reaches_step _ ha6))
        (reaches_trans _ (reaches_step _ ha7) (reaches_step _ ha8)))
  have hrAll := reaches_trans _ (reaches_trans _ (reaches_trans _ hrPre hrShift) hrEnd) hrRew
  have hcnt : 3 + (2 * (x.length + c.length) + 1) + 8 + (x.length + c.length + 4 + 2) =
      3 * (x.length + c.length) + 18 := by omega
  rwa [hcnt] at hrAll

/-! ## Phase 2 + Phase 3: Simulating `runFlatTM` and writing `[cfg.state_idx == acc]` -/

private lemma doMove_sim (M : FlatTM) (acc : ℕ) (hvalid : validFlatTM M)
    (q' : Fin M.states) (d : TMMove) (head : ℕ) (right : List ℕ)
    (T : Tape (SimSym (max M.sig 4)))
    (hT : TapeMatch (max M.sig 4) T head right) :
    ∃ (T' : Tape (SimSym (max M.sig 4))) (k : ℕ), k ≤ 2 ∧
      Reaches (simDelta M acc hvalid) ⟨.doMove q' d, T⟩ ⟨.sim q', T'⟩ k ∧
      TapeMatch (max M.sig 4) T' (moveTapeHead ([], head, right) d).2.1 right := by
  cases d with
  | Nmove =>
    have hs : TM0.step (simDelta M acc hvalid) ⟨.doMove q' .Nmove, T⟩ =
        some ⟨.sim q', T.write T.head⟩ := step_write _ _ _ _ _ rfl
    have hwr : T.write T.head = T := by cases T; rfl
    rw [hwr] at hs
    exact ⟨T, 1, by omega, reaches_step _ hs, hT⟩
  | Rmove =>
    have hs : TM0.step (simDelta M acc hvalid) ⟨.doMove q' .Rmove, T⟩ =
        some ⟨.sim q', T.move .right⟩ := step_move _ _ _ _ _ rfl
    exact ⟨T.move .right, 1, by omega, reaches_step _ hs, tapeMatch_move_right hT⟩
  | Lmove =>
    have hs1 : TM0.step (simDelta M acc hvalid) ⟨.doMove q' .Lmove, T⟩ =
        some ⟨.checkLeftWall q', T.move .left⟩ := step_move _ _ _ _ _ rfl
    cases head with
    | zero =>
      have hwall : (T.move .left).head = SimSym.leftWall := by
        rw [← nth_zero, nth_move_left]; simpa using hT.2.1
      have hs2 : TM0.step (simDelta M acc hvalid) ⟨.checkLeftWall q', T.move .left⟩ =
          some ⟨.sim q', (T.move .left).move .right⟩ := by
        apply step_move; simp [simDelta, hwall]
      refine ⟨(T.move .left).move .right, 2, le_rfl,
        reaches_trans _ (reaches_step _ hs1) (reaches_step _ hs2), ?_⟩
      have hsame : ∀ z : ℤ, ((T.move .left).move .right).nth z = T.nth z := by
        intro z; rw [nth_move_right, nth_move_left]; congr 1; omega
      obtain ⟨h1, h2, h3, h4, h5⟩ := hT
      exact ⟨fun k hk => by rw [hsame]; exact h1 k hk, by rw [hsame]; exact h2,
        fun i hi => by obtain ⟨hv, heq⟩ := h3 i hi; exact ⟨hv, by rw [hsame]; exact heq⟩,
        by rw [hsame]; exact h4, fun i hi => by rw [hsame]; exact h5 i hi⟩
    | succ h0 =>
      have hT' := tapeMatch_move_left hT
      have hnotW : (T.move .left).head ≠ SimSym.leftWall := by
        rcases lt_trichotomy h0 right.length with hlt | heq | hgt
        · obtain ⟨_, hhd⟩ := tapeMatch_head_lt hT' hlt; rw [hhd]; intro h; cases h
        · rw [tapeMatch_head_eq hT' heq]; intro h; cases h
        · rw [tapeMatch_head_gt hT' hgt]; intro h; cases h
      have hs2 : TM0.step (simDelta M acc hvalid) ⟨.checkLeftWall q', T.move .left⟩ =
          some ⟨.sim q', (T.move .left).write (T.move .left).head⟩ := by
        apply step_write; unfold simDelta
        cases hhd : (T.move .left).head with
        | leftWall => exact absurd hhd hnotW
        | _ => rfl
      have hwr : (T.move .left).write (T.move .left).head = T.move .left := by
        cases T.move .left; rfl
      rw [hwr] at hs2
      exact ⟨T.move .left, 2, le_rfl,
        reaches_trans _ (reaches_step _ hs1) (reaches_step _ hs2), hT'⟩

private lemma finish_output (M : FlatTM) (acc : ℕ) (hvalid : validFlatTM M)
    (b : Bool) (T : Tape (SimSym (max M.sig 4))) :
    ∃ T', Reaches (simDelta M acc hvalid) ⟨.outMoveR, T.write (.outBit b)⟩ ⟨.halt, T'⟩ 3 ∧
      (simMachine M acc hvalid).Shows ⟨SimState.halt, T'⟩ [b] := by
  let T1 := (T.write (.outBit b)).move .right
  let T2 := T1.write .blank
  let T3 := T2.move .left
  have hs1 : TM0.step (simDelta M acc hvalid) ⟨.outMoveR, T.write (.outBit b)⟩ =
      some ⟨.outWriteBlank, T1⟩ := step_move _ _ _ _ _ rfl
  have hs2 : TM0.step (simDelta M acc hvalid) ⟨.outWriteBlank, T1⟩ =
      some ⟨.outMoveL, T2⟩ := step_write _ _ _ _ _ rfl
  have hs3 : TM0.step (simDelta M acc hvalid) ⟨.outMoveL, T2⟩ =
      some ⟨.halt, T3⟩ := step_move _ _ _ _ _ rfl
  refine ⟨T3, reaches_trans _ (reaches_trans _ (reaches_step _ hs1) (reaches_step _ hs2)) (reaches_step _ hs3), ?_⟩
  refine ⟨fun i hi => ?_, fun b' => ?_⟩
  · have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    show T3.right₀.nth 0 = SimSym.outBit b
    rw [right₀_nth_eq_nth]
    simp only [T3, T2, T1, nth_move_left, nth_write]
    rw [if_neg (by omega), nth_move_right, show ((0 : ℕ) : ℤ) - 1 + 1 = 0 by omega, nth_write, if_pos rfl]
  · show T3.right₀.nth 1 ≠ SimSym.outBit b'
    rw [right₀_nth_eq_nth]
    simp only [T3, T2, T1, nth_move_left, nth_write]
    rw [if_pos (by omega)]
    intro h; cases h

private lemma sim_runFlatTM (M : FlatTM) (acc : ℕ) (hvalid : validFlatTM M) (htapes : M.tapes = 1) :
    ∀ (n : ℕ) (q : Fin M.states) (head : ℕ) (right : List ℕ)
      (T : Tape (SimSym (max M.sig 4))) (cfg : FlatTMConfig),
      TapeMatch (max M.sig 4) T head right →
      runFlatTM n M ⟨q.val, [([], head, right)]⟩ = some cfg →
      haltingStateReached M cfg = true →
      ∃ (T' : Tape (SimSym (max M.sig 4))) (k : ℕ),
        k ≤ 6 * n + 4 ∧
        Reaches (simDelta M acc hvalid) ⟨.sim q, T⟩ ⟨.halt, T'⟩ k ∧
        (simMachine M acc hvalid).Shows ⟨SimState.halt, T'⟩ [cfg.state_idx == acc] := by
  intro n
  induction n with
  | zero =>
    intro q head right T cfg hT hrun hhalt
    simp only [runFlatTM, Option.some.injEq] at hrun
    subst hrun
    have hqhalt : M.halt.getD q.val false = true := hhalt
    have hs : TM0.step (simDelta M acc hvalid) ⟨.sim q, T⟩ =
        some ⟨.outMoveR, T.write (.outBit (q.val == acc))⟩ := by
      apply step_write
      dsimp [simDelta]; rw [if_pos hqhalt]
    obtain ⟨T', hrFin, hshows⟩ := finish_output M acc hvalid (q.val == acc) T
    exact ⟨T', 1 + 3, le_rfl, reaches_trans _ (reaches_step _ hs) hrFin, hshows⟩
  | succ m ih =>
    intro q head right T cfg hT hrun hhalt
    by_cases hqhalt : M.halt.getD q.val false = true
    · have hrun' : some ⟨q.val, [([], head, right)]⟩ = some cfg := by
        rw [runFlatTM] at hrun
        have hh : haltingStateReached M ⟨q.val, [([], head, right)]⟩ = true := hqhalt
        rw [hh] at hrun
        simpa using hrun
      injection hrun' with hcfg
      subst hcfg
      have hs : TM0.step (simDelta M acc hvalid) ⟨.sim q, T⟩ =
          some ⟨.outMoveR, T.write (.outBit (q.val == acc))⟩ := by
        apply step_write; dsimp [simDelta]; rw [if_pos hqhalt]
      obtain ⟨T', hrFin, hshows⟩ := finish_output M acc hvalid (q.val == acc) T
      exact ⟨T', 1 + 3, by omega, reaches_trans _ (reaches_step _ hs) hrFin, hshows⟩
    · have hqhaltF : M.halt.getD q.val false = false := by
        cases h : M.halt.getD q.val false <;> simp_all
      have hcur_eq : (match T.head with | SimSym.cell v => some v.val | _ => none) =
          currentTapeSymbol ([], head, right) := by
        unfold currentTapeSymbol
        rcases lt_trichotomy head right.length with hlt | heq | hgt
        · obtain ⟨hv, hhd⟩ := tapeMatch_head_lt hT hlt
          rw [hhd, dif_pos hlt]; rfl
        · rw [tapeMatch_head_eq hT heq, dif_neg (show ¬ head < right.length by omega)]
        · rw [tapeMatch_head_gt hT hgt, dif_neg (show ¬ head < right.length by omega)]
      have hpred : (fun e : FlatTMTransEntry =>
          entryMatchesConfig e ⟨q.val, [([], head, right)]⟩) =
          (fun e : FlatTMTransEntry =>
            e.src_state == q.val && decide (e.src_tape_vals =
              [match T.head with | SimSym.cell v => some v.val | _ => none])) := by
        funext e; simp [entryMatchesConfig, hcur_eq]
      rw [runFlatTM, show haltingStateReached M ⟨q.val, [([], head, right)]⟩ = false from hqhaltF] at hrun
      simp only [Bool.false_eq_true, ↓reduceIte, stepFlatTM, Option.bind_eq_bind, hpred] at hrun
      cases hfind : M.trans.find? (fun e => e.src_state == q.val &&
          decide (e.src_tape_vals = [match T.head with | SimSym.cell v => some v.val | _ => none])) with
      | none =>
        rw [hfind] at hrun
        simp only [Option.bind_none, Option.some.injEq] at hrun
        subst hrun
        simp only [haltingStateReached, hqhaltF, Bool.false_eq_true] at hhalt
      | some e =>
        have he_mem : e ∈ M.trans := List.mem_of_find?_eq_some hfind
        have he_val := hvalid.2.2 e he_mem
        have hdst_lt : e.dst_state < M.states := he_val.2.1
        have hlen_w : e.dst_write_vals.length = 1 := by rw [he_val.2.2.2.1, htapes]
        have hlen_d : e.move_dirs.length = 1 := by rw [he_val.2.2.2.2.1, htapes]
        rcases List.length_eq_one_iff.mp hlen_w with ⟨w, hw⟩
        rcases List.length_eq_one_iff.mp hlen_d with ⟨d, hd⟩
        have happ : applyTransitionEntry ⟨q.val, [([], head, right)]⟩ e =
            some ⟨e.dst_state, [tapeStep ([], head, right) w d]⟩ := by
          simp [applyTransitionEntry, hw, hd]
        rw [hfind, Option.bind_some, happ] at hrun
        let q' : Fin M.states := ⟨e.dst_state, hdst_lt⟩
        have hq'_eq : (if h : e.dst_state < M.states then ⟨e.dst_state, h⟩ else q) = q' :=
          dif_pos hdst_lt
        have hwrite_phase : ∃ (T1 : Tape (SimSym (max M.sig 4))) (k1 : ℕ),
            k1 ≤ 4 ∧
            Reaches (simDelta M acc hvalid) ⟨.sim q, T⟩ ⟨.doMove q' d, T1⟩ k1 ∧
            TapeMatch (max M.sig 4) T1 head (writeCurrentTapeSymbol ([], head, right) w).2.2 := by
          cases w with
          | none =>
            have hs : TM0.step (simDelta M acc hvalid) ⟨.sim q, T⟩ =
                some ⟨.doMove q' d, T.write T.head⟩ := by
              apply step_write; unfold simDelta
              simp only [hqhaltF, Bool.false_eq_true, ↓reduceIte, hfind, hw, hd,
                List.headD_cons, hq'_eq]
            have hwr : T.write T.head = T := by cases T; rfl
            rw [hwr] at hs
            exact ⟨T, 1, by omega, reaches_step _ hs, hT⟩
          | some v =>
            have hv_lt_sig : v < M.sig := by
              have hbdd := he_val.2.2.2.2.2.2
              simp [flatTMOptionSymbolsBounded, hw] at hbdd
              exact hbdd
            have hv_lt : v < max M.sig 4 := lt_of_lt_of_le hv_lt_sig (le_max_left _ _)
            let vf : Fin (max M.sig 4) := ⟨v, hv_lt⟩
            have hvf_eq : (if h : v < max M.sig 4 then ⟨v, h⟩ else ⟨0, by omega⟩) = vf :=
              dif_pos hv_lt
            rcases lt_trichotomy head right.length with hlt | heq | hgt
            · obtain ⟨_, hhd⟩ := tapeMatch_head_lt hT hlt
              have hfind' := hfind; rw [hhd] at hfind'
              have hs : TM0.step (simDelta M acc hvalid) ⟨.sim q, T⟩ =
                  some ⟨.doMove q' d, T.write (.cell vf)⟩ := by
                apply step_write; unfold simDelta
                simp only [hqhaltF, Bool.false_eq_true, ↓reduceIte, hhd, hfind', hw, hd,
                  List.headD_cons, hq'_eq, hvf_eq]
              refine ⟨T.write (.cell vf), 1, by omega, reaches_step _ hs, ?_⟩
              simpa [writeCurrentTapeSymbol, hlt, vf] using tapeMatch_write_in_range hT hlt vf
            · have hhd := tapeMatch_head_eq hT heq
              have hfind' := hfind; rw [hhd] at hfind'
              have hs1 : TM0.step (simDelta M acc hvalid) ⟨.sim q, T⟩ =
                  some ⟨.frontMoveR q' d, T.write (.cell vf)⟩ := by
                apply step_write; unfold simDelta
                simp only [hqhaltF, Bool.false_eq_true, ↓reduceIte, hhd, hfind', hw, hd,
                  List.headD_cons, hq'_eq, hvf_eq]
              have hs2 : TM0.step (simDelta M acc hvalid) ⟨.frontMoveR q' d, T.write (.cell vf)⟩ =
                  some ⟨.frontWriteF q' d, (T.write (.cell vf)).move .right⟩ :=
                step_move _ _ _ _ _ rfl
              have hs3 : TM0.step (simDelta M acc hvalid) ⟨.frontWriteF q' d, (T.write (.cell vf)).move .right⟩ =
                  some ⟨.frontMoveL q' d, ((T.write (.cell vf)).move .right).write .frontier⟩ :=
                step_write _ _ _ _ _ rfl
              have hs4 : TM0.step (simDelta M acc hvalid) ⟨.frontMoveL q' d, ((T.write (.cell vf)).move .right).write .frontier⟩ =
                  some ⟨.doMove q' d, (((T.write (.cell vf)).move .right).write .frontier).move .left⟩ :=
                step_move _ _ _ _ _ rfl
              have hr : Reaches (simDelta M acc hvalid) ⟨.sim q, T⟩
                  ⟨.doMove q' d, (((T.write (.cell vf)).move .right).write .frontier).move .left⟩ 4 :=
                reaches_trans _ (reaches_trans _ (reaches_step _ hs1) (reaches_step _ hs2))
                  (reaches_trans _ (reaches_step _ hs3) (reaches_step _ hs4))
              subst heq
              refine ⟨_, 4, le_rfl, hr, ?_⟩
              simpa [writeCurrentTapeSymbol, vf] using tapeMatch_write_frontier hT vf
            · have hhd := tapeMatch_head_gt hT hgt
              have hfind' := hfind; rw [hhd] at hfind'
              have hs : TM0.step (simDelta M acc hvalid) ⟨.sim q, T⟩ =
                  some ⟨.doMove q' d, T.write T.head⟩ := by
                apply step_write; unfold simDelta
                simp only [hqhaltF, Bool.false_eq_true, ↓reduceIte, hhd, hfind', hw, hd,
                  List.headD_cons, hq'_eq, hvf_eq]
              have hwr : T.write T.head = T := by cases T; rfl
              rw [hwr] at hs
              have hnotlt : ¬ (head < right.length) := by omega
              have hnoteq : ¬ (head = right.length) := by omega
              refine ⟨T, 1, by omega, reaches_step _ hs, ?_⟩
              simpa [writeCurrentTapeSymbol, hnotlt, hnoteq] using hT
        obtain ⟨T1, k1, hk1, hr1, hT1⟩ := hwrite_phase
        set right1 := (writeCurrentTapeSymbol ([], head, right) w).2.2 with hright1
        have hwr_eq : writeCurrentTapeSymbol ([], head, right) w = ([], head, right1) := by
          cases w <;> simp [writeCurrentTapeSymbol, hright1] <;> split_ifs <;> rfl
        have hstep_eq : tapeStep ([], head, right) w d =
            ([], (moveTapeHead ([], head, right1) d).2.1, right1) := by
          unfold tapeStep; rw [hwr_eq]; cases d <;> rfl
        obtain ⟨T2, k2, hk2, hr2, hT2⟩ := doMove_sim M acc hvalid q' d head right1 T1 hT1
        rw [hstep_eq] at hrun
        obtain ⟨T', k3, hk3, hr3, hshows⟩ :=
          ih q' (moveTapeHead ([], head, right1) d).2.1 right1 T2 cfg hT2 hrun hhalt
        refine ⟨T', k1 + k2 + k3, by omega,
          reaches_trans _ (reaches_trans _ hr1 hr2) hr3, hshows⟩

/-! ## Polynomial upper bound for `inOPoly t` -/

private lemma inOPoly_le_poly {t : ℕ → ℕ} (ht : inOPoly t) :
    ∃ (C k : ℕ), ∀ n : ℕ, t n ≤ C * n ^ k + C := by
  rcases ht with ⟨k, c, n0, hcn⟩
  let B := maxPrefix t n0
  refine ⟨c + B, k, fun n => ?_⟩
  by_cases hn : n0 ≤ n
  · have h1 := hcn n hn
    have h2 : c * n ^ k ≤ (c + B) * n ^ k := Nat.mul_le_mul_right _ (by omega)
    exact le_trans h1 (le_trans h2 (Nat.le_add_right _ _))
  · have h1 : t n ≤ B := le_maxPrefix t (by omega)
    omega

end PvsNP.Units.m1_flat_np_to_st_np

theorem PvsNP.Units.m1_flat_np_to_st_np :
    ∀ L : Language Bool, CookLevin.inNP (fun x => x ∈ L) → L ∈ PvsNP.SingleTape.NP := by
  intro L hNP
  rcases hNP with ⟨R, a, k_cert, b, t, M, acc, rej, ht, hvalid, htapes, hcert, hdec⟩
  classical
  let V : List Bool × List Bool → Bool := fun p => decide (R p.1 p.2)
  let p_cert : Polynomial ℕ := Polynomial.C b + Polynomial.C a * Polynomial.X ^ k_cert
  obtain ⟨C, k_t, hCk⟩ := PvsNP.Units.m1_flat_np_to_st_np.inOPoly_le_poly ht
  let p_time : Polynomial ℕ :=
    Polynomial.C (6 * C + 25) + Polynomial.C 3 * Polynomial.X +
      Polynomial.C (6 * C) * Polynomial.X ^ k_t
  refine ⟨V, p_cert, ⟨PvsNP.Units.m1_flat_np_to_st_np.simMachine M acc hvalid, p_time, ?_⟩, ?_⟩
  · rintro ⟨x, c⟩
    obtain ⟨cfg, hrun, hhalt, hacc, _⟩ := hdec x c
    obtain ⟨T1, hr1, hTM1⟩ := PvsNP.Units.m1_flat_np_to_st_np.phase1_init M acc hvalid x c
    obtain ⟨T2, k2, hk2, hr2, hshows⟩ :=
      PvsNP.Units.m1_flat_np_to_st_np.sim_runFlatTM M acc hvalid htapes (t (x.length + c.length))
        ⟨M.start, hvalid.1⟩ 0 (CookLevin.pairTape x c) T1 cfg hTM1 hrun hhalt
    have hbool_eq : (cfg.state_idx == acc) = V (x, c) := by
      apply Bool.eq_iff_iff.mpr
      simp only [V, beq_iff_eq, decide_eq_true_eq]
      exact hacc.symm
    have henc_ans : PvsNP.encodeAnswer (V (x, c)) = [cfg.state_idx == acc] := by
      simp [PvsNP.encodeAnswer, Computability.encodeBool, hbool_eq]
    rw [← henc_ans] at hshows
    have hrTot := PvsNP.Units.m1_flat_np_to_st_np.reaches_trans _ hr1 hr2
    have hlen_pair : (PvsNP.encodePair (x, c)).length = x.length + c.length := by
      change (x.map Sum.inl ++ c.map Sum.inr).length = x.length + c.length
      simp
    have ht_le : t (x.length + c.length) ≤ C * (x.length + c.length) ^ k_t + C :=
      hCk (x.length + c.length)
    have h6 : 6 * t (x.length + c.length) ≤ 6 * C * (x.length + c.length) ^ k_t + 6 * C := by
      calc 6 * t (x.length + c.length)
          ≤ 6 * (C * (x.length + c.length) ^ k_t + C) := Nat.mul_le_mul_left 6 ht_le
        _ = 6 * C * (x.length + c.length) ^ k_t + 6 * C := by ring
    have hpeval : p_time.eval (PvsNP.encodePair (x, c)).length =
        6 * C + 25 + 3 * (x.length + c.length) + 6 * C * (x.length + c.length) ^ k_t := by
      rw [hlen_pair]
      simp [p_time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    have hsteps_le : 3 * (x.length + c.length) + 18 + k2 ≤ p_time.eval (PvsNP.encodePair (x, c)).length := by
      rw [hpeval]; omega
    refine ⟨⟨PvsNP.Units.m1_flat_np_to_st_np.SimState.halt, T2⟩,
      ⟨⟨⟨3 * (x.length + c.length) + 18 + k2, hrTot⟩, hsteps_le⟩⟩, rfl, hshows⟩
  · intro x
    dsimp only at hcert
    rw [hcert x]
    have hp : p_cert.eval x.length = b + a * x.length ^ k_cert := by
      simp [p_cert, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    simp only [V, decide_eq_true_eq, hp, Nat.add_comm]
