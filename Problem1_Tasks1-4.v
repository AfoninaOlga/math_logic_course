Parameter V : Set.

Inductive Formula : Set :=
  | Top
  | Bottom
  | Var : V -> Formula
  | Not : Formula -> Formula
  | And : Formula -> Formula -> Formula
  | Or : Formula -> Formula -> Formula.
Notation "⊤" := Top.
Notation "⊥" := Bottom.
Notation "¬" := Not (at level 35).
Infix "∧" := And (at level 40).
Infix "∨" := Or (at level 41).

Definition Implication (φ ψ : Formula) : Formula := ¬φ ∨ ψ.
Definition Equivalence (φ ψ : Formula) : Formula := ¬φ ∧ ¬ψ ∨ φ ∧ ψ.
Infix "→" := Implication (at level 50).
Infix "↔" := Equivalence (at level 51).

Inductive bool : Type :=
  | true
  | false.

Definition Max (φ ψ : bool) : bool :=
  match φ, ψ with
  | false, false => false
  | _, _ => true
  end.

Definition Min (φ ψ : bool) : bool :=
  match φ, ψ with
  | true, true => true
  | _, _ => false
  end.

Compute (Min false true).

Fixpoint Interpretation (M: V -> bool) (φ : Formula) : bool :=
  match φ with
  | ⊤ => true
  | ⊥ => false
  | Var p => M p
  | ¬ψ => match (Interpretation M ψ) with
          | true => false
          | false => true
          end
  |ψ ∨ γ => Max (Interpretation M ψ) (Interpretation M γ)
  |ψ ∧ γ => Min (Interpretation M ψ) (Interpretation M γ)
  end.

Definition Model M φ := (Interpretation M φ) = true.
Definition Entails φ ψ := forall M, (Model M φ) -> (Model M ψ).
Definition Tautology φ := forall M, Model M φ.
Infix "⊨" := Entails (at level 53, left associativity).
Notation "ε⊨" := Tautology.
Definition LogicEquivalence φ ψ := (φ ⊨ ψ) /\ (ψ ⊨ φ).
Infix "~" := LogicEquivalence (at level 52).

Theorem Task_1a: forall φ ψ, ε⊨(φ → ψ) <-> φ ⊨ ψ.
Proof.
  intros.
  split.
  - intros H M.
    unfold Tautology in H.
    unfold Implication in H.
    intros.
    assert (Model M (¬φ ∨ ψ)).
    apply H.
    unfold Model in H, H0, H1.
    unfold Model.
    simpl in H1.
    rewrite H0 in H1.
    destruct (Interpretation M ψ).
    auto.
    auto.
  - intros H M.
    unfold Entails in H.
    unfold Implication.
    assert (Model M φ -> Model M ψ).
    apply H.
    unfold Model.
    unfold Model in H, H0.
    simpl.
    destruct (Interpretation M φ).
    rewrite H0.
    auto.
    auto.
    auto.
Qed.



Theorem Task_1b: forall φ ψ, ε⊨(φ ↔ ψ) <-> φ ~ ψ.
Proof.
  split.
  - unfold Tautology.
    split.
    + unfold Entails.
      intros.
      unfold Equivalence in H.
      assert (Model M ((¬) φ ∧ (¬) ψ ∨ φ ∧ ψ)).
      auto.
      unfold Model in H, H0, H1.
      unfold Model.
      simpl in H1.
      rewrite H0 in H1.
      destruct (Interpretation M ψ).
      auto.
      auto.
    + unfold Entails.
      intros.
      unfold Equivalence in H.
      assert (Model M ((¬) φ ∧ (¬) ψ ∨ φ ∧ ψ)).
      auto.
      unfold Model in H, H0, H1.
      unfold Model.
      simpl in H1.
      rewrite H0 in H1.
      destruct (Interpretation M φ).
      auto.
      auto.
  - intros H.
    unfold Tautology.
    intros M.
    unfold Model.
    unfold Equivalence.
    unfold LogicEquivalence in H.
    unfold Entails in H.
    unfold Model in H.
    destruct H.
    assert (Interpretation M φ = true ->
    Interpretation M ψ = true).
    apply H.
    assert (Interpretation M ψ = true ->
    Interpretation M φ = true).
    apply H0.
    simpl.
    destruct (Interpretation M φ).
    -- rewrite H1.
      auto.
      auto.
    -- destruct (Interpretation M ψ).
      auto.
      auto.
Qed.

Theorem Task_2a: forall φ, ¬(¬φ)~φ.
Proof.
  split.
  - unfold Entails.
    intros.
    unfold Model in H.
    simpl in H.
    unfold Model.
    destruct (Interpretation M φ).
    auto.
    auto.
  - unfold Entails.
    intros.
    unfold Model in H.
    unfold Model.
    simpl.
    destruct (Interpretation M φ).
    auto.
    auto.
Qed.

Theorem Task_2b: forall φ, ε⊨ (φ ∨ ¬φ).
Proof.
  intros.
  unfold Tautology.
  intros.
  unfold Model.
  simpl.
  destruct (Interpretation M φ).
  auto.
  auto.
Qed.

Theorem Task_2c: forall φ ψ η, φ ∧ (ψ ∨ η) ~ (φ ∧ ψ) ∨ (φ ∧ η).
Proof.
  split.
  - unfold Entails.
    intros.
    unfold Model in H.
    simpl in H.
    unfold Model.
    simpl.
    destruct (Interpretation M φ).
    destruct (Interpretation M ψ).
    auto.
    auto.
    auto.
  - unfold Entails.
    intros.
    unfold Model in H.
    simpl in H.
    unfold Model.
    simpl.
    destruct (Interpretation M φ).
    destruct (Interpretation M ψ).
    auto.
    auto.
    auto.
Qed.

Theorem Task_2d: forall φ ψ η, φ ∨ (ψ ∧ η) ~ (φ ∨ ψ) ∧ (φ ∨ η).
Proof.
  split.
  - unfold Entails.
    intros.
    unfold Model in H.
    simpl in H.
    unfold Model.
    simpl.
    destruct (Interpretation M φ).
    destruct (Interpretation M ψ).
    destruct (Interpretation M η).
    auto.
    auto.
    auto.
    destruct (Interpretation M ψ).
    auto.
    auto.
  - unfold Entails.
    intros.
    unfold Model in H.
    simpl in H.
    unfold Model.
    simpl.
    destruct (Interpretation M φ).
    destruct (Interpretation M ψ).
    destruct (Interpretation M η).
    auto.
    auto.
    auto.
    destruct (Interpretation M ψ).
    auto.
    auto.
Qed.

Theorem Task_2e: forall φ ψ, φ ∨ (φ ∧ ψ) ~ φ.
Proof.
  split.
  - unfold Entails.
    intros.
    unfold Model in H.
    simpl in H.
    unfold Model.
    destruct (Interpretation M φ).
    auto.
    auto.
  - unfold Entails.
    intros.
    unfold Model in H.
    unfold Model.
    simpl.
    destruct (Interpretation M φ).
    auto.
    auto.
Qed.

Theorem Task_2f: forall φ ψ, φ ∧ (φ ∨ ψ) ~ φ.
Proof.
  split.
  - unfold Entails.
    intros.
    unfold Model in H.
    simpl in H.
    unfold Model.
    destruct (Interpretation M φ).
    auto.
    auto.
  - unfold Entails.
    intros.
    unfold Model in H.
    unfold Model.
    simpl.
    destruct (Interpretation M φ).
    auto.
    auto.
Qed.

Theorem Task_2h: forall φ ψ, ¬(φ ∨ ψ) ~ ¬φ ∧ ¬ψ.
Proof.
  split.
  - unfold Entails.
    intros.
    unfold Model in H.
    simpl in H.
    unfold Model.
    simpl.
    destruct (Interpretation M φ).
    destruct (Interpretation M ψ).
    auto.
    auto.
    destruct (Interpretation M ψ).
    auto.
    auto.
  - unfold Entails.
    intros.
    unfold Model in H.
    simpl in H.
    unfold Model.
    simpl.
    destruct (Interpretation M φ).
    destruct (Interpretation M ψ).
    auto.
    auto.
    destruct (Interpretation M ψ).
    auto.
    auto.
Qed.

Theorem Task_3a: forall p q, ε⊨ ((p → q) ↔ (¬q → ¬p)).
Proof.
  intros.
  unfold Tautology.
  intros.
  unfold Model.
  simpl.
  destruct (Interpretation M p).
  destruct (Interpretation M q).
  auto.
  auto.
  destruct (Interpretation M q).
  auto.
  auto.
Qed.

Theorem Task_3b: forall p q r, ε⊨ ((p → (q → r)) ↔ (¬r → (¬q → ¬p))).
Proof.
  unfold Tautology.
  intros.
  unfold Model.
  simpl.
  destruct (Interpretation M p).
  - destruct (Interpretation M q).
    -- destruct (Interpretation M r).
      simpl.
      auto.
      simpl.
      Abort.
(*для p=q=r=true получили true=true, формула выполнима;
  для p=q=true, r=false получили false=true, формула необщезначима*)
Theorem Task_4ab: forall p q r, ¬(¬(p ∧ q) → ¬r) ~ (¬p ∨ ¬q) ∧ r.
Proof.
  split.
  - unfold Entails.
    intros.
    unfold Model in H.
    simpl in H.
    unfold Model.
    simpl.
    destruct (Interpretation M p).
    destruct (Interpretation M q).
    auto.
    destruct (Interpretation M r).
    auto.
    auto.
    destruct (Interpretation M q).
    destruct (Interpretation M r).
    auto.
    auto.
    destruct (Interpretation M r).
    auto.
    auto.
  - unfold Entails.
    intros.
    unfold Model in H.
    simpl in H.
    unfold Model.
    simpl.
    destruct (Interpretation M p).
    destruct (Interpretation M q).
    auto.
    destruct (Interpretation M r).
    auto.
    auto.
    destruct (Interpretation M q).
    destruct (Interpretation M r).
    auto.
    auto.
    destruct (Interpretation M r).
    auto.
    auto.
Qed.

Theorem Task_4ac: forall p q r, ¬(¬(p ∧ q) → ¬r) ~ (¬p ∧ r) ∨ (¬q ∧ r).
Proof.
  split.
  - unfold Entails.
    intros.
    unfold Model in H.
    simpl in H.
    unfold Model.
    simpl.
    destruct (Interpretation M p).
    destruct (Interpretation M q).
    auto.
    destruct (Interpretation M r).
    auto.
    auto.
    destruct (Interpretation M q).
    destruct (Interpretation M r).
    auto.
    auto.
    destruct (Interpretation M r).
    auto.
    auto.
  - unfold Entails.
    intros.
    unfold Model in H.
    simpl in H.
    unfold Model.
    simpl.
    destruct (Interpretation M p).
    destruct (Interpretation M q).
    auto.
    destruct (Interpretation M r).
    auto.
    auto.
    destruct (Interpretation M q).
    destruct (Interpretation M r).
    auto.
    auto.
    destruct (Interpretation M r).
    auto.
    auto.
Qed.

