From iris.base_logic.lib Require Export invariants token.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import lang proofmode notation.

Definition acquire : val :=
  rec: "loop" "l" :=
    if: CAS "l" #0 #1 then #() else "loop" "l".

Definition release : val :=
  λ: "l", "l" <- #0.

Class spin_lockG Σ := SpinLockG {
  #[local] spin_lock_tokG :: tokenG Σ;
}.

Definition spin_lockΣ : gFunctors := #[tokenΣ].

Global Instance subG_spin_lockΣ {Σ} : subG spin_lockΣ Σ → spin_lockG Σ.
Proof. solve_inG. Qed.

Section spec.
  Context `{!heapGS Σ, !spin_lockG Σ}.
  Let N := nroot .@ "spin_lock".

  Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    ∃ (b : Z), l ↦ #b ∗
      ⌜b = 0 ∨ b = 1⌝ ∗
      (if (decide (b = 0)) then token γ ∗ R else True).

  Definition is_lock (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    inv N (lock_inv γ l R).

  Definition locked (γ : gname) : iProp Σ := token γ.

  Global Instance is_lock_persistent γ l R : Persistent (is_lock γ l R).
  Proof. apply _. Qed.

  Lemma locked_exclusive γ : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iCombine "H1 H2" gives %?. Qed.

  Lemma acquire_spec γ (l : loc) R :
    {{{ is_lock γ l R }}}
      acquire #l
    {{{ RET #(); locked γ ∗ R }}}.
  Proof. Admitted.

  Lemma release_spec γ (l : loc) R :
    {{{ is_lock γ l R ∗ locked γ ∗ R }}}
      release #l
    {{{ RET #(); True }}}.
  Proof. Admitted.

End spec.
