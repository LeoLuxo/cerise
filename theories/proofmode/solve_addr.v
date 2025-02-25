From Coq Require Import ZArith Lia.
From stdpp Require Import list.
From cap_machine Require Import addr_reg.
From machine_utils Require Import solve_finz.

Ltac zify_addr := zify_finz.
Tactic Notation "solve_addr" := solve_finz.
Tactic Notation "solve_addr" "-" hyp_list(Hs) := clear Hs; solve_addr.
Tactic Notation "solve_addr" "+" hyp_list(Hs) := clear -Hs; solve_addr.

(* --------------------------- BASIC LEMMAS --------------------------------- *)

(** Physical Address arithmetic *)

Lemma phys_addr_add_0 (a: PhysAddr): (a + 0)%a = Some a.
Proof. solve_addr. Qed.

Lemma incr_phys_addr_one_none (a: PhysAddr) :
  (a + 1)%a = None ->
  a = top_phys.
Proof. solve_addr. Qed.

Lemma incr_phys_addr_opt_add_twice (a: PhysAddr) (n m: Z) :
  (0 <= n)%Z ->
  (0 <= m)%Z ->
  ((a ^+ n) ^+ m)%a = (a ^+ (n + m)%Z)%a.
Proof. solve_addr. Qed.

Lemma incr_phys_addr_opt_add_twice' (a: PhysAddr) (n m: Z) :
  (0 <= n)%Z ->
  (0 <= m)%Z ->
  ((a ^+ n) ^+ m)%a = (a ^+ (n + m)%Z)%a.
Proof. zify_addr;[]. (* only one goal! *) lia. Qed.

Lemma phys_top_le_eq (a: PhysAddr) : (top_phys <= a)%a → a = top_phys.
Proof. solve_addr. Qed.

Lemma phys_top_not_le_eq (a: PhysAddr) : ¬ (a < top_phys)%a → a = top_phys.
Proof. solve_addr. Qed.

Lemma phys_next_lt (a a' : PhysAddr) :
  (a + 1)%a = Some a' → (a < a')%Z.
Proof. solve_addr. Qed.

Lemma phys_next_lt_i (a a' : PhysAddr) (i : Z) :
  (i > 0)%Z →
  (a + i)%a = Some a' → (a < a')%Z.
Proof. solve_addr. Qed.

Lemma phys_next_le_i (a a' : PhysAddr) (i : Z) :
  (i >= 0)%Z →
  (a + i)%a = Some a' → (a <= a')%Z.
Proof. solve_addr. Qed.

Lemma phys_next_lt_top (a : PhysAddr) i :
  (i > 0)%Z →
  is_Some (a + i)%a → a ≠ top_phys.
Proof. intros ? [? ?] ?. solve_addr. Qed.

Lemma phys_addr_next_le (a e : PhysAddr) :
  (a < e)%Z → ∃ a', (a + 1)%a = Some a'.
Proof. intros. zify_addr; eauto. exfalso. lia. lia. Qed.

Lemma phys_addr_next_lt (a e : PhysAddr) :
  (a < e)%Z -> ∃ a', (a + 1)%a = Some a'.
Proof. intros. zify_addr; eauto. exfalso. lia. lia. Qed.

Lemma phys_addr_next_lt_gt_contr (a e a' : PhysAddr) :
  (a < e)%Z → (a + 1)%a = Some a' → (e < a')%Z → False.
Proof. solve_addr. Qed.

Lemma phys_addr_next_lt_le (a e a' : PhysAddr) :
  (a < e)%Z → (a + 1)%a = Some a' → (a' ≤ e)%Z.
Proof. solve_addr. Qed.

Lemma phys_addr_abs_next (a e a' : PhysAddr) :
  (a + 1)%a = Some a' → (a < e)%Z → (Z.abs_nat (e - a) - 1) = (Z.abs_nat (e - a')).
Proof. solve_addr. Qed.

Lemma incr_phys_addr_trans (a1 a2 a3 : PhysAddr) (z1 z2 : Z) :
  (a1 + z1)%a = Some a2 → (a2 + z2)%a = Some a3 →
  (a1 + (z1 + z2))%a = Some a3.
Proof. solve_addr. Qed.

Lemma phys_addr_add_assoc (a a' : PhysAddr) (z1 z2 : Z) :
  (a + z1)%a = Some a' →
  (a + (z1 + z2))%a = (a' + z2)%a.
Proof. solve_addr. Qed.

Lemma incr_phys_addr_le (a1 a2 a3 : PhysAddr) (z1 z2 : Z) :
  (a1 + z1)%a = Some a2 -> (a1 + z2)%a = Some a3 -> (z1 <= z2)%Z ->
  (a2 <= a3)%Z.
Proof. solve_addr. Qed.

Lemma incr_phys_addr_ne (a: PhysAddr) i :
  i ≠ 0%Z → a ≠ top_phys →
  (a ^+ i)%a ≠ a.
Proof. intros H1 H2. intro. apply H2. solve_addr. Qed.

Lemma incr_phys_addr_ne_top (a a': PhysAddr) z :
  (z > 0)%Z → (a + z)%a = Some a' →
  a ≠ top_phys.
Proof. intros. intro. solve_addr. Qed.

Lemma get_phys_addrs_from_option_phys_addr_comm (a: PhysAddr) i k :
  (k >= 0)%Z -> (i >= 0)%Z ->
  (((a ^+ i) ^+ k)%a) =
  ((a ^+ (i + k)%Z)%a).
Proof. solve_addr. Qed.

Lemma incr_phys_addr_of_z (a a' : PhysAddr) :
  (a + 1)%a = Some a' →
  (a + 1)%Z = a'.
Proof. solve_addr. Qed.

Lemma incr_phys_addr_of_z_i (a a' : PhysAddr) i :
  (a + i)%a = Some a' →
  (a + i)%Z = a'.
Proof. solve_addr. Qed.

Lemma invert_incr_phys_addr (a1 a2: PhysAddr) (z:Z):
      (a1 + z)%a = Some a2 → (a2 + (- z))%a = Some a1.
Proof. solve_addr. Qed.




(** Virtual Address arithmetic *)

Lemma virt_addr_add_0 (a: VirtAddr): (a + 0)%a = Some a.
Proof. solve_addr. Qed.

Lemma incr_virt_addr_one_none (a: VirtAddr) :
  (a + 1)%a = None ->
  a = top_virt.
Proof. solve_addr. Qed.

Lemma incr_virt_addr_opt_add_twice (a: VirtAddr) (n m: Z) :
  (0 <= n)%Z ->
  (0 <= m)%Z ->
  ((a ^+ n) ^+ m)%a = (a ^+ (n + m)%Z)%a.
Proof. solve_addr. Qed.

Lemma incr_virt_addr_opt_add_twice' (a: VirtAddr) (n m: Z) :
  (0 <= n)%Z ->
  (0 <= m)%Z ->
  ((a ^+ n) ^+ m)%a = (a ^+ (n + m)%Z)%a.
Proof. zify_addr;[]. (* only one goal! *) lia. Qed.

Lemma virt_top_le_eq (a: VirtAddr) : (top_virt <= a)%a → a = top_virt.
Proof. solve_addr. Qed.

Lemma virt_top_not_le_eq (a: VirtAddr) : ¬ (a < top_virt)%a → a = top_virt.
Proof. solve_addr. Qed.

Lemma virt_next_lt (a a' : VirtAddr) :
  (a + 1)%a = Some a' → (a < a')%Z.
Proof. solve_addr. Qed.

Lemma virt_next_lt_i (a a' : VirtAddr) (i : Z) :
  (i > 0)%Z →
  (a + i)%a = Some a' → (a < a')%Z.
Proof. solve_addr. Qed.

Lemma virt_next_le_i (a a' : VirtAddr) (i : Z) :
  (i >= 0)%Z →
  (a + i)%a = Some a' → (a <= a')%Z.
Proof. solve_addr. Qed.

Lemma virt_next_lt_top (a : VirtAddr) i :
  (i > 0)%Z →
  is_Some (a + i)%a → a ≠ top_virt.
Proof. intros ? [? ?] ?. solve_addr. Qed.

Lemma virt_addr_next_le (a e : VirtAddr) :
  (a < e)%Z → ∃ a', (a + 1)%a = Some a'.
Proof. intros. zify_addr; eauto. exfalso. lia. lia. Qed.

Lemma virt_addr_next_lt (a e : VirtAddr) :
  (a < e)%Z -> ∃ a', (a + 1)%a = Some a'.
Proof. intros. zify_addr; eauto. exfalso. lia. lia. Qed.

Lemma virt_addr_next_lt_gt_contr (a e a' : VirtAddr) :
  (a < e)%Z → (a + 1)%a = Some a' → (e < a')%Z → False.
Proof. solve_addr. Qed.

Lemma virt_addr_next_lt_le (a e a' : VirtAddr) :
  (a < e)%Z → (a + 1)%a = Some a' → (a' ≤ e)%Z.
Proof. solve_addr. Qed.

Lemma virt_addr_abs_next (a e a' : VirtAddr) :
  (a + 1)%a = Some a' → (a < e)%Z → (Z.abs_nat (e - a) - 1) = (Z.abs_nat (e - a')).
Proof. solve_addr. Qed.

Lemma incr_virt_addr_trans (a1 a2 a3 : VirtAddr) (z1 z2 : Z) :
  (a1 + z1)%a = Some a2 → (a2 + z2)%a = Some a3 →
  (a1 + (z1 + z2))%a = Some a3.
Proof. solve_addr. Qed.

Lemma virt_addr_add_assoc (a a' : VirtAddr) (z1 z2 : Z) :
  (a + z1)%a = Some a' →
  (a + (z1 + z2))%a = (a' + z2)%a.
Proof. solve_addr. Qed.

Lemma incr_virt_addr_le (a1 a2 a3 : VirtAddr) (z1 z2 : Z) :
  (a1 + z1)%a = Some a2 -> (a1 + z2)%a = Some a3 -> (z1 <= z2)%Z ->
  (a2 <= a3)%Z.
Proof. solve_addr. Qed.

Lemma incr_virt_addr_ne (a: VirtAddr) i :
  i ≠ 0%Z → a ≠ top_virt →
  (a ^+ i)%a ≠ a.
Proof. intros H1 H2. intro. apply H2. solve_addr. Qed.

Lemma incr_virt_addr_ne_top (a a': VirtAddr) z :
  (z > 0)%Z → (a + z)%a = Some a' →
  a ≠ top_virt.
Proof. intros. intro. solve_addr. Qed.

Lemma get_virt_addrs_from_option_virt_addr_comm (a: VirtAddr) i k :
  (k >= 0)%Z -> (i >= 0)%Z ->
  (((a ^+ i) ^+ k)%a) =
  ((a ^+ (i + k)%Z)%a).
Proof. solve_addr. Qed.

Lemma incr_virt_addr_of_z (a a' : VirtAddr) :
  (a + 1)%a = Some a' →
  (a + 1)%Z = a'.
Proof. solve_addr. Qed.

Lemma incr_virt_addr_of_z_i (a a' : VirtAddr) i :
  (a + i)%a = Some a' →
  (a + i)%Z = a'.
Proof. solve_addr. Qed.

Lemma invert_incr_virt_addr (a1 a2: VirtAddr) (z:Z):
      (a1 + z)%a = Some a2 → (a2 + (- z))%a = Some a1.
Proof. solve_addr. Qed.
