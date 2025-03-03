From Coq Require Import Eqdep_dec. (* Needed to prove decidable equality on RegName *)
From Coq.micromega Require Import ZifyClasses.
From stdpp Require Import gmap fin_maps list.
From Coq Require Import ssreflect.
From cap_machine Require Import stdpp_extra.
From machine_utils Require Export finz.

(* No longer a coercion in Coq >= 8.14*)
Local Coercion Z.of_nat : nat >-> Z.

(* We assume a fixed set of registers, and a finite set of memory addresses.

   The exact size of the address space does not matter, it could be made a
   parameter of the machine.
*)

Definition RegNum: nat := 31.

(* ---------------------------------- Registers ----------------------------------------*)

Inductive RegName: Type :=
| PC
| R (n: nat) (fin: n <=? RegNum = true).

Global Instance reg_eq_dec : EqDecision RegName.
Proof. intros r1 r2.  destruct r1,r2; [by left | by right | by right |].
       destruct (Nat.eq_dec n n0).
       + subst n0. left.
         assert (forall (b: bool) (n m: nat) (P1 P2: n <=? m = b), P1 = P2).
         { intros. apply eq_proofs_unicity.
           intros; destruct x; destruct y; auto. }
         rewrite (H _ _ _ fin fin0). reflexivity.
       + right. congruence.
Defined.

Lemma reg_eq_sym (r1 r2 : RegName) : r1 ≠ r2 → r2 ≠ r1. Proof. auto. Qed.

Program Definition n_to_regname (n : nat) : option RegName :=
  match Nat.le_dec n RegNum with left _ => Some (R n _) | right _ => None end.
Next Obligation.
  intros. eapply Nat.leb_le; eauto.
Defined.

Global Instance reg_countable : Countable RegName.
Proof.
  refine {| encode r := encode match r with
                               | PC => inl ()
                               | R n fin => inr n
                               end ;
            decode n := match (decode n) with
                        | Some (inl ()) => Some PC
                        | Some (inr n) => n_to_regname n
                        | None => None
                        end ;
            decode_encode := _ |}.
  intro r. destruct r; auto.
  rewrite decode_encode.
  unfold n_to_regname.
  destruct (Nat.le_dec n RegNum).
  - do 2 f_equal. apply eq_proofs_unicity. decide equality.
  - exfalso. by apply (Nat.leb_le n RegNum) in fin.
Defined.

(* Instances for [zify]: make [lia] work on registers *)
(* TODO: separate the proof parts into lemmas *)

Definition Z_of_regname (r: RegName): Z.
  destruct r. exact 0.
  exact (S n).
Defined.

Instance RegName_InjTyp : InjTyp RegName Z.
  refine (mkinj _ _ Z_of_regname (fun n => n <= RegNum + 1)%Z _).
  intros [|]. cbn. lia. cbn. apply Nat.leb_le in fin. lia.
Defined.
Add Zify InjTyp RegName_InjTyp.

Instance Op_RegName_eq : BinRel (@eq RegName).
  refine ({| TR := @eq Z; TRInj := _ |}).
  cbn. intros r1 r2. split.
  - intros ->; eauto.
  - destruct r1; destruct r2; eauto; cbn; try apply Nat.leb_le in fin; try lia.
    intros ->%Nat2Z.inj%eq_add_S.
    f_equal. apply eq_proofs_unicity. intros [|] [|]; eauto.
Defined.
Add Zify BinRel Op_RegName_eq.

(* Names for registers *)
Definition r_t0 : RegName := R 0 eq_refl.
Definition r_t1 : RegName := R 1 eq_refl.
Definition r_t2 : RegName := R 2 eq_refl.
Definition r_t3 : RegName := R 3 eq_refl.
Definition r_t4 : RegName := R 4 eq_refl.
Definition r_t5 : RegName := R 5 eq_refl.
Definition r_t6 : RegName := R 6 eq_refl.
Definition r_t7 : RegName := R 7 eq_refl.
Definition r_t8 : RegName := R 8 eq_refl.
Definition r_t9 : RegName := R 9 eq_refl.
Definition r_t10 : RegName := R 10 eq_refl.
Definition r_t11 : RegName := R 11 eq_refl.
Definition r_t12 : RegName := R 12 eq_refl.
Definition r_t13 : RegName := R 13 eq_refl.
Definition r_t14 : RegName := R 14 eq_refl.
Definition r_t15 : RegName := R 15 eq_refl.
Definition r_t16 : RegName := R 16 eq_refl.
Definition r_t17 : RegName := R 17 eq_refl.
Definition r_t18 : RegName := R 18 eq_refl.
Definition r_t19 : RegName := R 19 eq_refl.
Definition r_t20 : RegName := R 20 eq_refl.
Definition r_t21 : RegName := R 21 eq_refl.
Definition r_t22 : RegName := R 22 eq_refl.
Definition r_t23 : RegName := R 23 eq_refl.
Definition r_t24 : RegName := R 24 eq_refl.
Definition r_t25 : RegName := R 25 eq_refl.
Definition r_t26 : RegName := R 26 eq_refl.
Definition r_t27 : RegName := R 27 eq_refl.
Definition r_t28 : RegName := R 28 eq_refl.
Definition r_t29 : RegName := R 29 eq_refl.
Definition r_t30 : RegName := R 30 eq_refl.
Definition r_t31 : RegName := R 31 eq_refl.

(* A list of all general purpuse registers (if regnum=31) *)
Definition all_registers : list RegName :=
  [r_t0;r_t1;r_t2;r_t3;r_t4;r_t5;r_t6;r_t7;r_t8;r_t9;r_t10;r_t11;r_t12;r_t13;
     r_t14;r_t15;r_t16;r_t17;r_t18;r_t19;r_t20;r_t21;r_t22;r_t23;r_t24;r_t25;r_t26;
       r_t27;r_t28;r_t29;r_t30;r_t31;PC].

(* Set of all registers *)
Definition all_registers_s : gset RegName := list_to_set all_registers.

Lemma all_registers_NoDup :
  NoDup all_registers.
Proof.
  unfold all_registers.
  repeat (
    apply NoDup_cons_2;
    first (repeat (rewrite not_elem_of_cons; split; [done|]); apply not_elem_of_nil)
  ).
  by apply NoDup_nil.
Qed.

(* Spec for all_registers *)

Lemma all_registers_correct r1 :
  r1 ∈ all_registers.
Proof.
  rewrite /all_registers.
  destruct r1.
  - do 32 (apply elem_of_cons; right).
      by apply elem_of_list_singleton.
  - induction n.
    + apply elem_of_cons; left.
      apply f_equal. apply eq_proofs_unicity. decide equality.
    + apply elem_of_list_lookup_2 with (S n).
      repeat (destruct n;
                first (simpl;do 2 f_equal;apply eq_proofs_unicity;decide equality)).
      simpl in *. inversion fin.
Qed.

Lemma all_registers_s_correct r:
  r ∈ all_registers_s.
Proof.
  rewrite /all_registers_s elem_of_list_to_set.
  apply all_registers_correct.
Qed.

Lemma all_registers_correct_sub r : NoDup r → r ⊆+ all_registers.
Proof.
  intros Hdup.
  apply NoDup_submseteq;auto. intros r' Hin.
  apply all_registers_correct.
Qed.

Instance setunfold_all_regs:
  forall x, SetUnfoldElemOf x all_registers_s True.
Proof.
  intros. constructor. split; auto.
  intro. eapply all_registers_s_correct.
Qed.

Lemma all_registers_union_l s :
  s ∪ all_registers_s = all_registers_s.
Proof.
  apply (anti_symm subseteq). 2: set_solver.
  rewrite elem_of_subseteq. intros ? _.
  apply all_registers_s_correct.
Qed.

Lemma all_registers_union_r s :
  all_registers_s ∪ s = all_registers_s.
Proof. rewrite union_comm_L. apply all_registers_union_l. Qed.

Lemma all_registers_subseteq s :
  s ⊆ all_registers_s.
Proof.
  rewrite elem_of_subseteq. intros ? _. apply all_registers_s_correct.
Qed.

Lemma regmap_full_dom {A} (r: gmap RegName A):
  (∀ x, is_Some (r !! x)) →
  dom r = all_registers_s.
Proof.
  intros Hfull. apply (anti_symm subseteq); rewrite elem_of_subseteq.
  - intros rr _. apply all_registers_s_correct.
  - intros rr _. rewrite elem_of_dom. apply Hfull.
Qed.




(* -------------------------------- Physical Memory addresses -----------------------------------*)


Definition MemNumPhys: Z := 2000000.
Global Opaque MemNumPhys.

Inductive PhysAddr : Type := 
  | PhysAddrCons: (finz MemNumPhys) -> PhysAddr.

Declare Scope PhysAddr_scope.
Delimit Scope PhysAddr_scope with pa.

Definition finz_to_phys_addr: (finz MemNumPhys) -> PhysAddr := PhysAddrCons.

Definition finz_to_phys_addr' (f : option (finz MemNumPhys)): option PhysAddr :=
  match f with
  | Some f => Some (PhysAddrCons f)
  | None => None
  end.

Definition finz_of_phys_addr (pa: PhysAddr): finz MemNumPhys := 
  match pa with
  | PhysAddrCons f => f
  end.

Definition z_of_phys_addr (pa: PhysAddr) : Z :=
  finz.to_z (finz_of_phys_addr pa).

Notation "a1 <= a2 < a3" := (@finz.le_lt MemNumPhys (finz_of_phys_addr a1) (finz_of_phys_addr a2) (finz_of_phys_addr a3)) : PhysAddr_scope.
Notation "a1 <= a2" := (@finz.le MemNumPhys (finz_of_phys_addr a1) (finz_of_phys_addr a2)) : PhysAddr_scope.
Notation "a1 <=? a2" := (@finz.leb MemNumPhys (finz_of_phys_addr a1) (finz_of_phys_addr a2)) : PhysAddr_scope.
Notation "a1 < a2" := (@finz.lt MemNumPhys (finz_of_phys_addr a1) (finz_of_phys_addr a2)) : PhysAddr_scope.
Notation "a1 <? a2" := (@finz.ltb MemNumPhys (finz_of_phys_addr a1) (finz_of_phys_addr a2)) : PhysAddr_scope.
Notation "a1 + z" := (finz_to_phys_addr' (@finz.incr MemNumPhys (finz_of_phys_addr a1) z)) : PhysAddr_scope.
Notation "a ^+ off" := (finz_to_phys_addr (@finz.incr_default MemNumPhys (finz_of_phys_addr a) off)) (at level 50) : PhysAddr_scope.

Notation za_phys := (finz_to_phys_addr (@finz.FinZ MemNumPhys 0%Z eq_refl eq_refl)).
Notation top_phys := (finz_to_phys_addr (finz.largest (finz_of_phys_addr za_phys))).
Notation "0" := (za_phys) : PhysAddr_scope.

Notation eqb_phys_addr := (λ (a1 a2: PhysAddr), Z.eqb (z_of_phys_addr a1) (z_of_phys_addr a2)).
Notation "a1 =? a2" := (eqb_phys_addr a1 a2) : PhysAddr_scope.

Notation phys_addr_incr_eq := (λ (a1: PhysAddr) (z: Z) (a2: PhysAddr), finz_incr_eq (finz_of_phys_addr a1) z (finz_of_phys_addr a2)).

Global Open Scope general_if_scope.

(* -------------------------------- Virtual Memory addresses -----------------------------------*)


Definition MemNumVirt: Z := MemNumPhys.
Global Opaque MemNumVirt.

Inductive VirtAddr : Type := 
  | VirtAddrCons: (finz MemNumVirt) -> VirtAddr.

Declare Scope VirtAddr_scope.
Delimit Scope VirtAddr_scope with va.

Definition finz_to_virt_addr: (finz MemNumVirt) -> VirtAddr := VirtAddrCons.

Definition finz_to_virt_addr' (f : option (finz MemNumVirt)): option VirtAddr :=
  match f with
  | Some f => Some (VirtAddrCons f)
  | None => None
  end.

Definition finz_of_virt_addr (pa: VirtAddr): finz MemNumVirt := 
  match pa with
  | VirtAddrCons f => f
  end.

Definition z_of_virt_addr (pa: VirtAddr) : Z :=
  finz.to_z (finz_of_virt_addr pa).

Notation "a1 <= a2 < a3" := (@finz.le_lt MemNumVirt (finz_of_virt_addr a1) (finz_of_virt_addr a2) (finz_of_virt_addr a3)) : VirtAddr_scope.
Notation "a1 <= a2" := (@finz.le MemNumVirt (finz_of_virt_addr a1) (finz_of_virt_addr a2)) : VirtAddr_scope.
Notation "a1 <=? a2" := (@finz.leb MemNumVirt (finz_of_virt_addr a1) (finz_of_virt_addr a2)) : VirtAddr_scope.
Notation "a1 < a2" := (@finz.lt MemNumVirt (finz_of_virt_addr a1) (finz_of_virt_addr a2)) : VirtAddr_scope.
Notation "a1 <? a2" := (@finz.ltb MemNumVirt (finz_of_virt_addr a1) (finz_of_virt_addr a2)) : VirtAddr_scope.
Notation "a1 + z" := (finz_to_virt_addr' (@finz.incr MemNumVirt (finz_of_virt_addr a1) z)) : VirtAddr_scope.
Notation "a ^+ off" := (finz_to_virt_addr (@finz.incr_default MemNumVirt (finz_of_virt_addr a) off)) (at level 50) : VirtAddr_scope.

Notation za_virt := (finz_to_virt_addr (@finz.FinZ MemNumVirt 0%Z eq_refl eq_refl)).
Notation top_virt := (finz_to_virt_addr (finz.largest (finz_of_virt_addr za_virt))).
Notation "0" := (za_virt) : VirtAddr_scope.

Notation eqb_virt_addr := (λ (a1 a2: VirtAddr), Z.eqb (z_of_virt_addr a1) (z_of_virt_addr a2)).
Notation "a1 =? a2" := (eqb_virt_addr a1 a2) : VirtAddr_scope.

Notation virt_addr_incr_eq := (λ (a1: VirtAddr) (z: Z) (a2: VirtAddr), finz_incr_eq (finz_of_virt_addr a1) z (finz_of_virt_addr a2)).

Global Open Scope general_if_scope.

(* -------------------------------- Address convertion -----------------------------------*)

(* TEMPORARILY: virtual and physical addresses are a 1-to-1 mapping *)
(* Definition virt_to_phys (v: VirtAddr) : option PhysAddr :=  z_to_phys_addr (z_of_virt_addr v). *)

(* Coerce physical addresses to virtual so we don't need to copy-paste all the lemmas *)
(* Definition phys_to_virt := (λ (a: PhysAddr), z_to_virt_addr (z_of_phys_addr a)). *)
(* Definition phys_to_virt (a : PhysAddr) : VirtAddr.
 (* := z_to_virt_addr (z_of_phys_addr a). *)
 Proof.
 destruct (z_of_phys_addr a).
 - auto.
 - admit.
 -  *)
  

(*
Definition coerce_phys_to_virt (a : PhysAddr) : VirtAddr.
Proof.
  (* apply (@finz.of_z MemNumVirt). *)
(* destruct (Z.lt_dec a MemNumPhys),(Z.le_dec 0%Z a). *)
  
  destruct (phys_to_virt a).
  - exact f.
  - exact None.
  - exact None. *)

(* Coercion phys_to_virt : PhysAddr >-> VirtAddr. *)



(* ---------------------------------- OTypes ----------------------------------------*)

(* Number of otypes in our system *)
Definition ONum: nat := 1000.
Global Opaque ONum.
Notation OType := (finz ONum).
Declare Scope OType_scope.
Delimit Scope OType_scope with ot.

Notation "a1 <= a2 < a3" := (@finz.le_lt ONum a1 a2 a3) : OType_scope.
Notation "a1 <= a2" := (@finz.le ONum a1 a2) : OType_scope.
Notation "a1 <=? a2" := (@finz.leb ONum a1 a2) : OType_scope.
Notation "a1 < a2" := (@finz.lt ONum a1 a2) : OType_scope.
Notation "a1 <? a2" := (@finz.ltb ONum a1 a2) : OType_scope.
Notation "a1 + z" := (@finz.incr ONum a1 z) : OType_scope.
Notation "a ^+ off" := (@finz.incr_default ONum a off) (at level 50) : OType_scope.

Notation z_to_otype := (@finz.of_z ONum).
Notation z_of_ot := (@finz.to_z ONum).

Notation za_ot := (@finz.FinZ ONum 0%Z eq_refl eq_refl).
Notation top_ot := (finz.largest za_phys : OType).
Notation "0" := (za_ot) : OType_scope.

Notation eqb_otype := (λ (a1 a2: OType), Z.eqb a1 a2).
Notation "a1 =? a2" := (eqb_otype a1 a2) : OType_scope.

Notation otype_incr_eq := (finz_incr_eq).
