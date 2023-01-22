Require Export PeanoNat.

(* Arith.Le
le is an order on nat

https://coq.inria.fr/library/Coq.Arith.Le.html

 *)


(*
Arith.Minus

https://coq.inria.fr/library/Coq.Arith.Arith_prebase.html
*)
Definition minus_Sn_m_stt := fun n m Hle => eq_sym (Nat.sub_succ_l m n Hle).
Notation minus_Sn_m := minus_Sn_m_stt.

Definition minus_n_O_stt := fun n => eq_sym (Nat.sub_0_r n).
Notation minus_n_O := minus_n_O_stt.

Definition minus_diag_reverse_stt := fun n => eq_sym (Nat.sub_diag n).
Notation minus_diag_reverse := minus_diag_reverse_stt.

(* Arith.Div2

https://coq.inria.fr/library/Coq.Arith.Div2.html#even_double_stt

Properties related to the double (2n)

 *)

Implicit Type n : nat.

Definition even_odd_double_stt n :
 (Nat.Even_alt n <-> n = Nat.double (Nat.div2 n)) /\ (Nat.Odd_alt n <-> n = S (Nat.double (Nat.div2 n))).
Proof.
 rewrite Nat.Even_alt_Even, Nat.Odd_alt_Odd; apply Nat.Even_Odd_double.
Qed.

Definition even_double_stt n : Nat.Even_alt n -> n = Nat.double (Nat.div2 n).
Proof proj1 (proj1 (even_odd_double_stt n)).
Notation even_double := even_double_stt.


Definition odd_double_stt n : Nat.Odd_alt n -> n = S (Nat.double (Nat.div2 n)).
Proof proj1 (proj2 (even_odd_double_stt n)).
Notation odd_double := odd_double_stt.


(* Arith.Even

https://github.com/coq/coq/blob/V8.16.1/theories/Arith/Even.v

 *)

Notation even_equiv := Nat.Even_alt_Even.

Notation odd_equiv := Nat.Odd_alt_Odd.
