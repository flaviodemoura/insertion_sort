(** Algoritmo de Ordenação por Inserção em listas *)

Require Import Arith List.

(** * Definição de ordenação *)

Inductive sorted :list nat -> Prop :=
  | nil_sorted : sorted nil
  | one_sorted: forall n:nat, sorted (n :: nil)
  | all_sorted : forall (x y: nat) (l:list nat), sorted (y :: l) -> x <= y -> sorted (x :: y :: l).

(** * Definição da função auxiliar [insert] *)

Fixpoint insert (x:nat) (l: list nat) := match l with
                      | nil => x :: nil
                      | h :: tl => if x <=? h then (x :: l)
                                                  else (h :: (insert x tl)) 
                      end.

(** A função [insert] preserva a ordenação. *)

Lemma insert_preserves_sorting: forall l x, sorted l -> sorted (insert x l). 
Proof.
Admitted.

(** * Definição da função principal do algoritmo. *)

Fixpoint insertion_sort l := match l with
                             | nil =>l
                             | h :: tl => insert h (insertion_sort tl)
                             end.

(** O algoritmo [insertion_sort] ordena. *)

Lemma insertion_sort_sorts: forall l, sorted (insertion_sort l).
Proof.
Admitted.

(** * Permutação *)

Fixpoint num_oc n l  :=
  match l with
    | nil => 0
    | h :: tl =>
      if n =? h then S(num_oc n tl) else  num_oc n tl
  end.

Definition perm l l' := forall n:nat, num_oc n l = num_oc n l'.

(** A reflexividade é uma propriedade que pode ser obtida a partir desta definição: uma lista é sempre permutação dela mesma. *)

Lemma perm_refl: forall l, perm l l.
Proof.
intro l. unfold perm. intro. reflexivity.
Qed.

Lemma num_oc_insert_neq: forall l n a, n =? a = false -> num_oc n (insert a l) = num_oc n l.
Proof.
Admitted.

Lemma num_oc_insert: forall l n, num_oc n (insert n l) = S (num_oc n l).
Proof.
Admitted.

Lemma ord_insercao_perm: forall l, perm l (insertion_sort l).
Proof.
Admitted.
  
Theorem correcao_ord_insercao: forall l, sorted (insertion_sort l) /\ perm l (insertion_sort l).
Proof.
Admitted.
  
(** Extração de código certificado *)

Require Extraction.

Recursive Extraction insertion_sort.
Extraction "insertion_sort.ml" insertion_sort.

