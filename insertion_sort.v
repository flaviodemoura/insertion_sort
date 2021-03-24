(** * A correção do algoritmo de ordenação por inserção *)

(** O objetivo deste arquivo é servir de apoio ao desenvolvimento do projeto deste semestre. Aqui apresentaremos todo o processo de formalização do algoritmo de ordenação por inserção, e este processo deve servir como modelo para o desenvolvimento do seu projeto. *)

(* begin hide *)
Require Import Arith List.
(* end hide *)

(** Inicialmente apresentamos a definição do predicado [sorted] que é o mesmo apresentado no projeto, e por isto não nos preocuparemos em explicar aqui esta definição. *)

Inductive sorted :list nat -> Prop :=
  | nil_sorted : sorted nil
  | one_sorted: forall n:nat, sorted (n :: nil)
  | all_sorted : forall (x y: nat) (l:list nat), sorted (y :: l) -> x <= y -> sorted (x :: y :: l).

(** O algoritmo de ordenação por inserção é baseado em na função auxiliar [insert] que definimos a seguir. A função [insert] recebe um natural [x] e uma lista [l] como argumentos, e é definida recursivamente na estrutura de [l]: *)

Fixpoint insert (x:nat) (l: list nat) := match l with
                      | nil => x :: nil
                      | h :: tl => if x <=? h then (x :: l)
                                                  else (h :: (insert x tl)) 
                      end.

(** Como podemos observar, quando a lista [l] é a lista vazia, a função retorna a lista unitária contendo o elemento que foi inserido. Quando [l] não é a lista vazia, então ela tem a forma [h::tl], isto é, [l] tem [h] como primeiro elemento, e [tl] como cauda. Para saber onde inserir um elemento [x], comparamos [x] com [h], e quando [x] é menor ou igual a [h] simplesmente inserimos [x] na primeira posição da lista. Caso contrário, a função vai recursivamente encontrar a posição correta para inserir [x]. Assim, temos que a função [insert] é construída de forma a preservar a ordenação da lista recebida como segundo argumento. Este é exatamente o conteúdo do lema a seguir: *)

Lemma insert_preserves_sorting: forall l x, sorted l -> sorted (insert x l). 
Proof.
  (* A prova deste lema será apresentada em um vídeo, mas você já pode utilizá-lo em provas posteriores. *)
Admitted.

(** A função principal do algoritmo é dada a seguir: *)

Fixpoint insertion_sort l := match l with
                             | nil =>l
                             | h :: tl => insert h (insertion_sort tl)
                             end.

(** A função [insertion_sort] é  definida recursivamente na estrutura da lista [l] que é dada como argumento. Quando a lista é vazia não há nada a fazer, e caso contrário, a função [insert] é chamada para inserir a cabeça [h] da lista na cauda [tl] onde a função é aplicada recursivamente. O lema a seguir pede para você provar que a função [insertion_sort] retorna uma lista ordenada. *)

Lemma insertion_sort_sorts: forall l, sorted (insertion_sort l).
Proof.
Admitted.

(** A seguir apresentamos a definição de permutação a partir da contagem do número de ocorrências dos elementos nas listas, assim como apresentada no projeto mergesort deste semestre, e os lemas a seguir nos permitem concluir que o algoritmo [insertion_sort] é correto. *)

Fixpoint num_oc n l  :=
  match l with
    | nil => 0
    | h :: tl =>
      if n =? h then S(num_oc n tl) else  num_oc n tl
  end.

Definition perm l l' := forall n:nat, num_oc n l = num_oc n l'.

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

