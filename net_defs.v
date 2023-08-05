(*
  Определения:
Множество идентификаторов кортежей: L, |L| ≥ 0
Множество идентификаторных кортежей длины n ∈ ℕ₀: T^n ⊆ Lⁿ.
Множество ассоциаций: A ⊆ L × T^n.
Семейство функций: ∪_n {netⁿ | n ∈ ℕ₀} ⊆ A
Здесь ∪ обозначает объединение всех функций в семействе {netⁿ}, ⊆ обозначает "это подмножество", а A - пространство всех ассоциаций.
Это говорит о том, что все упорядоченные пары, полученные от функций netⁿ, являются подмножеством A.
Ассоциативная сеть кортежей длины n из семейства функций {netⁿ}, netⁿ : L → T^n отображает идентификатор l из множества L в идентификаторный кортеж длины n,
который принадлежит множеству T^n. 'n' в netⁿ указывает на то, что функция возвращает кортежи, содержащие n идентификаторов. 
Ассоциативная сеть дуплетов: net² : L → T₂.
Ассоциативная сеть вложенных упорядоченных пар: net : L → P
, где P = {(∅,∅) | (∅,l) | (l1,l2), l, l1, l2 ∈ L} - это множество вложенных упорядоченных пар, которое состоит из пустых пар, пар, содержащих только один элемент, и пар, содержащих два элемента.
Дополнительные пояснения:
Кортеж длины n ∈ ℕ₀ можно представить как вложенные упорядоченные пары.
Идентификатор кортежа - уникальный идентификатор, каждый из которых связан с определенным кортежем.
Идентификаторный кортеж - это кортеж, состоящий из нуля или нескольких идентификаторов кортежей, где количество индексов соответствует количеству элементов кортежа.
Ассоциация - это упорядоченная пара, состоящая из идентификатора кортежа и кортежа идентификаторов. Эта структура служит для отображения между идентификаторами и кортежами.
Пустой кортеж представлен пустым множеством: () представлено как ∅.
*)

Section TuplesNets.
  (* Определяем базовый тип идентификаторов *)
  Parameter L: Type.

  (* Определение кортежа фиксированной длины n *)
  Fixpoint Tuple (n: nat) : Type :=
    match n with
    | 0 => unit
    | S n' => L * Tuple n'
    end.

  (* Определение ассоциативная сети кортежей фиксированной длины n *)
  Definition TuplesNet (n: nat) : Type := L -> Tuple n.
End TuplesNets.

Section NestedPairsNets.
  (* Определяем базовый тип идентификаторов *)
  Parameter L: Type.

  (* Определение вложенной пары с переменной длиной *)
  Inductive NestedPair : Type :=
  | singl : L -> NestedPair
  | nest : L -> NestedPair -> NestedPair.

  (* Определение ассоциативной сети с вложенными парами *)
  Definition NestedPairsNet : Type := L -> NestedPair. 
End NestedPairsNets.

Section DupletNets.
  (* Определяем базовый тип идентификаторов *)
  Parameter L: Type.
  
  (* Определение дуплета *)
  Definition Duplet := (L * L).
  
  (* Определение ассоциативной сети дуплетов *)
  Definition DupletNet : Type := L -> Duplet.
End DupletNets.
(*
Section ConversionFunction.
  Require Import List.

  Parameter L: Type.

  Inductive NestedPair : Type :=
  | singl : L -> NestedPair
  | nest : L -> NestedPair -> NestedPair.

  Fixpoint Tuple (n: nat) : Type :=
    match n with
    | 0 => unit
    | S n' => L * Tuple n'
    end.

  Fixpoint tupleToNestedPair {n: nat} : Tuple n -> NestedPair :=
    match n with
    | 0 => fun _ => singl tt (* или любое значение в L вместо tt *)
    | S n' => fun t => nest (fst t) (tupleToNestedPair (snd t))
    end.

  Definition convertTuplesNetToNestedPairsNet {n: nat} (tn: L -> Tuple n) : L -> NestedPair :=
    fun l => tupleToNestedPair (tn l).
End ConversionFunction.
*)
Section ConversionFunction.
  Require Import List.
  Require Import PeanoNat.

  Inductive NestedPair : Type :=
  | singl : nat -> NestedPair
  | nest : nat -> NestedPair -> NestedPair.

  Fixpoint Tuple (n: nat) : Type :=
    match n with
    | 0 => unit
    | S n' => nat * Tuple n'
    end.

  Fixpoint tupleToNestedPair {n: nat} : Tuple n -> NestedPair :=
    match n with
    | 0 => fun _ => singl 0
    | S n' => fun t => nest (fst t) (tupleToNestedPair (snd t))
    end.

  Definition convertTuplesNetToNestedPairsNet {n: nat} (tn: nat -> Tuple n) : nat -> NestedPair :=
    fun l => tupleToNestedPair (tn l).
End ConversionFunction.

Section ConversionProof.
  Require Import List.
  Require Import PeanoNat.

  Inductive NestedPair : Type :=
  | singl : NestedPair
  | nest : nat -> NestedPair -> NestedPair.

  Fixpoint Tuple (n: nat) : Type :=
    match n with
    | 0 => unit
    | S n' => nat * Tuple n'
    end.

  Fixpoint tupleToNestedPair {n: nat} : Tuple n -> NestedPair :=
    match n with
    | 0 => fun _ => singl
    | S n' => fun t => nest (fst t) (tupleToNestedPair (snd t))
    end.

  Fixpoint nestedPairLength (np : NestedPair) : nat :=
    match np with
    | singl => 0
    | nest _ np' => S (nestedPairLength np')
    end.

  Lemma tupleToNestedPair_keeps_length : forall n (t : Tuple n),
      nestedPairLength (tupleToNestedPair t) = n.
  Proof.
    intros n. induction n; intros t.
    - (* Case n = 0 *)
      simpl. reflexivity.
    - (* Case n = S n' *)
      simpl. f_equal. apply IHn.
  Qed.

  Definition convertTuplesNetToNestedPairsNet {n: nat} (tn: nat -> Tuple n) : nat -> NestedPair :=
    fun l => tupleToNestedPair (tn l).
End ConversionProof.



