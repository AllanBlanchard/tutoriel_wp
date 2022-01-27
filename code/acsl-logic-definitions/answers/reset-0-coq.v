Inductive P_zeroed: (addr -> Z) -> addr ->
  Z -> Z -> Prop :=
  | Q_zeroed_empty : forall (Mint:addr -> Z) (a:addr) (b:Z) (e:Z),
      (e <= b)%Z -> is_sint32_chunk Mint -> P_zeroed Mint a b e
  | Q_zeroed_range : forall (Mint:addr -> Z) (a:addr) (b:Z) (e:Z),
      let x := ((-1%Z)%Z + e)%Z in
      let x1 := Mint (shift a x) in
      (x1 = 0%Z) -> (b < e)%Z -> is_sint32_chunk Mint ->
      P_zeroed Mint a b x -> is_sint32 x1 -> P_zeroed Mint a b e.

Definition P_same_elems (Mint:addr -> Z)
    (Mint1:addr -> Z) (a:addr) (b:Z) (e:Z) : Prop :=
  forall (i:Z),
  let a1 := shift a i in (b <= i)%Z -> (i < e)%Z -> ((Mint1 a1) = (Mint a1)).

(* The property to prove *)
Theorem wp_goal :
  forall (t:addr -> Z) (t1:addr -> Z) (a:addr) (i:Z) (i1:Z),
  is_sint32_chunk t1 -> is_sint32_chunk t -> P_zeroed t1 a i i1 ->
  P_same_elems t t1 a i i1 -> P_zeroed t a i i1.
Proof.
  Require Import Psatz. (* Used for reasoning on integers *)

  (* We introduce our variable and the main hypothese *)
  intros Mi' Mi arr b e tMi tMi' H.
  (* We reason by induction on our first (inductive) hypothese *)
  induction H ; intros Same.
  + (* Base case, immediate by using the first case of the inductive predicate *)
    constructor 1 ; auto.
  + unfold x in * ; clear x.
    (* Induction case, by using the second case of the inductive predicate.
       Most premises are trivial or just simple integers relations. *)
      constructor 2 ; auto ; try lia.
    - (* First: the first cell in new memory must be zero, we replace 0 with
         the cell in old memory *)
      rewrite <- H ; symmetry.
      (* And show that the cells are the same *)
      apply Same ; lia.
    - (* Third we use our induction hypothesis to show that the property
         holds on the first part of the array *)

      apply IHP_zeroed ; auto.
      intros i' ; intros.
      apply Same ; lia.
Qed.
