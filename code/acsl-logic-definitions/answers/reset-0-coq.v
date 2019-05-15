Inductive P_zeroed : farray addr Z -> addr -> Z -> Z -> Prop :=
    | Q_zeroed_empty: forall (i_1 i : Z), forall (t : farray addr Z),
        forall (a : addr), ((i <= i_1)%Z) -> ((P_zeroed t a i_1%Z i%Z))
    | Q_zeroed_range: forall (i_1 i : Z), forall (t : farray addr Z),
        forall (a : addr), let x := (i%Z - 1%Z)%Z in
        (((t.[ (shift_sint32 a x) ]) = 0)%Z) -> ((i_1 < i)%Z) ->
        ((P_zeroed t a i_1%Z x)) -> ((P_zeroed t a i_1%Z i%Z)).

Definition P_same_elems (Mint_0 : farray addr Z) (Mint_1 : farray addr Z)
    (a : addr) (b : Z) (e : Z) : Prop :=
    forall (i : Z), let a_1 := (shift_sint32 a i%Z) in ((b <= i)%Z) ->
      ((i < e)%Z) -> (((Mint_1.[ a_1 ]) = (Mint_0.[ a_1 ]))%Z).

(* The property to prove *)
Goal
  forall (i_1 i : Z),
  forall (t_1 t : farray addr Z),
  forall (a : addr),
  ((P_zeroed t a i_1%Z i%Z)) ->
  ((P_same_elems t_1 t a i_1%Z i%Z)) ->
  ((P_zeroed t_1 a i_1%Z i%Z)).

Proof.
  (* We introduce our variable and the main hypothese *)
  intros b e Mi Mi' arr H.
  (* We reason by induction on our first (inductive) hypothese *)
  induction H ; intros Same.
  (* Base case, by using the first case of the inductive predicate *)
  + constructor 1.
    (* The only premise to prove is a trivial relation between the bounds *)
    omega.
  + unfold x in * ; clear x.
    (* Induction case, by using the second case of the inductive predicate*)
    constructor 2.
    (* We have three premises *)
    - (* First: the first cell in new memory must be zero, we replace 0 with 
         the cell in old memory *)
      rewrite <- H ; symmetry.
      (* And show that the cells are the same *)
      apply Same ; omega.
    - (* Second, we have to prove a trivial relation about the bounds *)
      omega.
    - (* Third we use our induction hypothesis to show that the property
         holds on the first part of the array *)
      apply IHP_zeroed.
      intros i' ; intros.
      apply Same ; omega.
Qed.

