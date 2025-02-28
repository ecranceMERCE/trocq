From Trocq Require Import Trocq.
From Coq Require Import ssreflect.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(*** D_arrow ***)

Print R_arrow.

(* For m = 0, (0, 0) and (0, 0) is of course optimal *)

Definition p44_true : Param44.Rel Unit Unit.
Proof.
by exists (fun _ _ => Unit);
   apply: (MkUMap idmap (fun a b e => tt) _ _); do ?case.
Defined.

Definition p00 (B B': Type) : Param00.Rel B B'.
Proof. by exists (fun B B' => Unit); exists. Defined.


Theorem D1_arrow_left_is_gt0: not (
    forall (A A' : Type) (AR: Param01.Rel A A'),
    forall (B B' : Type) (BR: Param00.Rel B B'),
    exists (R: Param10.Rel (A -> B) (A' -> B')),
      rel R = R_arrow AR BR
  ).
Proof.
  intro Habs.
  specialize (Habs _ _ p44_true).
  specialize (Habs Unit False (p00 _ _)).
  destruct Habs as [R Req].
  pose m := Param10.map _ _ R.
  destruct (m (fun t => t) tt).
Defined.

Definition p10_false : Param10.Rel False False.
Proof.
  exists (fun _ _ => Unit).
  - exists.
    exact (fun f => f).
  - exists.
Defined.

Theorem D1_arrow_right_is_gt0: not (
    forall (A A' : Type) (AR: Param00.Rel A A'),
    forall (B B' : Type) (BR: Param10.Rel B B'),
    exists (R: Param10.Rel (A -> B) (A' -> B')),
      rel R = R_arrow AR BR
  ).
Proof.
  intro Habs.
  specialize (Habs False Unit  (p00 _ _)).
  specialize (Habs _ _ p10_false).
  destruct Habs as [R Req].
  pose m := Param10.map _ _ R.
  destruct (m (fun f => f) tt).
Defined.

(* Thus, for m = 1, (0, 1) and (1, 0) is optimal *)

Definition p2b2b_empty_R : Param2b2b.Rel Unit Unit.
Proof.
  exists (fun _ _ => False).
  - exists (fun b => b).
    intros ? ? f ; destruct f.
  - exists (fun b => b).
    unfold sym_rel.
    intros ? ? f ; destruct f.
Defined.

Theorem D2a_arrow_right_is_gt1: not (
    forall (A A' : Type) (AR: Param02b.Rel A A'),
    forall (B B' : Type) (BR: Param10.Rel B B'),
    exists (R: Param2a0.Rel (A -> B) (A' -> B')),
      (* we would really want here to use definitional equality but it works nonetheless and def. eq. is stronger *)
      Param2a0.R _ _ R = R_arrow AR BR
  ).
Proof.
  intro Habs.
  specialize (Habs Unit Unit p44_true).
  specialize (Habs Unit Unit p2b2b_empty_R).
  destruct Habs as [R Req].
  have g2a := Param2a0.map_in_R _ _ R.
  induction (inverse Req) ; clear Req.

  set (id_t := fun (f: Unit) => tt).
  specialize (g2a id_t).
  set (transported_id_t := (Map2a.map
    (Param2a0.R _ _ R)
    (Param2a0.covariant _ _ R) id_t
  )).
  specialize (g2a transported_id_t).
  specialize (g2a (idpath _)).
  simpl in g2a ; unfold R_arrow in g2a.

  specialize (g2a tt tt tt).
  destruct g2a.
Qed.
Theorem D2a_arrow_right_isnt_2b: not (
    forall (A A' : Type) (AR: Param02b.Rel A A'),
    forall (B B' : Type) (BR: Param2b0.Rel B B'),
    exists (R: Param2a0.Rel (A -> B) (A' -> B')),
      (* we would really want here to use definitional equality but it works nonetheless and def. eq. is stronger *)
      Param2a0.R _ _ R = R_arrow AR BR
  ).
Proof.
  intro Habs.
  specialize (Habs Unit Unit p44_true).
  specialize (Habs Unit Unit p2b2b_empty_R).
  destruct Habs as [R Req].
  have g2a := Param2a0.map_in_R _ _ R.
  induction (inverse Req) ; clear Req.

  set (id_t := fun (f: Unit) => tt).
  specialize (g2a id_t).
  set (transported_id_t := (Map2a.map
    (Param2a0.R _ _ R)
    (Param2a0.covariant _ _ R) id_t
  )).
  specialize (g2a transported_id_t).
  specialize (g2a (idpath _)).
  simpl in g2a ; unfold R_arrow in g2a.

  specialize (g2a tt tt tt).
  destruct g2a.
Qed.

Definition p2a2a_A : Param2a2a.Rel Bool Bool.
Proof.
  exists (fun _ _ => Unit).
  - exists (fun b => b).
    unfold sym_rel.
    reflexivity.
  - exists (fun b => b).
    reflexivity.
Defined.

Definition p44_bool : Param44.Rel Bool Bool.
Proof.
  exists (fun b b' => b = b').
  - unshelve refine (MkUMap idmap (fun a b e => e) _ _).
    + intros ? ? e ; exact e.
    + intros ; reflexivity.
  - unshelve refine (MkUMap idmap (fun a b e => inverse e) _ _).
    + intros ? ? r ; exact (inverse r).
    + intros; apply inv_V.
Defined.

Theorem D2a_arrow_left_is_gt1: not (
    forall (A A' : Type) (AR: Param01.Rel A A'),
    forall (B B' : Type) (BR: Param2a0.Rel B B'),
    exists (R: Param2a0.Rel (A -> B) (A' -> B')),
      (* we would really want here to use definitional equality but it works nonetheless and def. eq. is stronger *)
      Param2a0.R _ _ R = R_arrow AR BR
  ).
Proof.
  intro Habs.
  specialize (Habs Bool Bool p2a2a_A).
  specialize (Habs Bool Bool p44_bool).
  destruct Habs as [R Req].
  have g2a := Param2a0.map_in_R _ _ R.

  set (id := fun (x: Bool) => x).
  specialize (g2a id).
  set (transported_id := (Map2a.map
    (Param2a0.R _ _ R)
    (Param2a0.covariant _ _ R) id
  )).
  specialize (g2a transported_id).
  specialize (g2a (idpath _)).
  simpl in g2a ; unfold R_arrow in g2a.

  induction (inverse Req) ; clear Req.
  assert (forall b, b = transported_id false) by (
    intro b ;
    apply (g2a b false tt)
  ).

  destruct (transported_id false).
  - destruct (false_ne_true (X false)).
  - destruct (true_ne_false (X true)).
Qed.

Theorem D2a_arrow_left_isnt_2a: not (
    forall (A A' : Type) (AR: Param02a.Rel A A'),
    forall (B B' : Type) (BR: Param2a0.Rel B B'),
    exists (R: Param2a0.Rel (A -> B) (A' -> B')),
      (* we would really want here to use definitional equality but it works nonetheless and def. eq. is stronger *)
      Param2a0.R _ _ R = R_arrow AR BR
  ).
Proof.
  intro Habs.
  specialize (Habs Bool Bool p2a2a_A).
  specialize (Habs Bool Bool p44_bool).
  destruct Habs as [R Req].
  have g2a := Param2a0.map_in_R _ _ R.

  set (id := fun (x: Bool) => x).
  specialize (g2a id).
  set (transported_id := (Map2a.map
    (Param2a0.R _ _ R)
    (Param2a0.covariant _ _ R) id
  )).
  specialize (g2a transported_id).
  specialize (g2a (idpath _)).
  simpl in g2a ; unfold R_arrow in g2a.

  induction (inverse Req) ; clear Req.
  assert (forall b, b = transported_id false) by (
    intro b ;
    apply (g2a b false tt)
  ).

  destruct (transported_id false).
  - destruct (false_ne_true (X false)).
  - destruct (true_ne_false (X true)).
Qed.

(* Thus, for m = 2a, (0, 2b) and (2a, 0) is optimal *)

Theorem D2b_arrow_left_is_gt1: not (
    forall (A A' : Type) (AR: Param01.Rel A A'),
    forall (B B' : Type) (BR: Param2b0.Rel B B'),
    exists (R: Param2b0.Rel (A -> B) (A' -> B')),
      (* we would really want here to use definitional equality but it works nonetheless and def. eq. is stronger *)
      Param2b0.R _ _ R = R_arrow AR BR
  ).
Proof.
  intro Habs.
  specialize (Habs Unit Unit p2b2b_empty_R).
  specialize (Habs Bool Bool p44_bool).
  destruct Habs as [R Req].
  have g2b := Param2b0.R_in_map _ _ R.
  induction (inverse Req) ; clear Req.

  assert (forall a b: Unit -> Bool,
    R_arrow p2b2b_empty_R p44_bool a b
  ) by (
    intros a b;
    unfold R_arrow;
    intros x x';
    simpl; unfold sym_rel;
    intro false ; destruct false
  ).

  assert (
    forall a b: Unit -> Bool,
      Map2b.map (Param2b0.R (Unit -> Bool) (Unit -> Bool) R)
                (Param2b0.covariant (Unit -> Bool) (Unit -> Bool) R) a = b
  ) by (
    intros a b ;
    apply (g2b a b) ;
    apply X
  ). clear X g2b.

  set (id_t := fun (f: Unit) => true).
  set (id_f := fun (f: Unit) => false).

  specialize (X0 id_t id_t) as Y1.
  specialize (X0 id_t id_f) as Y2.

  destruct (inverse Y2).
  assert (id_f tt = id_t tt).
  - destruct Y1.
    reflexivity.
  - destruct (false_ne_true X).
Qed.
Theorem D2b_arrow_left_isnt_2b: not (
    forall (A A' : Type) (AR: Param02b.Rel A A'),
    forall (B B' : Type) (BR: Param2b0.Rel B B'),
    exists (R: Param2b0.Rel (A -> B) (A' -> B')),
      (* we would really want here to use definitional equality but it works nonetheless and def. eq. is stronger *)
      Param2b0.R _ _ R = R_arrow AR BR
  ).
Proof.
  intro Habs.
  specialize (Habs Unit Unit p2b2b_empty_R).
  specialize (Habs Bool Bool p44_bool).
  destruct Habs as [R Req].
  have g2b := Param2b0.R_in_map _ _ R.
  induction (inverse Req) ; clear Req.

  assert (forall a b: Unit -> Bool,
    R_arrow p2b2b_empty_R p44_bool a b
  ) by (
    intros a b;
    unfold R_arrow;
    intros x x';
    simpl; unfold sym_rel;
    intro false ; destruct false
  ).

  assert (
    forall a b: Unit -> Bool,
      Map2b.map (Param2b0.R (Unit -> Bool) (Unit -> Bool) R)
                (Param2b0.covariant (Unit -> Bool) (Unit -> Bool) R) a = b
  ) by (
    intros a b ;
    apply (g2b a b) ;
    apply X
  ). clear X g2b.

  set (id_t := fun (f: Unit) => true).
  set (id_f := fun (f: Unit) => false).

  specialize (X0 id_t id_t) as Y1.
  specialize (X0 id_t id_f) as Y2.

  destruct (inverse Y2).
  assert (id_f tt = id_t tt).
  - destruct Y1.
    reflexivity.
  - destruct (false_ne_true X).
Qed.

Theorem D2b_arrow_right_is_gt1: not (
    forall (A A' : Type) (AR: Param02a.Rel A A'),
    forall (B B' : Type) (BR: Param10.Rel B B'),
    exists (R: Param2b0.Rel (A -> B) (A' -> B')),
      (* we would really want here to use definitional equality but it works nonetheless and def. eq. is stronger *)
      Param2b0.R _ _ R = R_arrow AR BR
  ).
Proof.
  intro Habs.
  specialize (Habs Unit Unit p44_true).
  specialize (Habs Bool Bool p2a2a_A).
  destruct Habs as [R Req].
  have g2b := Param2b0.R_in_map _ _ R.

  assert (forall f g: Unit -> Bool,
    Map2b.map (Param2b0.R (Unit -> Bool) (Unit -> Bool) R)
              (Param2b0.covariant (Unit -> Bool) (Unit -> Bool) R) f = g
  ).
  - intros f g.
    specialize (g2b f g).

    induction (inverse Req) ; clear Req.
    simpl in g2b ; unfold R_arrow, sym_rel in g2b.
    exact (g2b (fun _ _ _ => tt)).
  - set (const_true := fun (_: Unit) => true).
    set (const_false := fun (_: Unit) => false).

    specialize (X const_true const_true) as Y1.
    specialize (X const_true const_false) as Y2.
    destruct (inverse Y1).

    assert (const_true tt = const_false tt) by (rewrite Y2 ; reflexivity).
    destruct (true_ne_false X0).
Qed.

Theorem D2b_arrow_right_isnt_2a: not (
    forall (A A' : Type) (AR: Param02a.Rel A A'),
    forall (B B' : Type) (BR: Param2a0.Rel B B'),
    exists (R: Param2b0.Rel (A -> B) (A' -> B')),
      (* we would really want here to use definitional equality but it works nonetheless and def. eq. is stronger *)
      Param2b0.R _ _ R = R_arrow AR BR
  ).
Proof.
  intro Habs.
  specialize (Habs Unit Unit p44_true).
  specialize (Habs Bool Bool p2a2a_A).
  destruct Habs as [R Req].
  have g2b := Param2b0.R_in_map _ _ R.

  assert (forall f g: Unit -> Bool,
    Map2b.map (Param2b0.R (Unit -> Bool) (Unit -> Bool) R)
              (Param2b0.covariant (Unit -> Bool) (Unit -> Bool) R) f = g
  ).
  - intros f g.
    specialize (g2b f g).

    induction (inverse Req) ; clear Req.
    simpl in g2b ; unfold R_arrow, sym_rel in g2b.
    exact (g2b (fun _ _ _ => tt)).
  - set (const_true := fun (_: Unit) => true).
    set (const_false := fun (_: Unit) => false).

    specialize (X const_true const_true) as Y1.
    specialize (X const_true const_false) as Y2.
    destruct (inverse Y1).

    assert (const_true tt = const_false tt) by (rewrite Y2 ; reflexivity).
    destruct (true_ne_false X0).
Qed.

(* Thus, for m = 2b, (0, 2a) and (2b, 0) is optimal *)

Theorem D3_arrow_left_isnt_2a: not (
    forall (A A' : Type) (AR: Param02a.Rel A A'),
    forall (B B' : Type) (BR: Param30.Rel B B'),
    exists (R: Param30.Rel (A -> B) (A' -> B')),
      (* we would really want here to use definitional equality but it works nonetheless and def. eq. is stronger *)
      Param30.R _ _ R = R_arrow AR BR
  ).
Proof.
  (* Proof adapted from D2b_arrow_left_is_gt1 *)

  intro Habs.
  specialize (Habs Bool Bool p2a2a_A).
  specialize (Habs Bool Bool p44_bool).
  destruct Habs as [R Req].
  have g2a := Param2a0.map_in_R _ _ R.

  set (id := fun (x: Bool) => x).
  specialize (g2a id).
  set (transported_id := (Map2a.map
    (Param2a0.R _ _ R)
    (Param2a0.covariant _ _ R) id
  )).
  specialize (g2a transported_id).
  specialize (g2a (idpath _)).
  simpl in g2a ; unfold R_arrow in g2a.

  induction (inverse Req) ; clear Req.
  assert (forall b, b = transported_id false) by (
    intro b ;
    apply (g2a b false tt)
  ).

  destruct (transported_id false).
  - destruct (false_ne_true (X false)).
  - destruct (true_ne_false (X true)).
Qed.

Theorem D3_arrow_left_isnt_2b: not (
    forall (A A' : Type) (AR: Param02b.Rel A A'),
    forall (B B' : Type) (BR: Param30.Rel B B'),
    exists (R: Param30.Rel (A -> B) (A' -> B')),
      (* we would really want here to use definitional equality but it works nonetheless and def. eq. is stronger *)
      Param30.R _ _ R = R_arrow AR BR
  ).
Proof.
  (* Proof adapted from D2a_arrow_left_is_gt1 *)

  intro Habs.
  specialize (Habs Unit Unit p2b2b_empty_R).
  specialize (Habs Bool Bool p44_bool).
  destruct Habs as [R Req].
  have g2b := Param30.R_in_map _ _ R.
  induction (inverse Req) ; clear Req.

  assert (forall a b: Unit -> Bool,
    R_arrow p2b2b_empty_R p44_bool a b
  ) by (
    intros a b;
    unfold R_arrow;
    intros x x';
    simpl; unfold sym_rel;
    intro false ; destruct false
  ).
  
  assert (
    forall a b: Unit -> Bool,
      Map2b.map (Param2b0.R (Unit -> Bool) (Unit -> Bool) R)
                (Param2b0.covariant (Unit -> Bool) (Unit -> Bool) R) a = b
  ) by (
    intros a b ;
    apply (g2b a b) ;
    apply X
  ). clear X g2b.

  set (id_t := fun (f: Unit) => true).
  set (id_f := fun (f: Unit) => false).

  specialize (X0 id_t id_t) as Y1.
  specialize (X0 id_t id_f) as Y2.

  destruct (inverse Y2).
  assert (id_f tt = id_t tt).
  - destruct Y1.
    reflexivity.
  - destruct (false_ne_true X).
Qed.

(* -> thus, the left-side of D_arrow(3, 0) is >= 3 *)

Theorem D3_arrow_right_isnt_2a: not (
    forall (A A' : Type) (AR: Param03.Rel A A'),
    forall (B B' : Type) (BR: Param2a0.Rel B B'),
    exists (R: Param30.Rel (A -> B) (A' -> B')),
      (* we would really want here to use definitional equality but it works nonetheless and def. eq. is stronger *)
      Param30.R _ _ R = R_arrow AR BR
  ).
Proof.
  (* Proof adapted from D2b_arrow_right_is_gt1 *)

  intro Habs.
  specialize (Habs Unit Unit p44_true).
  specialize (Habs Bool Bool (Param02a_sym _ _ p2a2a_A)).
  destruct Habs as [R Req].
  have g2b := Param30.R_in_map _ _ R.

  assert (forall f g: Unit -> Bool,
    Map2b.map (Param2b0.R (Unit -> Bool) (Unit -> Bool) R)
              (Param2b0.covariant (Unit -> Bool) (Unit -> Bool) R) f = g
  ).
  - intros f g.
    specialize (g2b f g).

    induction (inverse Req) ; clear Req.
    simpl in g2b ; unfold R_arrow, sym_rel in g2b.
    exact (g2b (fun _ _ _ => tt)).
  - set (const_true := fun (_: Unit) => true).
    set (const_false := fun (_: Unit) => false).

    specialize (X const_true const_true) as Y1.
    specialize (X const_true const_false) as Y2.
    destruct (inverse Y1).

    assert (const_true tt = const_false tt) by (rewrite Y2 ; reflexivity).
    destruct (true_ne_false X0).
Qed.

Definition p2b0_empty_R: Param2b0.Rel Unit Unit.
Proof.
  exists (fun _ _ => False).
  - exists (fun b => b).
    intros ? ? f ; destruct f.
  - exists.
Defined.

Theorem D3_arrow_right_isnt_2b: not (
    forall (A A' : Type) (AR: Param03.Rel A A'),
    forall (B B' : Type) (BR: Param2b0.Rel B B'),
    exists (R: Param30.Rel (A -> B) (A' -> B')),
      (* we would really want here to use definitional equality but it works nonetheless and def. eq. is stronger *)
      Param30.R _ _ R = R_arrow AR BR
  ).
Proof.
  (* Proof adapted from D2a_arrow_right_is_gt1 *)

  intro Habs.
  specialize (Habs Unit Unit p44_true).
  specialize (Habs Unit Unit p2b2b_empty_R).
  destruct Habs as [R Req].
  have g2a := Param30.map_in_R _ _ R.
  induction (inverse Req) ; clear Req.

  set (id_t := fun (f: Unit) => tt).
  specialize (g2a id_t).
  set (transported_id_t := (Map2a.map
    (Param2a0.R _ _ R)
    (Param2a0.covariant _ _ R) id_t
  )).
  specialize (g2a transported_id_t).
  specialize (g2a (idpath _)).
  simpl in g2a ; unfold R_arrow in g2a.

  specialize (g2a tt tt tt).
  destruct g2a.
Qed.

(* -> thus, the left-side of D_arrow(3, 0) is >= 3 *)

(* Thus, for m = 3, (0, 3) and (3, 0) is optimal *)

Definition p33_not_44: Param33.Rel Unit Unit.
Proof.
  exists (fun _ _ => Bool).
  - exists (fun b => b).
    + intros ; exact true.
    + intros a b ? ; destruct a, b ; reflexivity.
  - exists (fun b => b).
    + intros ; exact true.
    + intros a b ? ; destruct a, b ; reflexivity.
Defined.

(* from https://github.com/mattam82/Coq-Equations/blob/f9f7d3cdf91bae89f255335e083e9ddd5325f8df/theories/HoTT/EqDec.v#L218 *)
Lemma is_hset {A} `{H : IsHSet A} {x y : A} (p q : x = y) : p = q.
Proof.
  apply HSet.hset_path2.
Defined.

(* TODO: Can we do it without funext? *)
Theorem D4_arrow_right_is_gt3 `{Funext}: not (
    forall (A A' : Type) (AR: Param04.Rel A A'),
    forall (B B' : Type) (BR: Param30.Rel B B'),

    (* using definitional equality *)
    IsUMap (R_arrow AR BR)
).
Proof.
  intro Habs.
  specialize (Habs Unit Unit p44_true).
  specialize (Habs Unit Unit p33_not_44).
  destruct Habs.

  unfold R_arrow in *.
  simpl in *.

  specialize (R_in_mapK id id).

  set (rf := fun _ _ _: Unit => false).
  set (rt := fun _ _ _: Unit => true).
  specialize (R_in_mapK rf) as R_in_mapKf.
  specialize (R_in_mapK rt) as R_in_mapKt.

  remember (R_in_map id id rf) as R_in_mapf eqn:R_in_mapf_eq.
  remember (R_in_map id id rt) as R_in_mapt eqn:R_in_mapt_eq.

  destruct (is_hset R_in_mapf R_in_mapt).
  destruct (inverse R_in_mapKf).

  assert (rf tt tt tt = rt tt tt tt) as Habs by (rewrite R_in_mapKt ; reflexivity).
  destruct (false_ne_true Habs).
Qed.


(* TODO: Can we do it without Univalence? *)
Theorem D4_arrow_left_is_gt3 `{Univalence} : not (
    forall (A A' : Type) (AR: Param03.Rel A A'),
    forall (B B' : Type) (BR: Param40.Rel B B'),

    (* using definitional equality *)
    IsUMap (R_arrow AR BR)
).
Proof.
move=> /(_ Unit Unit p33_not_44) /(_ Type Type (Param40_Type44 _))[]/= m g1 g2/=.
move=> /(_ (fun _ => Bool) (fun _ => Bool))/=.
move: (g1 _ _) (g2 _ _) ; rewrite /R_arrow/= => {g1 g2}.
Admitted.

(*** D_forall ***)

(* Since an arrow is a dependent product, values of D_arrow are lower bound for D_forall.
   Thus, we only have to check :
    - m = 1, left is >= (0, 2a)
    - m = 2a, left is >= (0, 4)
    - m = 4, left is >= (0, 4) *)

Definition dependently_inhabited: Bool -> Type := fun b => match b with
    | true => Unit
    | false => False
    end.

Definition p01_is_true: Param01.Rel Unit Bool.
Proof.
  exists (fun _ b => b = true).
  - exists.
  - exists.
    intro ; exact tt.
Defined.

Definition p10_dependently_inhabited (x: Unit) (x': Bool) (_: p01_is_true x x'): Param10.Rel Unit (dependently_inhabited x').
Proof.
  exists (fun _ _ => Unit).
  - exists.
    intro.
    inversion X.
    exact tt.
  - exists.
Qed.

Theorem D1_forall_left_is_gt1: not (
    forall (A A' : Type) (AR: Param01.Rel A A'),
    forall (B : A -> Type) (B' : A' -> Type)
           (BR: forall (a: A) (a': A') (aR: (rel AR) a a'), Param10.Rel (B a) (B' a')),
    exists (R: Param10.Rel (forall (a: A), B a) (forall (a': A'), B' a')),
      rel R = R_forall AR BR
).
Proof.
  intro Habs.
  specialize (Habs _ _ p01_is_true).
  specialize (Habs _ _ p10_dependently_inhabited).
  destruct Habs as [R Req].
  pose m := Param10.map _ _ R.
  destruct (m (fun f => f) false).
Defined.

(* This relation is "artificially" not a 44 because we "glue" a Bool to the relation *)
Definition p33_not_44_bool: Param33.Rel Bool Bool.
Proof.
  exists (fun b b' => Bool * (b = b')).
  - exists id.
    + intros. unfold sym_rel. destruct X. exact (true, idpath).
    + intros. unfold sym_rel in *. destruct X as [_ eq]. destruct eq.
      reflexivity.
  - exists id.
    + intros. unfold sym_rel. destruct X. exact (true, idpath).
    + intros. unfold sym_rel in *. destruct X as [_ eq]. destruct eq.
      reflexivity.
Defined.

Definition p30_dependent_relation (b: Bool) (b': Bool) (aR: (rel p33_not_44_bool) b b'): Param30.Rel Bool Bool.
Proof.
  destruct aR as [fst _].
  case fst.
  - exists (fun b b' => b = b').
    + exists (fun b => b).
      * intros; assumption.
      * intros; assumption.
    + exists.
  - exists (fun b b' => b <> b').
    + exists (fun b => negb b).
      * intros. destruct X. intro Habs.
        destruct (not_fixed_negb _ (inverse Habs)).
      * intros. apply inverse.
        apply negb_ne. intro Habs.
        destruct (X (inverse Habs)).
    + exists.
Defined.

Theorem D2a_forall_left_is_gt3: not (
    forall (A A' : Type) (AR: Param03.Rel A A'),
    forall (B : A -> Type) (B' : A' -> Type)
           (BR: forall (a: A) (a': A') (aR: (rel AR) a a'), Param2a0.Rel (B a) (B' a')),
    exists (R: Param2a0.Rel (forall (a: A), B a) (forall (a': A'), B' a')),
      (* we would really want here to use definitional equality but it works nonetheless and def. eq. is stronger *)
      Param2a0.R _ _ R = R_forall AR BR
).
Proof.
  intro Habs.
  specialize (Habs Bool Bool p33_not_44_bool).
  (* This is interesting that the proof works since B and B' are not dependent products *)
  specialize (Habs (fun b => Bool) (fun b => Bool) p30_dependent_relation).
  destruct Habs as [R Req].
  have g2a := Param2a0.map_in_R _ _ R.

  set (f := fun _: Bool => true).
  specialize (g2a f).
  set (transported_f := (Map2a.map
    (Param2a0.R _ _ R)
    (Param2a0.covariant _ _ R) f
  )).
  specialize (g2a transported_f).
  induction (inverse Req) ; clear Req.
  simpl in g2a ; unfold R_forall in g2a.

  specialize (g2a idpath).
  simpl in g2a.
  
  specialize (g2a true true (false, idpath)) as not_eq. simpl in not_eq.
  specialize (g2a true true (true, idpath)) as eq. simpl in eq.
  destruct (not_eq eq).
Qed.

(* Interestingly, this proof is basically the same as the previous theorem *)
Theorem D3_forall_left_is_gt3: not (
    forall (A A' : Type) (AR: Param03.Rel A A'),
    forall (B : A -> Type) (B' : A' -> Type)
           (BR: forall (a: A) (a': A') (aR: (rel AR) a a'), Param30.Rel (B a) (B' a')),
    exists (R: Param30.Rel (forall (a: A), B a) (forall (a': A'), B' a')),
      (* we would really want here to use definitional equality but it works nonetheless and def. eq. is stronger *)
      Param30.R _ _ R = R_forall AR BR
).
Proof.
  intro Habs.
  specialize (Habs Bool Bool p33_not_44_bool).
  specialize (Habs (fun b => Bool) (fun b => Bool) p30_dependent_relation).
  destruct Habs as [R Req].
  have g2a := Param30.map_in_R _ _ R.

  set (f := fun _: Bool => true).
  specialize (g2a f).
  set (transported_f := (Map2a.map
    (Param2a0.R _ _ R)
    (Param2a0.covariant _ _ R) f
  )).
  specialize (g2a transported_f).
  induction (inverse Req) ; clear Req.
  simpl in g2a ; unfold R_forall in g2a.

  specialize (g2a idpath).
  simpl in g2a.
  
  specialize (g2a true true (false, idpath)) as not_eq. simpl in not_eq.
  specialize (g2a true true (true, idpath)) as eq. simpl in eq.
  destruct (not_eq eq).
Qed.
