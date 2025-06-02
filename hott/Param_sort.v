(*****************************************************************************)
(*                            *                    Trocq                     *)
(*  _______                   *       Copyright (C) 2023 Inria & MERCE       *)
(* |__   __|                  *    (Mitsubishi Electric R&D Centre Europe)   *)
(*    | |_ __ ___   ___ __ _  *       Cyril Cohen <cyril.cohen@inria.fr>     *)
(*    | | '__/ _ \ / __/ _` | *       Enzo Crance <enzo.crance@inria.fr>     *)
(*    | | | | (_) | (_| (_| | *   Assia Mahboubi <assia.mahboubi@inria.fr>   *)
(*    |_|_|  \___/ \___\__, | ************************************************)
(*                        | | * This file is distributed under the terms of  *)
(*                        |_| * GNU Lesser General Public License Version 3  *)
(*                            * see LICENSE file for the text of the license *)
(*****************************************************************************)

Require Import ssreflect.
From elpi Require Import elpi.
Require Import Hierarchy Stdlib Database Param_lemmas.

From Trocq.Elpi Extra Dependency "class.elpi" as class.
From Trocq.Elpi.generation Extra Dependency "param-sort.elpi" as param_sort_generation.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Local Open Scope param_scope.

(* generate MapM_TypeNP@{i} :
    MapM.Has Type@{i} Type@{i} ParamNP.Rel@{i},
  for all N P, for M = map2a and below (above, NP is always 44)
  + symmetry MapM_Type_symNP *)

Elpi Command genmaptype.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File class.
Elpi Accumulate File param_sort_generation.

Elpi Query lp:{{
  map-class.all-of-kind all AllClasses,
  map-class.all-of-kind low LowClasses,
  std.forall LowClasses (m\
    std.forall AllClasses (n\
      std.forall AllClasses (p\
        generate-map-sort ttype m (pc n p)
      )
    )
  ).
}}.

(* now R is always Param44.Rel *)

(* NB: here we would like to use i+1 instead of j but Rocq does not allow it
 * Map*.Has is a constant so it currently cannot be instantiated with an algebraic universe
 *)

Definition Map2b_Type44@{i j | i < j} `{Univalence} :
  @Map2b.Has@{j} Type@{i} Type@{i} Param44.Rel@{i}.
Proof.
  unshelve econstructor.
  - exact idmap.
  - move=> A B /uparam_equiv. apply: path_universe_uncurried.
Defined.

Definition Map2b_Type_sym44@{i j | i < j} `{Univalence} :
  @Map2b.Has@{j} Type@{i} Type@{i} (sym_rel@{j} Param44.Rel@{i}).
Proof.
  unshelve econstructor.
  - exact idmap.
  - move=> A B /uparam_equiv /path_universe_uncurried /inverse. exact.
Defined.

Definition Map3_Type44@{i j | i < j} `{Univalence} :
  @Map3.Has@{j} Type@{i} Type@{i} Param44.Rel@{i}.
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e # id_Param44 A).
  - move=> A B /uparam_equiv. apply: path_universe_uncurried.
Defined.

Definition Map3_Type_sym44@{i j | i < j} `{Univalence} :
  @Map3.Has@{j} Type@{i} Type@{i} (sym_rel@{j} Param44.Rel@{i}).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e # id_Param44 A).
  - move=> A B /uparam_equiv /path_universe_uncurried /inverse. exact.
Defined.

Definition Map4_Type44@{i j | i < j} `{Univalence} :
  @Map4.Has@{j} Type@{i} Type@{i} Param44.Rel@{i}.
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e # id_Param44 A).
  - move=> A B /uparam_equiv. apply: path_universe_uncurried.
  - move=> A B; elim/uparam_induction.
    by rewrite uparam_equiv_id /= [path_universe_uncurried _] path_universe_1.
Defined.

Definition Map4_Type_sym44@{i j | i < j} `{Univalence} :
  @Map4.Has@{j} Type@{i} Type@{i} (sym_rel@{j} Param44.Rel@{i}).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e # id_Param44 A).
  - move=> A B /uparam_equiv /path_universe_uncurried /inverse. exact.
  - move=> A B; elim/uparam_induction.
    by rewrite uparam_equiv_id /= [path_universe_uncurried _] path_universe_1.
Defined.

Register Map2b_Type44 as trocq.map2b_type44.
Register Map2b_Type_sym44 as trocq.map2b_type_sym44.
Register Map3_Type44 as trocq.map3_type44.
Register Map3_Type_sym44 as trocq.map3_type_sym44.
Register Map4_Type44 as trocq.map4_type44.
Register Map4_Type_sym44 as trocq.map4_type_sym44.

Elpi Query lp:{{
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (
    trocq.db.map-sort ttype map2b (pc map4 map4) {{:gref lib:trocq.map2b_type44}}
  )),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (
    trocq.db.map-sym-sort ttype map2b (pc map4 map4) {{:gref lib:trocq.map2b_type_sym44}}
  )),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (
    trocq.db.map-sort ttype map3 (pc map4 map4) {{:gref lib:trocq.map3_type44}}
  )),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (
    trocq.db.map-sym-sort ttype map3 (pc map4 map4) {{:gref lib:trocq.map3_type_sym44}}
  )),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (
    trocq.db.map-sort ttype map4 (pc map4 map4) {{:gref lib:trocq.map4_type44}}
  )),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (
    trocq.db.map-sym-sort ttype map4 (pc map4 map4) {{:gref lib:trocq.map4_type_sym44}}
  )).
}}.

Elpi Command genparamtype.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File class.
Elpi Accumulate File param_sort_generation.

Elpi Query lp:{{
  map-class.all-of-kind all AllClasses,
  map-class.all-of-kind low LowClasses,
  map-class.all-of-kind high HighClasses,
  std.forall LowClasses (m\
    std.forall LowClasses (n\
      std.forall AllClasses (p\
        std.forall AllClasses (q\
          generate-param-sort ttype (pc m n) (pc p q)
        )
      )
    ),
    std.forall HighClasses (n\
      generate-param-sort ttype (pc m n) (pc map4 map4)
    )
  ),
  std.forall HighClasses (m\
    std.forall AllClasses (n\
      generate-param-sort ttype (pc m n) (pc map4 map4)
    )
  ).
}}.

