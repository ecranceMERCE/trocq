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

From elpi Require Import elpi.
Require Import ssreflect.
Require Export Database.
Require Import Hierarchy.
Require Export Param_sort Param_arrow Param_forall.

From Trocq.Elpi Extra Dependency "annot.elpi" as annot.
From Trocq.Elpi Extra Dependency "util-rocq.elpi" as util_rocq.
From Trocq.Elpi Extra Dependency "class.elpi" as class.
From Trocq.Elpi Extra Dependency "param-class-util.elpi" as param_class_util.
From Trocq.Elpi Extra Dependency "param.elpi" as param.
From Trocq.Elpi.constraints Extra Dependency "simple-graph.elpi" as simple_graph.
From Trocq.Elpi.constraints Extra Dependency "constraint-graph.elpi" as constraint_graph.
From Trocq.Elpi.constraints Extra Dependency "constraints.elpi" as constraints.
From Trocq.Elpi.constraints Extra Dependency "constraints-impl.elpi" as constraints_impl.
From Trocq.Elpi.generation Extra Dependency "pparam-type.elpi" as pparam_type_generation.
From Trocq.Elpi Extra Dependency "tactic.elpi" as tactic.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Elpi Command genpparam.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File class.

Elpi Command genpparamtype.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File class.
Elpi Accumulate File pparam_type_generation.

Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  coq.univ.alg-super U U1,
  coq.univ.variable U1 L1,
  map-class.all-of-kind low Classes1,
  % first the ones where the arguments matter
  std.forall Classes1 (m\
    std.forall Classes1 (n\
      generate-pparam-type L L1 (pc m n)
    )
  ).
}}.

Elpi Tactic trocq.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File class.
Elpi Accumulate File simple_graph.
Elpi Accumulate File constraints.
Elpi Accumulate File annot.
Elpi Accumulate File constraint_graph.
Elpi Accumulate File constraints_impl.
Elpi Accumulate File param_class_util.
Elpi Accumulate File param.
Elpi Accumulate File util_rocq.
Elpi Accumulate File tactic.

Tactic Notation "trocq" ident_list(l) := elpi trocq ltac_string_list:(l).
