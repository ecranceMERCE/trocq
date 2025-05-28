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

From elpi Require Export elpi.

From Trocq.Elpi Extra Dependency "util.elpi" as util.
From Trocq.Elpi Extra Dependency "class.elpi" as class.
From Trocq.Elpi Extra Dependency "sort.elpi" as sort.
From Trocq.Elpi Extra Dependency "database.elpi" as database.

Elpi Db trocq.db lp:{{ }}.
Elpi Accumulate trocq.db File util.
Elpi Accumulate trocq.db File class.
Elpi Accumulate trocq.db File sort.
#[superglobal] Elpi Accumulate trocq.db File database.
