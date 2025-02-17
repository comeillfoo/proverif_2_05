(*************************************************************
 *                                                           *
 *  Cryptographic protocol verifier                          *
 *                                                           *
 *  Bruno Blanchet, Vincent Cheval, and Marc Sylvestre       *
 *                                                           *
 *  Copyright (C) INRIA, CNRS 2000-2023                      *
 *                                                           *
 *************************************************************)

(*

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details (in file LICENSE).

    You should have received a copy of the GNU General Public License along
    with this program; if not, write to the Free Software Foundation, Inc.,
    51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.

*)
val equal_terms_with_links : Types.term -> Types.term -> bool
val equal_facts_with_links : Types.fact -> Types.fact -> bool

val equal_closed_terms : Types.term -> Types.term -> bool

val equal_tags : Types.label -> Types.label -> bool
val equal_constra : Types.constraints -> Types.constraints -> bool

val match_terms : Types.term -> Types.term -> unit

val get_vars : Types.binder list ref -> Types.term -> unit
val has_vars : Types.term -> bool
