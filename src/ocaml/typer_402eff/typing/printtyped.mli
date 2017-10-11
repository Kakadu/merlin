(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*             Damien Doligez, projet Para, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1999 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

open Typedtree;;
open Format;;

val interface : formatter -> signature -> unit;;
val implementation : formatter -> structure -> unit;;

val implementation_with_coercion :
    formatter -> (structure * module_coercion) -> unit;;

(* Added by merlin for debugging purposes *)
val pattern : int -> formatter -> pattern -> unit
