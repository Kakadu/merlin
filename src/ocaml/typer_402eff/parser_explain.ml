open Parser_raw
let named_item_at = function
  | 2 -> "while_lwt"
  | 58 -> "attribute"
  | 153 -> "extension"
  | 363 -> "while"
  | 365 -> "try_lwt"
  | 367 -> "try"
  | 381 -> "object"
  | 402 -> "attribute"
  | 420 -> "match_lwt"
  | 422 -> "match"
  | 434 -> "lwt"
  | 453 -> "let"
  | 454 -> "let open"
  | 473 -> "if"
  | 475 -> "function"
  | 478 -> "pattern"
  | 479 -> "when guard"
  | 480 -> "fun"
  | 502 -> "for_lwt"
  | 506 -> "for"
  | 527 -> "val"
  | 532 -> "type"
  | 534 -> "type nonrec"
  | 644 -> "open"
  | 648 -> "module"
  | 723 -> "module type"
  | 729 -> "recursive module"
  | 738 -> "extension"
  | 742 -> "attribute"
  | 746 -> "include"
  | 749 -> "external"
  | 758 -> "exception"
  | 762 -> "effect"
  | 773 -> "class"
  | 775 -> "class type"
  | 783 -> "object"
  | 945 -> "meta-let"
  | 1092 -> "for body"
  | 1096 -> "for body"
  | 1103 -> "for body"
  | 1118 -> "match action"
  | 1120 -> "match action"
  | 1127 -> "then clause"
  | 1129 -> "else clause"
  | 1148 -> "let module"
  | 1178 -> "type constraint"
  | 1180 -> "type constraint"
  | 1191 -> "type constraint"
  | 1285 -> "object"
  | 1344 -> "while body"
  | 1353 -> "while_lwt body"
  | 1356 -> "type"
  | 1357 -> "type nonrec"
  | 1390 -> "module"
  | 1394 -> "module type"
  | 1400 -> "recursive module"
  | 1406 -> "lwt"
  | 1410 -> "let"
  | 1414 -> "include"
  | 1417 -> "external"
  | 1424 -> "exception"
  | 1430 -> "effect"
  | 1439 -> "class"
  | 1440 -> "class type"
  | 1461 -> "lwt"
  | 1465 -> "let"
  | _ -> raise Not_found

let nullable (type a) : a MenhirInterpreter.nonterminal -> bool =
  let open MenhirInterpreter in function
  | N_virtual_flag -> true
  | N_type_variance -> true
  | N_type_parameters -> true
  | N_type_kind -> true
  | N_toplevel_directives -> true
  | N_structure_tail -> true
  | N_structure_head -> true
  | N_structure -> true
  | N_signature -> true
  | N_rec_flag -> true
  | N_private_virtual_flags -> true
  | N_private_flag -> true
  | N_post_item_attributes -> true
  | N_payload -> true
  | N_parent_binder -> true
  | N_override_flag -> true
  | N_optional_type_parameters -> true
  | N_opt_semi -> true
  | N_opt_default -> true
  | N_opt_bar -> true
  | N_opt_ampersand -> true
  | N_mutable_flag -> true
  | N_generalized_constructor_arguments -> true
  | N_ext_attributes -> true
  | N_constraints -> true
  | N_class_type_parameters -> true
  | N_class_structure -> true
  | N_class_sig_fields -> true
  | N_class_sig_body -> true
  | N_class_self_type -> true
  | N_class_self_pattern -> true
  | N_class_fields -> true
  | N_attributes -> true
  | _ -> false
