
type token = 
  | WITH
  | WHILE_LWT
  | WHILE
  | WHEN
  | VIRTUAL
  | VAL
  | UNDERSCORE
  | UIDENT of (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 14 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | TYPE
  | TRY_LWT
  | TRY
  | TRUE
  | TO
  | TILDE
  | THEN
  | STRUCT
  | STRING of (
# 402 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string * string option)
# 27 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | STAR
  | SIG
  | SHARPOP of (
# 399 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 34 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | SHARP
  | SEMISEMI
  | SEMI
  | RPAREN
  | REC
  | RBRACKET
  | RBRACE
  | QUOTE
  | QUESTIONQUESTION
  | QUESTION
  | PRIVATE
  | PREFIXOP of (
# 387 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 50 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | PLUSEQ
  | PLUSDOT
  | PLUS
  | PERCENT
  | OR
  | OPTLABEL of (
# 381 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 60 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | OPEN
  | OF
  | OBJECT
  | NONREC
  | NEW
  | NATIVEINT of (
# 376 "src/ocaml/typer/preprocess/parser_raw.mly"
       (nativeint)
# 70 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | MUTABLE
  | MODULE
  | MINUSGREATER
  | MINUSDOT
  | MINUS
  | METHOD
  | MATCH_LWT
  | MATCH
  | LPAREN
  | LIDENT of (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 84 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | LET_LWT
  | LETOP of (
# 429 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 90 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | LET
  | LESSMINUS
  | LESS
  | LBRACKETPERCENTPERCENT
  | LBRACKETPERCENT
  | LBRACKETLESS
  | LBRACKETGREATER
  | LBRACKETBAR
  | LBRACKETATATAT
  | LBRACKETATAT
  | LBRACKETAT
  | LBRACKET
  | LBRACELESS
  | LBRACE
  | LAZY
  | LABEL of (
# 351 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 110 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | INT64 of (
# 350 "src/ocaml/typer/preprocess/parser_raw.mly"
       (int64)
# 115 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | INT32 of (
# 349 "src/ocaml/typer/preprocess/parser_raw.mly"
       (int32)
# 120 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | INT of (
# 348 "src/ocaml/typer/preprocess/parser_raw.mly"
       (int)
# 125 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | INITIALIZER
  | INHERIT
  | INFIXOP4 of (
# 345 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 132 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | INFIXOP3 of (
# 344 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 137 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | INFIXOP2 of (
# 343 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 142 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | INFIXOP1 of (
# 342 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 147 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | INFIXOP0 of (
# 341 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 152 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | INCLUDE
  | IN
  | IF
  | GREATERRBRACKET
  | GREATERRBRACE
  | GREATERDOT
  | GREATER
  | FUNCTOR
  | FUNCTION
  | FUN
  | FOR_LWT
  | FOR
  | FLOAT of (
# 330 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 169 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | FINALLY_LWT
  | FALSE
  | EXTERNAL
  | EXCEPTION
  | EQUAL
  | EOL
  | EOF
  | END
  | ELSE
  | DOWNTO
  | DOTTILDE
  | DOTLESS
  | DOTDOT
  | DOT
  | DONE
  | DO
  | CONSTRAINT
  | COMMENT of (
# 417 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string * Location.t)
# 191 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | COMMA
  | COLONGREATER
  | COLONEQUAL
  | COLONCOLON
  | COLON
  | CLASS
  | CHAR of (
# 310 "src/ocaml/typer/preprocess/parser_raw.mly"
       (char)
# 202 "src/ocaml/typer/preprocess/parser_raw.ml"
)
  | BEGIN
  | BARRBRACKET
  | BARBAR
  | BAR
  | BANG
  | BACKQUOTE
  | ASSERT
  | AS
  | AND
  | AMPERSAND
  | AMPERAMPER

# 1 "src/ocaml/typer/preprocess/parser_raw.mly"
  
open Asttypes
open Longident
open Parsetree
open Ast_helper
let rloc loc_start loc_end =
  { Location. loc_start; loc_end; loc_ghost = false; }
let gloc loc_start loc_end =
  { Location. loc_start; loc_end; loc_ghost = true; }
let mkloc =
  Location.mkloc
let mktyp startpos endpos d = Typ.mk ~loc:(rloc startpos endpos) d
let mkpat startpos endpos d = Pat.mk ~loc:(rloc startpos endpos) d
let mkexp startpos endpos d = Exp.mk ~loc:(rloc startpos endpos) d
let mkmty startpos endpos d = Mty.mk ~loc:(rloc startpos endpos) d
let mksig startpos endpos d = [Sig.mk ~loc:(rloc startpos endpos) d]
let mkmod startpos endpos d = Mod.mk ~loc:(rloc startpos endpos) d
let mkstr startpos endpos d = [Str.mk ~loc:(rloc startpos endpos) d]
let ghstr startpos endpos d = [Str.mk ~loc:(gloc startpos endpos) d]
let mkclass startpos endpos d = Cl.mk ~loc:(rloc startpos endpos) d
let mkcty startpos endpos d = Cty.mk ~loc:(rloc startpos endpos) d
let mkctf startpos endpos ?attrs d = Ctf.mk ~loc:(rloc startpos endpos) ?attrs d
let mkcf startpos endpos ?attrs d = [Cf.mk ~loc:(rloc startpos endpos) ?attrs d]
let mkrhs startpos endpos rhs = mkloc rhs (rloc startpos endpos)
let mkoption d =
  let loc = {d.ptyp_loc with Location. loc_ghost = true} in
  Typ.mk ~loc (Ptyp_constr(mkloc (Ldot (Lident "*predef*", "option")) loc,[d]))
let reloc_pat startpos endpos x= { x with ppat_loc = rloc startpos endpos };;
let reloc_exp startpos endpos x= { x with pexp_loc = rloc startpos endpos };;
let merloc startpos ?endpos x =
  let endpos = match endpos with
    | None -> x.pexp_loc.Location.loc_end
    | Some endpos -> endpos
  in
  let str = mkloc "merlin.loc" (rloc startpos endpos) in
  { x with pexp_attributes = (str , PStr []) :: x.pexp_attributes }
let mkoperator startpos endpos name =
  let loc = rloc startpos endpos in
  Exp.mk ~loc (Pexp_ident(mkloc (Lident name) loc))
let mkpatvar startpos endpos name =
  Pat.mk ~loc:(rloc startpos endpos) (Ppat_var (mkrhs startpos endpos name))
(*
  Ghost expressions and patterns:
  expressions and patterns that do not appear explicitly in the
  source file they have the loc_ghost flag set to true.
  Then the profiler will not try to instrument them and the
  -annot option will not try to display their type.
  Every grammar rule that generates an element with a location must
  make at most one non-ghost element, the topmost one.
  How to tell whether your location must be ghost:
  A location corresponds to a range of characters in the source file.
  If the location contains a piece of code that is syntactically
  valid (according to the documentation), and corresponds to the
  AST node, then the location must be real; in all other cases,
  it must be ghost.
*)
let ghexp startpos endpos d = Exp.mk ~loc:(gloc startpos endpos) d
let ghpat startpos endpos d = Pat.mk ~loc:(gloc startpos endpos) d
let ghtyp startpos endpos d = Typ.mk ~loc:(gloc startpos endpos) d
let ghloc startpos endpos d = { txt = d; loc = gloc startpos endpos }
let mkinfix startpos endpos arg1 startpos2 endpos2 name arg2 =
  mkexp startpos endpos
    (Pexp_apply(mkoperator startpos2 endpos2 name, ["", arg1; "", arg2]))
let neg_float_string f =
  if String.length f > 0 && f.[0] = '-'
  then String.sub f 1 (String.length f - 1)
  else "-" ^ f
let mkuminus startpos endpos name arg =
  match name, arg.pexp_desc with
  | "-", Pexp_constant(Const_int n) ->
      mkexp startpos endpos (Pexp_constant(Const_int(-n)))
  | "-", Pexp_constant(Const_int32 n) ->
      mkexp startpos endpos (Pexp_constant(Const_int32(Int32.neg n)))
  | "-", Pexp_constant(Const_int64 n) ->
      mkexp startpos endpos (Pexp_constant(Const_int64(Int64.neg n)))
  | "-", Pexp_constant(Const_nativeint n) ->
      mkexp startpos endpos (Pexp_constant(Const_nativeint(Nativeint.neg n)))
  | ("-" | "-."), Pexp_constant(Const_float f) ->
      mkexp startpos endpos (Pexp_constant(Const_float(neg_float_string f)))
  | _ ->
      mkexp startpos endpos (Pexp_apply(mkoperator startpos endpos ("~" ^ name), ["", arg]))
let mkuplus startpos endpos name arg =
  let desc = arg.pexp_desc in
  match name, desc with
  | "+", Pexp_constant(Const_int _)
  | "+", Pexp_constant(Const_int32 _)
  | "+", Pexp_constant(Const_int64 _)
  | "+", Pexp_constant(Const_nativeint _)
  | ("+" | "+."), Pexp_constant(Const_float _) -> mkexp startpos endpos desc
  | _ ->
      mkexp startpos endpos (Pexp_apply(mkoperator startpos endpos ("~" ^ name), ["", arg]))
let mkexp_cons consloc args loc =
  Exp.mk ~loc (Pexp_construct(mkloc (Lident "::") consloc, Some args))
let mkpat_cons consloc args loc =
  Pat.mk ~loc (Ppat_construct(mkloc (Lident "::") consloc, Some args))
let rec mktailexp startpos endpos = function
    [] ->
      let loc = gloc startpos endpos in
      let nil = { txt = Lident "[]"; loc = loc } in
      Exp.mk ~loc (Pexp_construct (nil, None))
  | e1 :: el ->
      let open Location in
      let exp_el = mktailexp e1.pexp_loc.loc_end endpos el in
      let loc = gloc e1.pexp_loc.loc_start exp_el.pexp_loc.loc_end in
      let arg = Exp.mk ~loc (Pexp_tuple [e1; exp_el]) in
      mkexp_cons loc arg loc
let rec mktailpat startpos endpos = function
    [] ->
      let loc = gloc startpos endpos in
      let nil = { txt = Lident "[]"; loc = loc } in
      Pat.mk ~loc (Ppat_construct (nil, None))
  | p1 :: pl ->
      let open Location in
      let pat_pl = mktailpat p1.ppat_loc.loc_end endpos pl in
      let loc = gloc p1.ppat_loc.loc_start pat_pl.ppat_loc.loc_end in
      let arg = Pat.mk ~loc (Ppat_tuple [p1; pat_pl]) in
      mkpat_cons loc arg loc
let mkstrexp e attrs =
  { pstr_desc = Pstr_eval (e, attrs); pstr_loc = e.pexp_loc }
let mkexp_constraint startpos endpos e (t1, t2) =
  match t1, t2 with
  | Some t, None -> mkexp startpos endpos (Pexp_constraint(e, t))
  | _, Some t -> mkexp startpos endpos (Pexp_coerce(e, t1, t))
  | None, None -> e
let array_function startpos endpos str name =
  ghloc startpos endpos
    (Ldot(Lident str, (if !Clflags.fast then "unsafe_" ^ name else name)))
let raise_error = Msupport.raise_error
let syntax_error startpos endpos =
  raise_error (Syntaxerr.Escape_error (rloc startpos endpos))
let unclosed opening_name opstart opend closing_name clstart clend =
  raise_error
    Syntaxerr.(Error (Unclosed (rloc opstart opend, opening_name,
                                rloc clstart clend, closing_name)))
let expecting startpos endpos nonterm =
  raise_error
    Syntaxerr.(Error (Expecting (rloc startpos endpos, nonterm)))
let not_expecting startpos endpos nonterm =
  raise_error
    Syntaxerr.(Error (Not_expecting (rloc startpos endpos, nonterm)))
let bigarray_function startpos endpos str name =
  ghloc startpos endpos (Ldot(Ldot(Lident "Bigarray", str), name))
let bigarray_untuplify = function
    { pexp_desc = Pexp_tuple explist; pexp_loc = _ } -> explist
  | exp -> [exp]
let bigarray_get (startpos,endpos) (startop,endop) arr arg =
  let get = if !Clflags.fast then "unsafe_get" else "get" in
  let ghexp = ghexp startop endop in
  let mkexp = mkexp startpos endpos in
  let bigarray_function = bigarray_function startop endop in
  match bigarray_untuplify arg with
    [c1] ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Array1" get)),
                       ["", arr; "", c1]))
  | [c1;c2] ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Array2" get)),
                       ["", arr; "", c1; "", c2]))
  | [c1;c2;c3] ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Array3" get)),
                       ["", arr; "", c1; "", c2; "", c3]))
  | coords ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Genarray" "get")),
                       ["", arr; "", ghexp(Pexp_array coords)]))
let bigarray_set (startpos,endpos) (startop,endop) arr arg newval =
  let set = if !Clflags.fast then "unsafe_set" else "set" in
  let ghexp = ghexp startop endop in
  let mkexp = mkexp startpos endpos in
  let bigarray_function = bigarray_function startop endop in
  match bigarray_untuplify arg with
    [c1] ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Array1" set)),
                       ["", arr; "", c1; "", newval]))
  | [c1;c2] ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Array2" set)),
                       ["", arr; "", c1; "", c2; "", newval]))
  | [c1;c2;c3] ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Array3" set)),
                       ["", arr; "", c1; "", c2; "", c3; "", newval]))
  | coords ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Genarray" "set")),
                       ["", arr;
                        "", ghexp(Pexp_array coords);
                        "", newval]))
let lapply startpos endpos p1 p2 =
  if not !Clflags.applicative_functors then
    raise_error Syntaxerr.(Error(Applicative_path(rloc startpos endpos)));
  Lapply(p1, p2)
let exp_of_label startpos endpos lbl =
  mkexp startpos endpos (Pexp_ident(mkrhs startpos endpos (Lident(Longident.last lbl))))
let pat_of_label startpos endpos lbl =
  mkpat startpos endpos (Ppat_var (mkrhs startpos endpos (Longident.last lbl)))
let check_variable vl loc v =
  if List.mem v vl then
    raise_error Syntaxerr.(Error(Variable_in_scope(loc,v)))
let varify_constructors var_names t =
  let rec loop t =
    let desc =
      match t.ptyp_desc with
      | Ptyp_any -> Ptyp_any
      | Ptyp_var x ->
          check_variable var_names t.ptyp_loc x;
          Ptyp_var x
      | Ptyp_arrow (label,core_type1,core_type2) ->
          Ptyp_arrow(label, loop core_type1, loop core_type2)
      | Ptyp_tuple lst -> Ptyp_tuple (List.map loop lst)
      | Ptyp_constr( { txt = Lident s }, []) when List.mem s var_names ->
          Ptyp_var s
      | Ptyp_constr(longident, lst) ->
          Ptyp_constr(longident, List.map loop lst)
      | Ptyp_object (lst, o) ->
          Ptyp_object (List.map (fun (s, attrs, t) -> (s, attrs, loop t)) lst, o)
      | Ptyp_class (longident, lst) ->
          Ptyp_class (longident, List.map loop lst)
      | Ptyp_alias(core_type, string) ->
          check_variable var_names t.ptyp_loc string;
          Ptyp_alias(loop core_type, string)
      | Ptyp_variant(row_field_list, flag, lbl_lst_option) ->
          Ptyp_variant(List.map loop_row_field row_field_list,
                       flag, lbl_lst_option)
      | Ptyp_poly(string_lst, core_type) ->
          List.iter (check_variable var_names t.ptyp_loc) string_lst;
          Ptyp_poly(string_lst, loop core_type)
      | Ptyp_package(longident,lst) ->
          Ptyp_package(longident,List.map (fun (n,typ) -> (n,loop typ) ) lst)
      | Ptyp_extension (s, arg) ->
          Ptyp_extension (s, arg)
    in
    {t with ptyp_desc = desc}
  and loop_row_field =
    function
      | Rtag(label,attrs,flag,lst) ->
          Rtag(label,attrs,flag,List.map loop lst)
      | Rinherit t ->
          Rinherit (loop t)
  in
  loop t
let wrap_type_annotation startpos endpos newtypes core_type body =
  let mkexp = mkexp startpos endpos in
  let ghtyp = ghtyp startpos endpos in
  let exp = mkexp(Pexp_constraint(body,core_type)) in
  let exp =
    List.fold_right (fun newtype exp -> mkexp (Pexp_newtype (newtype, exp)))
      newtypes exp
  in
  (exp, ghtyp (Ptyp_poly(newtypes,varify_constructors newtypes core_type)))
let wrap_exp_attrs startpos endpos body (ext, attrs) =
  (* todo: keep exact location for the entire attribute *)
  let body = {body with pexp_attributes = attrs @ body.pexp_attributes} in
  match ext with
  | None -> body
  | Some id -> ghexp startpos endpos (Pexp_extension (id, PStr [mkstrexp body []]))
let mkexp_attrs startpos endpos d attrs =
  wrap_exp_attrs startpos endpos (mkexp startpos endpos d) attrs
let fake_tydecl tydecl = tydecl.ptype_name, tydecl
let fake_untydecl (ptype_name,tydecl) = {tydecl with ptype_name}
let tag_nonrec loc (id, a) =
  let attr = ({ txt = "nonrec"; loc }, PStr []) in
  {a with ptype_attributes = attr :: a.ptype_attributes}
let fake_vb_app f vb = {vb with pvb_expr = Fake.app f vb.pvb_expr}
let let_operator startpos endpos op bindings cont =
  let pat, expr =
    match bindings with
    | [] -> assert false
    | [x] -> (x.pvb_pat,x.pvb_expr)
    | l ->
      let pats, exprs =
        List.fold_right
          (fun {pvb_pat=p;pvb_expr=e} (ps,es) -> (p::ps,e::es)) l ([],[]) in
      ghpat startpos endpos (Ppat_tuple pats),
      ghexp startpos endpos (Pexp_tuple exprs)
  in
  let f = ghexp startpos endpos (Pexp_fun("", None, pat, cont)) in
  mkexp startpos endpos (Pexp_apply(op, [("", expr); ("", f)]))

# 491 "src/ocaml/typer/preprocess/parser_raw.ml"

let menhir_begin_marker =
  0

and (xv_with_type_binder, xv_with_constraints, xv_with_constraint, xv_virtual_flag, xv_value_type, xv_value, xv_val_longident, xv_val_ident, xv_typevar_list, xv_type_variance, xv_type_variable, xv_type_parameters, xv_type_parameter_list, xv_type_parameter, xv_type_longident, xv_type_kind, xv_type_declarations, xv_type_declaration, xv_type_constraint, xv_toplevel_directives, xv_tag_field, xv_subtractive, xv_structure_tail, xv_structure_item, xv_structure_head, xv_structure, xv_strict_binding, xv_str_type_extension, xv_str_extension_constructors, xv_str_exception_declaration, xv_single_attr_id, xv_simple_pattern_not_ident, xv_simple_pattern, xv_simple_labeled_expr_list, xv_simple_expr, xv_simple_core_type_or_tuple_no_attr, xv_simple_core_type_or_tuple, xv_simple_core_type_no_attr, xv_simple_core_type2, xv_simple_core_type, xv_signed_constant, xv_signature_item, xv_signature, xv_sig_type_extension, xv_sig_extension_constructors, xv_sig_exception_declaration, xv_seq_expr, xv_row_field_list, xv_row_field, xv_record_expr, xv_rec_module_declarations, xv_rec_flag, xv_private_virtual_flags, xv_private_flag, xv_primitive_declaration, xv_post_item_attributes, xv_post_item_attribute, xv_poly_type_no_attr, xv_poly_type, xv_payload, xv_pattern_var, xv_pattern_semi_list, xv_pattern_comma_list, xv_pattern, xv_parse_expression, xv_parent_binder, xv_package_type_cstrs, xv_package_type_cstr, xv_package_type, xv_override_flag, xv_optional_type_variable, xv_optional_type_parameters, xv_optional_type_parameter_list, xv_optional_type_parameter, xv_opt_semi, xv_opt_default, xv_opt_bar, xv_opt_ampersand, xv_operator, xv_open_statement, xv_newtype, xv_name_tag_list, xv_name_tag, xv_mutable_flag, xv_mty_longident, xv_module_type, xv_module_rec_declaration, xv_module_expr, xv_module_declaration, xv_module_bindings, xv_module_binding_body, xv_module_binding, xv_mod_longident, xv_mod_ext_longident, xv_method_, xv_meth_list, xv_match_cases, xv_match_case, xv_lident_list, xv_let_pattern, xv_let_operator, xv_let_bindings_no_attrs, xv_let_bindings, xv_let_binding_, xv_let_binding, xv_lbl_pattern_list, xv_lbl_pattern, xv_lbl_expr_list, xv_lbl_expr, xv_labeled_simple_pattern, xv_labeled_simple_expr, xv_label_var, xv_label_longident, xv_label_let_pattern, xv_label_ident, xv_label_expr, xv_label_declarations, xv_label_declaration, xv_label, xv_item_extension, xv_interface, xv_implementation, xv_ident, xv_generalized_constructor_arguments, xv_functor_args, xv_functor_arg_name, xv_functor_arg, xv_fun_def, xv_fun_binding, xv_floating_attribute, xv_field_expr_list, xv_field, xv_extension_constructor_rebind, xv_extension_constructor_declaration, xv_extension, xv_ext_attributes, xv_expr_semi_list, xv_expr_open, xv_expr_comma_list, xv_expr, xv_direction_flag, xv_core_type_no_attr, xv_core_type_list_no_attr, xv_core_type_list, xv_core_type_comma_list, xv_core_type2, xv_core_type, xv_constructor_declarations, xv_constructor_declaration, xv_constraints, xv_constrain_field, xv_constrain, xv_constr_longident, xv_constr_ident, xv_constant, xv_clty_longident, xv_class_type_parameters, xv_class_type_declarations, xv_class_type_declaration, xv_class_type, xv_class_structure, xv_class_simple_expr, xv_class_signature, xv_class_sig_fields, xv_class_sig_field, xv_class_sig_body, xv_class_self_type, xv_class_self_pattern, xv_class_longident, xv_class_fun_def, xv_class_fun_binding, xv_class_fields, xv_class_field, xv_class_expr, xv_class_descriptions, xv_class_description, xv_class_declarations, xv_class_declaration, xv_attributes, xv_attribute, xv_attr_id, xv_amper_type_list, xv_additive) =
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1641 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Private )
# 501 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_with_type_binder) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1639 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Public )
# 507 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_with_type_binder) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_with_constraint) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_with_constraints) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1616 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 @ _1 )
# 513 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_with_constraints) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_with_constraint) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1614 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 519 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_with_constraints) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_mod_ext_longident) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 524 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1636 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [Pwith_modsubst (mkrhs _startpos__2_ _endpos__2_ _2, mkrhs _startpos__4_ _endpos__4_ _4)] )
# 529 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_with_constraint) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_mod_ext_longident) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_mod_longident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1634 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [Pwith_module (mkrhs _startpos__2_ _endpos__2_ _2, mkrhs _startpos__4_ _endpos__4_ _4)] )
# 535 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_with_constraint) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_core_type_no_attr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_type_parameters) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1628 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [Pwith_typesubst
          (Type.mk (mkrhs _startpos__3_ _endpos__3_ _3)
             ~params:_2
             ~manifest:_5
             ~loc:(rloc _startpos _endpos))] )
# 545 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_with_constraint) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_constraints) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_core_type_no_attr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_with_type_binder) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label_longident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_type_parameters) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1619 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [Pwith_type
          (mkrhs _startpos__3_ _endpos__3_ _3,
           (Type.mk (mkrhs _startpos__3_ _endpos__3_ (Longident.last _3))
              ~params:_2
              ~cstrs:(List.rev _6)
              ~manifest:_5
              ~priv:_4
              ~loc:(rloc _startpos _endpos)))] )
# 558 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_with_constraint) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2019 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Virtual )
# 564 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_virtual_flag) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 2017 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Concrete )
# 570 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_virtual_flag) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_core_type) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_label) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 914 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1, Immutable, Concrete, _3 )
# 576 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_value_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_core_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_virtual_flag) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 912 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3, Mutable, _2, _5 )
# 582 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_value_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_core_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_mutable_flag) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 910 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3, _2, Virtual, _5 )
# 588 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_value_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_seq_expr) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_type_constraint) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_mutable_flag) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_override_flag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 837 "src/ocaml/typer/preprocess/parser_raw.mly"
    (
       let e = mkexp_constraint _startpos _endpos _6 _4 in
       mkrhs _startpos__3_ _endpos__3_ _3, _2, Cfk_concrete (_1, e)
      )
# 597 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_value) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_seq_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_mutable_flag) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_override_flag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 835 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkrhs _startpos__3_ _endpos__3_ _3, _2, Cfk_concrete (_1, _5) )
# 603 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_value) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_core_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_mutable_flag) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 833 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkrhs _startpos__3_ _endpos__3_ _3, _2, Cfk_virtual _5 )
# 609 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_value) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_core_type) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_label) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_override_flag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 830 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( if _1 = Override then syntax_error _startpos _endpos;
        mkloc _4 (rloc _startpos__4_ _endpos__4_), Mutable, Cfk_virtual _6 )
# 616 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_value) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_val_ident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1942 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Ldot(_1, _3) )
# 622 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_val_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_val_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1940 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Lident _1 )
# 628 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_val_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_operator) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1871 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 634 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_val_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 639 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1869 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 644 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_val_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_ident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_typevar_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1647 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 650 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_typevar_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_ident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1645 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_2] )
# 656 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_typevar_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1516 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Contravariant )
# 662 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_variance) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1514 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Covariant )
# 668 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_variance) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 1512 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Invariant )
# 674 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_variance) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_ident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1519 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_var _2) )
# 680 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_variable) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_type_parameter_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1506 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( List.rev _2 )
# 686 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_parameters) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_type_parameter) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1504 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 692 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_parameters) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 1502 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [] )
# 698 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_parameters) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_type_parameter) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_type_parameter_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1524 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 704 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_parameter_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_type_parameter) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1522 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 710 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_parameter_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_type_variable) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_type_variance) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1509 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2, _1 )
# 716 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_parameter) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 721 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_ext_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1963 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Ldot(_1, _3) )
# 726 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 731 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1961 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Lident _1 )
# 736 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_core_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1479 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (Ptype_open, Public, Some _2) )
# 742 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_kind) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1477 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (Ptype_open, Public, None) )
# 748 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_kind) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_8 : unit) (_startpos__8_ : Lexing.position) (_endpos__8_ : Lexing.position) (_startofs__8_ : int) (_endofs__8_ : int) (_7 : 'tv_opt_semi) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : 'tv_label_declarations) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_private_flag) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_core_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1475 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (Ptype_record(List.rev _6), _4, Some _2) )
# 754 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_kind) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_constructor_declarations) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_opt_bar) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_private_flag) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_core_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1473 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (Ptype_variant(List.rev _6), _4, Some _2) )
# 760 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_kind) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_opt_semi) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_label_declarations) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_private_flag) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1471 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (Ptype_record(List.rev _4), _2, None) )
# 766 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_kind) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_constructor_declarations) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_private_flag) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1469 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (Ptype_variant(List.rev _4), _2, None) )
# 772 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_kind) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_constructor_declarations) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1467 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (Ptype_variant(List.rev _3), Private, None) )
# 778 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_kind) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_constructor_declarations) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1465 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (Ptype_variant(List.rev _2), Public, None) )
# 784 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_kind) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_core_type) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1463 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (Ptype_abstract, Private, Some _3) )
# 790 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_kind) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_core_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1461 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (Ptype_abstract, Public, Some _2) )
# 796 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_kind) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 1459 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (Ptype_abstract, Public, None) )
# 802 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_kind) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_type_declaration) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_type_declarations) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1444 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 808 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_declarations) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_type_declaration) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1442 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 814 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_declarations) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_post_item_attributes) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_constraints) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_type_kind) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 819 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_optional_type_parameters) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1447 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (kind, priv, manifest) = _3 in
        Type.mk (mkrhs _startpos__2_ _endpos__2_ _2)
          ~params:_1 ~cstrs:(List.rev _4)
          ~kind ~priv ?manifest ~attrs:_5 ~loc:(rloc _startpos _endpos)
       )
# 828 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_core_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1334 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (None, Some _2) )
# 834 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_constraint) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_core_type) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_core_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1331 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (Some _2, Some _4) )
# 840 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_constraint) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_core_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1328 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (Some _2, None) )
# 846 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_type_constraint) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_ident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_toplevel_directives) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2303 "src/ocaml/typer/preprocess/parser_raw.mly"
                                         ( () )
# 852 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_toplevel_directives) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_ident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_toplevel_directives) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2302 "src/ocaml/typer/preprocess/parser_raw.mly"
                                          ( () )
# 858 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_toplevel_directives) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_val_longident) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_ident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_toplevel_directives) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2301 "src/ocaml/typer/preprocess/parser_raw.mly"
                                                  ( () )
# 864 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_toplevel_directives) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : (
# 348 "src/ocaml/typer/preprocess/parser_raw.mly"
       (int)
# 869 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_ident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_toplevel_directives) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2300 "src/ocaml/typer/preprocess/parser_raw.mly"
                                        ( () )
# 874 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_toplevel_directives) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : (
# 402 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string * string option)
# 879 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_ident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_toplevel_directives) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2299 "src/ocaml/typer/preprocess/parser_raw.mly"
                                           ( () )
# 884 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_toplevel_directives) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_ident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_toplevel_directives) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2298 "src/ocaml/typer/preprocess/parser_raw.mly"
                                    ( () )
# 890 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_toplevel_directives) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 2297 "src/ocaml/typer/preprocess/parser_raw.mly"
                ( () )
# 896 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_toplevel_directives) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_name_tag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1768 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Rtag (_1, _2, true, []) )
# 902 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_tag_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_attributes) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_amper_type_list) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_opt_ampersand) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_name_tag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1766 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Rtag (_1, _5, _3, List.rev _4) )
# 908 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_tag_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2050 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "-." )
# 914 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_subtractive) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2048 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "-" )
# 920 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_subtractive) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_structure_tail) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_structure_item) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 574 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 @ _2 )
# 926 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_tail) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_structure_head) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 572 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 932 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_tail) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 570 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [] )
# 938 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_tail) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_floating_attribute) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 627 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstr _startpos _endpos (Pstr_attribute _1) )
# 944 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_post_item_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_item_extension) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 625 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstr _startpos _endpos (Pstr_extension (_1, _2)) )
# 950 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_post_item_attributes) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_module_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 622 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstr _startpos _endpos (Pstr_include (Incl.mk _2 ~attrs:_3
                                             ~loc:(rloc _startpos _endpos))) )
# 957 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_class_type_declarations) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 620 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstr _startpos _endpos (Pstr_class_type (List.rev _3)) )
# 963 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_class_declarations) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 618 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstr _startpos _endpos (Pstr_class (List.rev _2)) )
# 969 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_open_statement) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 616 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstr _startpos _endpos (Pstr_open _1) )
# 975 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_post_item_attributes) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_module_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_ident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 613 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstr _startpos _endpos (Pstr_modtype (Mtd.mk (mkrhs _startpos__3_ _endpos__3_ _3)
                              ~typ:_5 ~attrs:_6 ~loc:(rloc _startpos _endpos))) )
# 982 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_post_item_attributes) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_ident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 610 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstr _startpos _endpos (Pstr_modtype (Mtd.mk (mkrhs _startpos__3_ _endpos__3_ _3)
                              ~attrs:_4 ~loc:(rloc _startpos _endpos))) )
# 989 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_module_bindings) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 608 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstr _startpos _endpos (Pstr_recmodule(List.rev _3)) )
# 995 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_module_binding) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 606 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstr _startpos _endpos (Pstr_module _2) )
# 1001 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_str_exception_declaration) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 604 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstr _startpos _endpos (Pstr_exception _2) )
# 1007 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_str_type_extension) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 602 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstr _startpos _endpos (Pstr_typext _2) )
# 1013 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (decls : 'tv_type_declarations) (_startpos_decls_ : Lexing.position) (_endpos_decls_ : Lexing.position) (_startofs_decls_ : int) (_endofs_decls_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 600 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstr _startpos _endpos (Pstr_type (List.rev decls) ) )
# 1019 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_7 : 'tv_post_item_attributes) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : 'tv_primitive_declaration) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_core_type) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_val_ident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 596 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstr _startpos _endpos
        (Pstr_primitive (Val.mk (mkrhs _startpos__2_ _endpos__2_ _2) _4
                           ~prim:_6 ~attrs:_7 ~loc:(rloc _startpos _endpos))) )
# 1027 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_let_bindings) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_rec_flag) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 577 "src/ocaml/typer/preprocess/parser_raw.mly"
    (
      let (extensions, attributes) = _2 in
      let str =
        match _4 with
          [ {pvb_pat = { ppat_desc = Ppat_any; ppat_loc = _ };
            pvb_expr = exp; pvb_attributes = attrs}] ->
            let exp = wrap_exp_attrs _startpos _endpos exp (None, attributes) in
            mkstr _startpos _endpos (Pstr_eval (exp, attrs))
        | l ->
          if attributes <> [] then
            not_expecting _startpos__2_ _endpos__2_ "attribute";
          mkstr _startpos _endpos (Pstr_value(_3, List.rev l))
      in
      match extensions with
      | None -> str
      | Some id -> ghstr _startpos _endpos (Pstr_extension((id, PStr str), []))
    )
# 1049 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (decls : 'tv_type_declarations) (_startpos_decls_ : Lexing.position) (_endpos_decls_ : Lexing.position) (_startofs_decls_ : int) (_endofs_decls_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2231 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let ty = List.map fake_tydecl decls in
      let loc = rloc _startpos__2_ _endpos__2_ in
      mkstr _startpos _endpos (Pstr_type(List.rev_map (tag_nonrec loc) ty)) )
# 1057 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_let_bindings) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_rec_flag) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2215 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( match _4 with
    | [ {pvb_pat = { ppat_desc = Ppat_any; ppat_loc = _ };
         pvb_expr = exp; pvb_attributes = attrs} ] ->
        let exp = wrap_exp_attrs _startpos _endpos exp _2 in
        mkstr _startpos _endpos (Pstr_eval (Fake.app Fake.Lwt.un_lwt exp, attrs))
    | _ ->
      let str = mkstr _startpos _endpos
            (Pstr_value (_3, List.rev_map (fake_vb_app Fake.Lwt.un_lwt) _4))
      in
      let (ext, attrs) = _2 in
      if attrs <> [] then not_expecting _startpos__2_ _endpos__2_ "attribute";
      match ext with
      | None -> str
      | Some id -> ghstr _startpos _endpos (Pstr_extension((id, PStr str), []))
    )
# 1077 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_structure_tail) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_toplevel_directives) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 567 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 1083 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_head) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_structure_tail) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_post_item_attributes) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_seq_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_toplevel_directives) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 565 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkstrexp _2 _3 :: _4 )
# 1089 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure_head) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (v : 'tv_structure_head) (_startpos_v_ : Lexing.position) (_endpos_v_ : Lexing.position) (_startofs_v_ : int) (_endofs_v_ : int) ->
    (
# 562 "src/ocaml/typer/preprocess/parser_raw.mly"
  ( v )
# 1095 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_structure) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_fun_binding) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 1100 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1268 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_newtype(_3, _5)) )
# 1105 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_strict_binding) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_fun_binding) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_labeled_simple_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1266 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (l, o, p) = _1 in ghexp _startpos _endpos (Pexp_fun(l, o, p, _2)) )
# 1111 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_strict_binding) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_seq_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1264 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 1117 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_strict_binding) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_7 : 'tv_post_item_attributes) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : 'tv_str_extension_constructors) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_opt_bar) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_private_flag) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_type_longident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_optional_type_parameters) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1577 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Te.mk (mkrhs _startpos__2_ _endpos__2_ _2) (List.rev _6)
        ~params:_1 ~priv:_4 ~attrs:_7 )
# 1124 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_str_type_extension) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_extension_constructor_rebind) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_str_extension_constructors) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1593 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 1130 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_str_extension_constructors) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_extension_constructor_declaration) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_str_extension_constructors) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1591 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 1136 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_str_extension_constructors) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_extension_constructor_rebind) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1589 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 1142 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_str_extension_constructors) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_extension_constructor_declaration) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1587 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 1148 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_str_extension_constructors) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_post_item_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_extension_constructor_rebind) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1543 "src/ocaml/typer/preprocess/parser_raw.mly"
    (
      let ext = _1 in
      {ext with pext_attributes = ext.pext_attributes @ _2}
    )
# 1157 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_str_exception_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_post_item_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_extension_constructor_declaration) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1538 "src/ocaml/typer/preprocess/parser_raw.mly"
    (
      let ext = _1 in
      {ext with pext_attributes = ext.pext_attributes @ _2}
    )
# 1166 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_str_exception_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2157 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "with" )
# 1172 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2155 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "while" )
# 1178 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2153 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "when" )
# 1184 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2151 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "virtual" )
# 1190 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2149 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "val" )
# 1196 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2147 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "type" )
# 1202 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2145 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "try" )
# 1208 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2143 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "true" )
# 1214 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2141 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "to" )
# 1220 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2139 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "then" )
# 1226 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2137 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "struct" )
# 1232 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2135 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "sig" )
# 1238 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2133 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "rec" )
# 1244 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2131 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "private" )
# 1250 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2129 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "or" )
# 1256 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2127 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "open" )
# 1262 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2125 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "of" )
# 1268 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2123 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "object" )
# 1274 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2121 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "new" )
# 1280 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2119 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "mutable" )
# 1286 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2117 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "module" )
# 1292 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2115 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "method" )
# 1298 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2113 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "match" )
# 1304 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2111 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "let" )
# 1310 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2109 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "lazy" )
# 1316 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2107 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "initializer" )
# 1322 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2105 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "inherit" )
# 1328 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2103 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "include" )
# 1334 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2101 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "in" )
# 1340 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2099 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "if" )
# 1346 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2097 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "functor" )
# 1352 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2095 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "function" )
# 1358 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2093 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "fun" )
# 1364 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2091 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "for" )
# 1370 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2089 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "false" )
# 1376 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2087 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "external" )
# 1382 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2085 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "exception" )
# 1388 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2083 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "end" )
# 1394 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2081 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "else" )
# 1400 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2079 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "downto" )
# 1406 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2077 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "done" )
# 1412 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2075 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "do" )
# 1418 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2073 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "constraint" )
# 1424 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2071 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "class" )
# 1430 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2069 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "begin" )
# 1436 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2067 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "assert" )
# 1442 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2065 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "as" )
# 1448 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2063 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "and" )
# 1454 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 1459 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2061 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 1464 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 1469 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2059 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 1474 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_single_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_extension) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1406 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_extension _1) )
# 1480 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_package_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 1485 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1403 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_constraint(mkpat _startpos _endpos(Ppat_unpack (mkrhs _startpos__3_ _endpos__3_ _3)),
                              ghtyp _startpos _endpos (Ptyp_package _5))) )
# 1491 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 1496 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1401 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_unpack (mkrhs _startpos__3_ _endpos__3_ _3)) )
# 1501 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_core_type) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_pattern) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1397 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_constraint(_2, _4)) )
# 1507 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_pattern) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1395 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( reloc_pat _startpos _endpos _2 )
# 1513 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1393 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_array []) )
# 1519 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_opt_semi) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_pattern_semi_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1391 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_array(List.rev _2)) )
# 1525 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_opt_semi) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_pattern_semi_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1388 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( reloc_pat _startpos _endpos (mktailpat _startpos__4_ _endpos__4_ (List.rev _2)) )
# 1531 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_lbl_pattern_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1385 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (fields, closed) = _2 in mkpat _startpos _endpos (Ppat_record(fields, closed)) )
# 1537 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_type_longident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1382 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_type (mkrhs _startpos__2_ _endpos__2_ _2)) )
# 1543 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_name_tag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1380 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_variant(_1, None)) )
# 1549 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_constr_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1378 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_construct(mkrhs _startpos__1_ _endpos__1_ _1, None)) )
# 1555 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_signed_constant) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_signed_constant) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1376 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_interval (_1, _3)) )
# 1561 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_signed_constant) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1374 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_constant _1) )
# 1567 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1372 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_any) )
# 1573 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern_not_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_simple_pattern_not_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1369 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 1579 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_val_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1367 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_var (mkrhs _startpos__1_ _endpos__1_ _1)) )
# 1585 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_labeled_simple_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_simple_labeled_expr_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1205 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 :: _1 )
# 1591 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_labeled_expr_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_labeled_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1203 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 1597 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_labeled_expr_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1199 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let id = mkloc "merlin.hole" (rloc _startpos _endpos) in
      mkexp _startpos _endpos (Pexp_extension (id, PStr [])) )
# 1604 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_extension) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1197 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_extension _1) )
# 1610 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_8 : unit) (_startpos__8_ : Lexing.position) (_endpos__8_ : Lexing.position) (_startofs__8_ : int) (_endofs__8_ : int) (_7 : 'tv_package_type) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_module_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1193 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_open(Fresh, mkrhs _startpos__1_ _endpos__1_ _1,
        mkexp _startpos _endpos (Pexp_constraint (ghexp _startpos _endpos (Pexp_pack _5),
                                ghtyp _startpos _endpos (Ptyp_package _7))))) )
# 1618 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_package_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_module_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1190 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_constraint (ghexp _startpos _endpos (Pexp_pack _3),
                                ghtyp _startpos _endpos (Ptyp_package _5))) )
# 1625 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_module_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1188 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_pack _3) )
# 1631 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_simple_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 399 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 1636 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1186 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ _2 _3 )
# 1641 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_label) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1184 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_send(_1, _3)) )
# 1647 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_opt_semi) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_field_expr_list) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1182 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_open(Fresh, mkrhs _startpos__1_ _endpos__1_ _1, mkexp _startpos__4_ _endpos__4_ (Pexp_override(List.rev _4)))) )
# 1653 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1180 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_override []))
# 1659 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_opt_semi) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_field_expr_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1178 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_override(List.rev _2)) )
# 1665 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_class_longident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1176 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_new(mkrhs _startpos__3_ _endpos__3_ _3)) _2 )
# 1671 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_simple_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1174 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_apply(mkoperator _startpos__1_ _endpos__1_ "!", ["",_2])) )
# 1677 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_simple_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 387 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 1682 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1172 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_apply(mkoperator _startpos__1_ _endpos__1_ _1, ["",_2])) )
# 1687 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_opt_semi) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_expr_semi_list) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1169 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let list_exp = reloc_exp _startpos _endpos (mktailexp _startpos__6_ _endpos__6_ (List.rev _4)) in
        mkexp _startpos _endpos (Pexp_open(Fresh, mkrhs _startpos__1_ _endpos__1_ _1, list_exp)) )
# 1694 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_opt_semi) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_expr_semi_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1167 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( reloc_exp _startpos _endpos (mktailexp _startpos__4_ _endpos__4_ (List.rev _2)) )
# 1700 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_opt_semi) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_expr_semi_list) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1165 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_open(Fresh, mkrhs _startpos__1_ _endpos__1_ _1, mkexp _startpos__4_ _endpos__4_ (Pexp_array(List.rev _4)))) )
# 1706 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1163 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_array []) )
# 1712 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_opt_semi) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_expr_semi_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1161 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_array(List.rev _2)) )
# 1718 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_record_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1157 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (exten, fields) = _4 in
        let rec_exp = mkexp _startpos _endpos (Pexp_record(fields, exten)) in
        mkexp _startpos _endpos (Pexp_open(Fresh, mkrhs _startpos__1_ _endpos__1_ _1, rec_exp)) )
# 1726 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_record_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1155 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (exten, fields) = _2 in mkexp _startpos _endpos (Pexp_record(fields, exten)) )
# 1732 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_ope : unit) (_startpos__ope_ : Lexing.position) (_endpos__ope_ : Lexing.position) (_startofs__ope_ : int) (_endofs__ope_ : int) (_ops : unit) (_startpos__ops_ : Lexing.position) (_endpos__ops_ : Lexing.position) (_startofs__ops_ : int) (_endofs__ops_ : int) (_1 : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1153 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( bigarray_get (_startpos,_endpos) (_startpos__ops_,_endpos__ope_) _1 _4 )
# 1738 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_seq_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_ope : unit) (_startpos__ope_ : Lexing.position) (_endpos__ope_ : Lexing.position) (_startofs__ope_ : int) (_endofs__ope_ : int) (_ops : unit) (_startpos__ops_ : Lexing.position) (_endpos__ops_ : Lexing.position) (_startofs__ops_ : int) (_endofs__ops_ : int) (_1 : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1148 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos
          (Pexp_apply(ghexp _startpos__ops_ _endpos__ope_
                 (Pexp_ident(array_function _startpos__ops_ _endpos__ope_ "String" "get")),
                         ["",_1; "",_4])) )
# 1747 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_seq_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_ope : unit) (_startpos__ope_ : Lexing.position) (_endpos__ope_ : Lexing.position) (_startofs__ope_ : int) (_endofs__ope_ : int) (_ops : unit) (_startpos__ops_ : Lexing.position) (_endpos__ops_ : Lexing.position) (_startofs__ops_ : int) (_endofs__ops_ : int) (_1 : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1143 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos
          (Pexp_apply(ghexp _startpos__ops_ _endpos__ope_
                 (Pexp_ident(array_function _startpos__ops_ _endpos__ope_ "Array" "get")),
                         ["",_1; "",_4])) )
# 1756 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_seq_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1141 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_open(Fresh, mkrhs _startpos__1_ _endpos__1_ _1, _4)) )
# 1762 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_label_longident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1139 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_field(_1, mkrhs _startpos__3_ _endpos__3_ _3)) )
# 1768 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_type_constraint) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_seq_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1137 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_constraint _startpos _endpos _2 _3 )
# 1774 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1134 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_construct (mkloc (Lident "()") (rloc _startpos _endpos),
                               None)) _2 )
# 1781 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1132 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( wrap_exp_attrs _startpos _endpos (reloc_exp _startpos _endpos _3) _2 (* check location *) )
# 1787 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_simple_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1130 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Fake.Meta.uncode _startpos _endpos _2 )
# 1793 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1128 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Fake.Meta.code _startpos _endpos _2 )
# 1799 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_seq_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1126 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( reloc_exp _startpos _endpos _2 )
# 1805 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_name_tag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1124 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_variant(_1, None)) )
# 1811 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_constr_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1122 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_construct(mkrhs _startpos__1_ _endpos__1_ _1, None)) )
# 1817 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_constant) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1120 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_constant _1) )
# 1823 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_val_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1118 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_ident (mkrhs _startpos__1_ _endpos__1_ _1)) )
# 1829 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_core_type_list_no_attr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_simple_core_type_no_attr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1793 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_tuple(_1 :: List.rev _3)) )
# 1835 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type_or_tuple_no_attr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_simple_core_type_no_attr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1791 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 1841 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type_or_tuple_no_attr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_core_type_list) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_simple_core_type) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1788 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_tuple(_1 :: List.rev _3)) )
# 1847 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type_or_tuple) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_simple_core_type) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1786 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 1853 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type_or_tuple) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_core_type_comma_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1693 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( match _2 with [sty] -> sty
                  | _ ->
                    syntax_error _startpos _endpos;
                    mktyp _startpos _endpos (Ptyp_any)
    )
# 1863 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type_no_attr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_simple_core_type2) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1691 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 1869 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type_no_attr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_extension) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1740 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_extension _1) )
# 1875 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_package_type) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1738 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_package _3) )
# 1881 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_name_tag_list) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_row_field_list) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_opt_bar) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1736 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_variant(List.rev _3, Closed, Some (List.rev _5))) )
# 1887 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_row_field_list) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_opt_bar) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1734 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_variant(List.rev _3, Closed, Some [])) )
# 1893 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1732 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_variant([], Open, None)) )
# 1899 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_row_field_list) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_opt_bar) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1730 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_variant(List.rev _3, Open, None)) )
# 1905 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_row_field_list) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_row_field) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1728 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_variant(_2 :: List.rev _4, Closed, None)) )
# 1911 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_row_field_list) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1726 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_variant(List.rev _3, Closed, None)) )
# 1917 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_tag_field) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1720 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_variant([_2], Closed, None)) )
# 1923 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_class_longident) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_core_type_comma_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1718 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_class(mkrhs _startpos__5_ _endpos__5_ _5, List.rev _2)) )
# 1929 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_class_longident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_simple_core_type2) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1716 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_class(mkrhs _startpos__3_ _endpos__3_ _3, [_1])) )
# 1935 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_class_longident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1714 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_class(mkrhs _startpos__2_ _endpos__2_ _2, [])) )
# 1941 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1712 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_object ([], Closed)) )
# 1947 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_meth_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1710 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (f, c) = _2 in mktyp _startpos _endpos (Ptyp_object (f, c)) )
# 1953 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_type_longident) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_core_type_comma_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1708 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_constr(mkrhs _startpos__4_ _endpos__4_ _4, List.rev _2)) )
# 1959 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_type_longident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_simple_core_type2) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1706 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_constr(mkrhs _startpos__2_ _endpos__2_ _2, [_1])) )
# 1965 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_type_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1704 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_constr(mkrhs _startpos__1_ _endpos__1_ _1, [])) )
# 1971 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1702 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_any) )
# 1977 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_ident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1700 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_var _2) )
# 1983 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_core_type_comma_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1684 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( match _2 with [sty] -> sty
                  | _ ->
                    syntax_error _startpos _endpos;
                    mktyp _startpos _endpos (Ptyp_any)
    )
# 1993 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_simple_core_type2) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1682 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 1999 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_simple_core_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : (
# 376 "src/ocaml/typer/preprocess/parser_raw.mly"
       (nativeint)
# 2004 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1860 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_nativeint _2 )
# 2009 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signed_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : (
# 350 "src/ocaml/typer/preprocess/parser_raw.mly"
       (int64)
# 2014 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1858 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_int64 _2 )
# 2019 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signed_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : (
# 349 "src/ocaml/typer/preprocess/parser_raw.mly"
       (int32)
# 2024 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1856 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_int32 _2 )
# 2029 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signed_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : (
# 330 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2034 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1854 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_float _2 )
# 2039 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signed_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : (
# 348 "src/ocaml/typer/preprocess/parser_raw.mly"
       (int)
# 2044 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1852 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_int _2 )
# 2049 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signed_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : (
# 376 "src/ocaml/typer/preprocess/parser_raw.mly"
       (nativeint)
# 2054 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1850 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_nativeint(Nativeint.neg _2) )
# 2059 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signed_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : (
# 350 "src/ocaml/typer/preprocess/parser_raw.mly"
       (int64)
# 2064 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1848 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_int64(Int64.neg _2) )
# 2069 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signed_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : (
# 349 "src/ocaml/typer/preprocess/parser_raw.mly"
       (int32)
# 2074 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1846 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_int32(Int32.neg _2) )
# 2079 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signed_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : (
# 330 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2084 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1844 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_float("-" ^ _2) )
# 2089 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signed_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : (
# 348 "src/ocaml/typer/preprocess/parser_raw.mly"
       (int)
# 2094 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1842 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_int(- _2) )
# 2099 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signed_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_constant) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1840 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2105 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signed_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_floating_attribute) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 716 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_attribute _1) )
# 2111 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_post_item_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_item_extension) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 714 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_extension (_1, _2)) )
# 2117 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_class_type_declarations) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 712 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_class_type (List.rev _3)) )
# 2123 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_class_descriptions) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 709 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_class (List.rev _2)) )
# 2129 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_post_item_attributes) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_module_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 706 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_include (Incl.mk _2 ~attrs:_3
                                             ~loc:(rloc _startpos _endpos))) )
# 2136 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_open_statement) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 704 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_open _1) )
# 2142 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_post_item_attributes) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_module_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_ident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 700 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_modtype (Mtd.mk (mkrhs _startpos__3_ _endpos__3_ _3) ~typ:_5
                              ~loc:(rloc _startpos _endpos)
                              ~attrs:_6)) )
# 2150 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_post_item_attributes) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_ident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 697 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_modtype (Mtd.mk (mkrhs _startpos__3_ _endpos__3_ _3)
                              ~attrs:_4 ~loc:(rloc _startpos _endpos))) )
# 2157 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_rec_module_declarations) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 695 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_recmodule (List.rev _3)) )
# 2163 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_post_item_attributes) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_mod_longident) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2168 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 689 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_module (Md.mk (mkrhs _startpos__2_ _endpos__2_ _2)
                             (Mty.alias ~loc:(rloc _startpos__4_ _endpos__4_) (mkrhs _startpos__4_ _endpos__4_ _4))
                             ~attrs:_5
                             ~loc:(rloc _startpos _endpos)
                          )) )
# 2177 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_post_item_attributes) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_module_declaration) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2182 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 686 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_module (Md.mk (mkrhs _startpos__2_ _endpos__2_ _2)
                             _3 ~attrs:_4 ~loc:(rloc _startpos _endpos))) )
# 2188 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_sig_exception_declaration) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 684 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_exception _2) )
# 2194 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_sig_type_extension) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 682 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_typext _2) )
# 2200 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_type_declarations) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 680 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_type (List.rev _2)) )
# 2206 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_7 : 'tv_post_item_attributes) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : 'tv_primitive_declaration) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_core_type) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_val_ident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 676 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_value
                (Val.mk (mkrhs _startpos__2_ _endpos__2_ _2) _4 ~prim:_6 ~attrs:_7
                   ~loc:(rloc _startpos _endpos))) )
# 2214 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_post_item_attributes) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_core_type) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_val_ident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 672 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mksig _startpos _endpos (Psig_value
                (Val.mk (mkrhs _startpos__2_ _endpos__2_ _2) _4 ~attrs:_5 ~loc:(rloc _startpos _endpos))) )
# 2221 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (decls : 'tv_type_declarations) (_startpos_decls_ : Lexing.position) (_endpos_decls_ : Lexing.position) (_startofs_decls_ : int) (_endofs_decls_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2236 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let ty = List.map fake_tydecl decls in
      let loc = rloc _startpos__2_ _endpos__2_ in
      mksig _startpos _endpos (Psig_type (List.rev_map (tag_nonrec loc) ty)) )
# 2229 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature_item) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_signature) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_signature_item) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 669 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 @ _2 )
# 2235 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_signature) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 667 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 2241 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 665 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [] )
# 2247 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_signature) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_7 : 'tv_post_item_attributes) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : 'tv_sig_extension_constructors) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_opt_bar) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_private_flag) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_type_longident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_optional_type_parameters) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1583 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Te.mk (mkrhs _startpos__2_ _endpos__2_ _2) (List.rev _6)
        ~params:_1 ~priv:_4 ~attrs:_7 )
# 2254 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_sig_type_extension) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_extension_constructor_declaration) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_sig_extension_constructors) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1598 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 2260 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_sig_extension_constructors) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_extension_constructor_declaration) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1596 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 2266 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_sig_extension_constructors) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_post_item_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_extension_constructor_declaration) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1549 "src/ocaml/typer/preprocess/parser_raw.mly"
    (
      let ext = _1 in
      {ext with pext_attributes = ext.pext_attributes @ _2}
    )
# 2275 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_sig_exception_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 952 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_sequence(_1, _3)) )
# 2281 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_seq_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 950 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( reloc_exp _startpos _endpos _1 )
# 2287 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_seq_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 948 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2293 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_seq_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_row_field) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_row_field_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1758 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 2299 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_row_field_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_row_field) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1756 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 2305 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_row_field_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_simple_core_type) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1763 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Rinherit _1 )
# 2311 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_row_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_tag_field) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1761 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2317 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_row_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_lbl_expr_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1302 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (None, _1) )
# 2323 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_record_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_lbl_expr_list) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1300 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (Some _1, _3) )
# 2329 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_record_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_module_rec_declaration) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_rec_module_declarations) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 733 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 2335 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_rec_module_declarations) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_module_rec_declaration) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 731 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 2341 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_rec_module_declarations) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1999 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Recursive )
# 2347 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_rec_flag) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 1997 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Nonrecursive )
# 2353 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_rec_flag) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2030 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Private, Virtual )
# 2359 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_private_virtual_flags) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2028 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Private, Virtual )
# 2365 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_private_virtual_flags) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2026 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Public, Virtual )
# 2371 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_private_virtual_flags) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2024 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Private, Concrete )
# 2377 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_private_virtual_flags) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 2022 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Public, Concrete )
# 2383 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_private_virtual_flags) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2009 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Private )
# 2389 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_private_flag) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 2007 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Public )
# 2395 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_private_flag) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_primitive_declaration) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 402 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string * string option)
# 2400 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1438 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( fst _1 :: _2 )
# 2405 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_primitive_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 402 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string * string option)
# 2410 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1436 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [fst _1] )
# 2415 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_primitive_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_post_item_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_post_item_attribute) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2177 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 :: _2 )
# 2421 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_post_item_attributes) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 2175 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [] )
# 2427 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_post_item_attributes) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_payload) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_attr_id) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2169 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (_2, _3) )
# 2433 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_post_item_attribute) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_core_type_no_attr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_typevar_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1657 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_poly(List.rev _1, _3)) )
# 2439 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_poly_type_no_attr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_core_type_no_attr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1655 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2445 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_poly_type_no_attr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_core_type) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_typevar_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1652 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_poly(List.rev _1, _3)) )
# 2451 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_poly_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_core_type) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1650 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2457 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_poly_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_seq_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_pattern) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2204 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( PPat (_2, Some _4) )
# 2463 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_payload) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_pattern) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2202 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( PPat (_2, None) )
# 2469 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_payload) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_core_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2200 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( PTyp _2 )
# 2475 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_payload) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_structure) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2198 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( PStr _1 )
# 2481 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_payload) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 974 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos Ppat_any )
# 2487 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern_var) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2492 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 972 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_var (mkrhs _startpos__1_ _endpos__1_ _1)) )
# 2497 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern_var) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_pattern) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_pattern_semi_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1418 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 2503 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern_semi_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1416 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 2509 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern_semi_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_pattern) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1411 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_3; _1] )
# 2515 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern_comma_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_pattern) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_pattern_comma_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1409 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 2521 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern_comma_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_attribute) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1364 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Pat.attr _1 _2 )
# 2527 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_pattern) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1362 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_exception _2) )
# 2533 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_simple_pattern) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1360 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_lazy _2) )
# 2539 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_pattern) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1356 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_or(_1, _3)) )
# 2545 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_8 : unit) (_startpos__8_ : Lexing.position) (_endpos__8_ : Lexing.position) (_startofs__8_ : int) (_endofs__8_ : int) (_7 : 'tv_pattern) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_pattern) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1354 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat_cons (rloc _startpos__2_ _endpos__2_) (ghpat _startpos _endpos (Ppat_tuple[_5;_7])) (rloc _startpos _endpos) )
# 2551 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_pattern) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1350 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat_cons (rloc _startpos__2_ _endpos__2_) (ghpat _startpos _endpos (Ppat_tuple[_1;_3])) (rloc _startpos _endpos) )
# 2557 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_pattern) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_name_tag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1348 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_variant(_1, Some _2)) )
# 2563 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_pattern) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_constr_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1346 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_construct(mkrhs _startpos__1_ _endpos__1_ _1, Some _2)) )
# 2569 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_pattern_comma_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1344 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_tuple(List.rev _1)) )
# 2575 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_val_ident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1340 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_alias(_1, mkrhs _startpos__3_ _endpos__3_ _3)) )
# 2581 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_simple_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1338 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2587 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_seq_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 512 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2593 "src/ocaml/typer/preprocess/parser_raw.ml"
     : (
# 501 "src/ocaml/typer/preprocess/parser_raw.mly"
      (Parsetree.expression)
# 2597 "src/ocaml/typer/preprocess/parser_raw.ml"
    )) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 826 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( None )
# 2603 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_parent_binder) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2608 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 824 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Some _2 )
# 2613 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_parent_binder) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_package_type_cstrs) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_package_type_cstr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1753 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1::_3 )
# 2619 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_package_type_cstrs) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_package_type_cstr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1751 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 2625 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_package_type_cstrs) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_core_type) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_label_longident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1748 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (mkrhs _startpos__2_ _endpos__2_ _2, _4) )
# 2631 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_package_type_cstr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_package_type_cstrs) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mty_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1745 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (mkrhs _startpos__1_ _endpos__1_ _1, _3) )
# 2637 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_package_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_mty_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1743 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (mkrhs _startpos__1_ _endpos__1_ _1, []) )
# 2643 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_package_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2035 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Override )
# 2649 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_override_flag) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 2033 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Fresh )
# 2655 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_override_flag) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1499 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_any) )
# 2661 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_optional_type_variable) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_ident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1497 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_var _2) )
# 2667 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_optional_type_variable) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_optional_type_parameter_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1486 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( List.rev _2 )
# 2673 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_optional_type_parameters) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_optional_type_parameter) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1484 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 2679 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_optional_type_parameters) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 1482 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [] )
# 2685 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_optional_type_parameters) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_optional_type_parameter) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_optional_type_parameter_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1494 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 2691 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_optional_type_parameter_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_optional_type_parameter) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1492 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 2697 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_optional_type_parameter_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_optional_type_variable) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_type_variance) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1489 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2, _1 )
# 2703 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_optional_type_parameter) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2045 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( () )
# 2709 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_opt_semi) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 2043 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( () )
# 2715 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_opt_semi) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_seq_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 979 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Some _2 )
# 2721 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_opt_default) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 977 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( None )
# 2727 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_opt_default) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2040 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( () )
# 2733 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_opt_bar) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 2038 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( () )
# 2739 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_opt_bar) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 1773 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( false )
# 2745 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_opt_ampersand) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1771 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( true )
# 2751 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_opt_ampersand) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1924 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "%" )
# 2757 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1922 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "+=" )
# 2763 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1920 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( ":=" )
# 2769 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1918 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "&&" )
# 2775 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1916 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "&" )
# 2781 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1914 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "||" )
# 2787 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1912 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "or" )
# 2793 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1910 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( ">" )
# 2799 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1908 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "<" )
# 2805 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1906 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "=" )
# 2811 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1904 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "*" )
# 2817 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1902 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "-." )
# 2823 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1900 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "-" )
# 2829 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1898 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "+." )
# 2835 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1896 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "+" )
# 2841 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1894 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "!" )
# 2847 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 399 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2852 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1892 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2857 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 429 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2862 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1890 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2867 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 345 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2872 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1888 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2877 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 344 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2882 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1886 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2887 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 343 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2892 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1884 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2897 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 342 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2902 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1882 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2907 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 341 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2912 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1880 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2917 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 387 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2922 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1878 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 2927 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_post_item_attributes) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_mod_longident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_override_flag) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 720 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Opn.mk (mkrhs _startpos__3_ _endpos__3_ _3) ~override:_2 ~attrs:_4
        ~loc:(rloc _startpos _endpos) )
# 2934 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_open_statement) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 2939 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2208 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 )
# 2944 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_newtype) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_name_tag) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_name_tag_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1783 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 :: _1 )
# 2950 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_name_tag_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_name_tag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1781 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 2956 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_name_tag_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_ident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1994 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 2962 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_name_tag) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2014 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Mutable )
# 2968 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_mutable_flag) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 2012 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Immutable )
# 2974 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_mutable_flag) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_ident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_ext_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1980 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Ldot(_1, _3) )
# 2980 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_mty_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1978 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Lident _1 )
# 2986 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_mty_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_attribute) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_module_type) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 662 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Mty.attr _1 _2 )
# 2992 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_extension) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 660 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmty _startpos _endpos (Pmty_extension _1) )
# 2998 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_module_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 658 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 3004 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_module_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 654 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmty _startpos _endpos (Pmty_typeof _4) )
# 3010 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_with_constraints) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_module_type) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 652 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmty _startpos _endpos (Pmty_with(_1, List.rev _3)) )
# 3016 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_module_type) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_functor_args) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 650 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( List.fold_left (fun acc (n, t) -> mkmty _startpos _endpos (Pmty_functor(n, t, acc))) _4 _2 )
# 3022 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_signature) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 648 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmty _startpos _endpos (Pmty_signature _2) )
# 3028 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_mty_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 646 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmty _startpos _endpos (Pmty_ident (mkrhs _startpos__1_ _endpos__1_ _1)) )
# 3034 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_post_item_attributes) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_module_type) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3039 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 736 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Md.mk (mkrhs _startpos__1_ _endpos__1_ _1) _3 ~attrs:_4 ~loc:(rloc _startpos _endpos) )
# 3044 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_rec_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_extension) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 559 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmod _startpos _endpos (Pmod_extension _1) )
# 3050 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_attribute) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_module_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 557 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Mod.attr _1 _2 )
# 3056 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_package_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 554 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmod _startpos _endpos (Pmod_unpack(
              ghexp _startpos _endpos (Pexp_coerce(_3, None, ghtyp _startpos _endpos (Ptyp_package _5))))) )
# 3063 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_8 : unit) (_startpos__8_ : Lexing.position) (_endpos__8_ : Lexing.position) (_startofs__8_ : int) (_endofs__8_ : int) (_7 : 'tv_package_type) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_package_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 550 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmod _startpos _endpos (Pmod_unpack(
              ghexp _startpos _endpos (Pexp_coerce(_3, Some(ghtyp _startpos _endpos (Ptyp_package _5)),
                                    ghtyp _startpos _endpos (Ptyp_package _7))))) )
# 3071 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_package_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 547 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmod _startpos _endpos (Pmod_unpack(
              ghexp _startpos _endpos (Pexp_constraint(_3, ghtyp _startpos _endpos (Ptyp_package _5))))) )
# 3078 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 545 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmod _startpos _endpos (Pmod_unpack _3) )
# 3084 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_module_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 543 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 3090 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_module_type) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_module_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 541 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmod _startpos _endpos (Pmod_constraint(_2, _4)) )
# 3096 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_module_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 539 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmod _startpos _endpos (Pmod_apply(_1, mkmod _startpos _endpos (Pmod_structure []))) )
# 3102 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_module_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_module_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 537 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmod _startpos _endpos (Pmod_apply(_1, _3)) )
# 3108 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_module_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_functor_args) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 535 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( List.fold_left (fun acc (n, t) -> mkmod _startpos _endpos (Pmod_functor(n, t, acc))) _4 _2 )
# 3114 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_structure) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 533 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmod _startpos _endpos (Pmod_structure(_2)) )
# 3120 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_mod_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 531 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmod _startpos _endpos (Pmod_ident (mkrhs _startpos__1_ _endpos__1_ _1)) )
# 3126 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_module_declaration) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 728 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmty _startpos _endpos (Pmty_functor(mkrhs _startpos__1_ _endpos__1_ "*", None, _3)) )
# 3132 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_module_declaration) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_module_type) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3137 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 726 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmty _startpos _endpos (Pmty_functor(mkrhs _startpos__2_ _endpos__2_ _2, Some _4, _6)) )
# 3142 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_module_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 724 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 3148 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_module_binding) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_module_bindings) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 639 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 3154 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_bindings) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_module_binding) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 637 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 3160 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_bindings) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_module_binding_body) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_functor_arg) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 634 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmod _startpos _endpos (Pmod_functor(fst _1, snd _1, _2)) )
# 3166 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_binding_body) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_module_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_module_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 632 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkmod _startpos _endpos (Pmod_constraint(_4, _2)) )
# 3172 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_binding_body) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_module_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 630 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 3178 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_binding_body) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_post_item_attributes) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_module_binding_body) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3183 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 642 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Mb.mk (mkrhs _startpos__1_ _endpos__1_ _1) _2 ~attrs:_3 ~loc:(rloc _startpos _endpos) )
# 3188 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_module_binding) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3193 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1968 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Ldot(_1, _3) )
# 3198 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_mod_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3203 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1966 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Lident _1 )
# 3208 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_mod_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_mod_ext_longident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_ext_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1975 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( lapply _startpos _endpos _1 _3 )
# 3214 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_mod_ext_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3219 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_ext_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1973 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Ldot(_1, _3) )
# 3224 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_mod_ext_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3229 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1971 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Lident _1 )
# 3234 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_mod_ext_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (v10 : 'tv_seq_expr) (_startpos_v10_ : Lexing.position) (_endpos_v10_ : Lexing.position) (_startofs_v10_ : int) (_endofs_v10_ : int) (_9 : unit) (_startpos__9_ : Lexing.position) (_endpos__9_ : Lexing.position) (_startofs__9_ : int) (_endofs__9_ : int) (_8 : 'tv_core_type) (_startpos__8_ : Lexing.position) (_endpos__8_ : Lexing.position) (_startofs__8_ : int) (_endofs__8_ : int) (_7 : unit) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : 'tv_lident_list) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_private_flag) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_override_flag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 854 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let exp, poly = wrap_type_annotation _startpos _endpos _6 _8 v10 in
        mkloc _3 (rloc _startpos__3_ _endpos__3_), _2, Cfk_concrete (_1, ghexp _startpos _endpos (Pexp_poly(exp, Some poly))) )
# 3241 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_method_) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_7 : 'tv_seq_expr) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_poly_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_private_flag) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_override_flag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 852 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkloc _3 (rloc _startpos__3_ _endpos__3_), _2, Cfk_concrete (_1, ghexp _startpos _endpos (Pexp_poly(_7, Some _5))) )
# 3247 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_method_) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_strict_binding) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_private_flag) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_override_flag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 850 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkloc _3 (rloc _startpos__3_ _endpos__3_), _2, Cfk_concrete (_1, ghexp _startpos _endpos (Pexp_poly (_4, None))) )
# 3253 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_method_) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_poly_type) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_label) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_private_flag) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_override_flag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 847 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( if _1 = Override then syntax_error _startpos _endpos;
        mkloc _4 (rloc _startpos__4_ _endpos__4_), _3, Cfk_virtual _6 )
# 3260 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_method_) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_poly_type) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_label) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_override_flag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 844 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( if _1 = Override then syntax_error _startpos _endpos;
        mkloc _4 (rloc _startpos__4_ _endpos__4_), Private, Cfk_virtual _6 )
# 3267 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_method_) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1815 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [], Open )
# 3273 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_meth_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_opt_semi) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_field) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1813 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1], Closed )
# 3279 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_meth_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_meth_list) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_field) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1811 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (f, c) = _3 in (_1 :: f, c) )
# 3285 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_meth_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_match_case) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_match_cases) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1273 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 3291 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_match_cases) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_match_case) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1271 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 3297 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_match_cases) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_seq_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1281 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Exp.case _1 ~guard:(merloc _endpos__2_ _3) (merloc _endpos__4_ _5) )
# 3303 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_match_case) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1277 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Exp.case _1 (merloc _endpos__2_ _3) )
# 3309 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_match_case) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_lident_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3314 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1239 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 :: _2 )
# 3319 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_lident_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3324 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1237 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 3329 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_lident_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_core_type) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 992 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_constraint(_1, _3)) )
# 3335 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_let_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 990 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 3341 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_let_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : (
# 429 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3346 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2292 "src/ocaml/typer/preprocess/parser_raw.mly"
  ( mkexp _startpos _endpos
    (Pexp_ident(mkloc (Ldot (_1,_3)) (rloc _startpos _endpos))) )
# 3352 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_let_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 429 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3357 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2289 "src/ocaml/typer/preprocess/parser_raw.mly"
  ( mkexp _startpos _endpos
    (Pexp_ident(mkloc (Lident _1) (rloc _startpos _endpos))) )
# 3363 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_let_operator) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (l : 'tv_let_bindings) (_startpos_l_ : Lexing.position) (_endpos_l_ : Lexing.position) (_startofs_l_ : int) (_endofs_l_ : int) ->
    (
# 1230 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( List.iter (fun vb -> if vb.pvb_attributes <> [] then
        raise_error
          Syntaxerr.(Error(Not_expecting(vb.pvb_loc,"item attribute"))))
        l;
      l )
# 3373 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_let_bindings_no_attrs) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_let_binding) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_let_bindings) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1227 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 3379 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_let_bindings) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_let_binding) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1225 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 3385 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_let_bindings) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_seq_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_core_type) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_simple_pattern_not_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1256 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (ghpat _startpos _endpos (Ppat_constraint(_1, _3)), _5) )
# 3391 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_let_binding_) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1254 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (_1, _3) )
# 3397 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_let_binding_) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_8 : 'tv_seq_expr) (_startpos__8_ : Lexing.position) (_endpos__8_ : Lexing.position) (_startofs__8_ : int) (_endofs__8_ : int) (_7 : unit) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : 'tv_core_type) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_lident_list) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_val_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1251 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let exp, poly = wrap_type_annotation _startpos _endpos _4 _6 _8 in
        (ghpat _startpos _endpos (Ppat_constraint(mkpatvar _startpos__1_ _endpos__1_ _1, poly)), exp) )
# 3404 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_let_binding_) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_7 : 'tv_seq_expr) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_core_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_typevar_list) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_val_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1247 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (ghpat _startpos _endpos (Ppat_constraint(mkpatvar _startpos__1_ _endpos__1_ _1,
                               ghtyp _startpos _endpos (Ptyp_poly(List.rev _3,_5)))),
         _7) )
# 3412 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_let_binding_) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_fun_binding) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_val_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1245 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (mkpatvar _startpos__1_ _endpos__1_ _1, _2) )
# 3418 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_let_binding_) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_post_item_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_let_binding_) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1242 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (p, e) = _1 in Vb.mk ~loc:(rloc _startpos _endpos) ~attrs:_2 p e )
# 3424 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_let_binding) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_lbl_pattern_list) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_lbl_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1427 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (fields, closed) = _3 in _1 :: fields, closed )
# 3430 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_lbl_pattern_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_opt_semi) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_lbl_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1425 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1], Open )
# 3436 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_lbl_pattern_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_lbl_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1423 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1], Closed )
# 3442 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_lbl_pattern_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_lbl_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1421 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1], Closed )
# 3448 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_lbl_pattern_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_label_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1432 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (mkrhs _startpos__1_ _endpos__1_ _1, pat_of_label _startpos__1_ _endpos__1_ _1) )
# 3454 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_lbl_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_pattern) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_label_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1430 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (mkrhs _startpos__1_ _endpos__1_ _1,_3) )
# 3460 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_lbl_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_lbl_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1309 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 3466 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_lbl_expr_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_lbl_expr_list) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_lbl_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1307 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 :: _3 )
# 3472 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_lbl_expr_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_lbl_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1305 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 3478 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_lbl_expr_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_label_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1314 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (mkrhs _startpos__1_ _endpos__1_ _1, exp_of_label _startpos__1_ _endpos__1_ _1) )
# 3484 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_lbl_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_label_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1312 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (mkrhs _startpos__1_ _endpos__1_ _1,_3) )
# 3490 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_lbl_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_simple_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 969 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( ("", None, _1) )
# 3496 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_labeled_simple_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_simple_pattern) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 351 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3501 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 967 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (_1, None, _2) )
# 3506 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_labeled_simple_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_label_var) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 965 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (fst _2, None, snd _2) )
# 3512 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_labeled_simple_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label_let_pattern) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 963 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (fst _3, None, snd _3) )
# 3518 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_labeled_simple_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_pattern_var) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 381 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3523 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 961 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( ("?" ^ _1, None, _2) )
# 3528 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_labeled_simple_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_opt_default) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_let_pattern) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 381 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3533 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 959 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( ("?" ^ _1, _4, _3) )
# 3538 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_labeled_simple_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_label_var) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 957 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( ("?" ^ fst _2, None, snd _2) )
# 3544 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_labeled_simple_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_opt_default) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label_let_pattern) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 955 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( ("?" ^ fst _3, _4, snd _3) )
# 3550 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_labeled_simple_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_label_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1210 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 3556 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_labeled_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1208 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( ("", _1) )
# 3562 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_labeled_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3567 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 987 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (_1, mkpat _startpos _endpos (Ppat_var (mkrhs _startpos__1_ _endpos__1_ _1))) )
# 3572 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_label_var) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3577 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1958 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Ldot(_1, _3) )
# 3582 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_label_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3587 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1956 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Lident _1 )
# 3592 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_label_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_core_type) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_label_var) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 984 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (lab, pat) = _1 in (lab, mkpat _startpos _endpos (Ppat_constraint(pat, _3))) )
# 3598 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_label_let_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_label_var) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 982 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 3604 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_label_let_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3609 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1222 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (_1, mkexp _startpos _endpos (Pexp_ident(mkrhs _startpos__1_ _endpos__1_ (Lident _1)))) )
# 3614 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_label_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_simple_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 381 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3619 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1219 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( ("?" ^ _1, _2) )
# 3624 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_label_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_label_ident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1217 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( ("?" ^ fst _2, snd _2) )
# 3630 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_label_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_label_ident) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1215 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 3636 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_label_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_simple_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 351 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3641 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1213 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (_1, _2) )
# 3646 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_label_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_label_declaration) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_label_declarations) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1566 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 3652 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_label_declarations) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_label_declaration) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1564 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 3658 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_label_declarations) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_attributes) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_poly_type_no_attr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_label) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mutable_flag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1569 "src/ocaml/typer/preprocess/parser_raw.mly"
  (
    Type.field (mkrhs _startpos__2_ _endpos__2_ _2) _4 ~mut:_1 ~attrs:_5 ~loc:(rloc _startpos _endpos)
  )
# 3666 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_label_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3671 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1821 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 3676 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_label) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_payload) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_attr_id) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2195 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (_2, _3) )
# 3682 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_item_extension) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_signature) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 509 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 3688 "src/ocaml/typer/preprocess/parser_raw.ml"
     : (
# 498 "src/ocaml/typer/preprocess/parser_raw.mly"
      (Parsetree.signature)
# 3692 "src/ocaml/typer/preprocess/parser_raw.ml"
    )) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_structure) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 506 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 3698 "src/ocaml/typer/preprocess/parser_raw.ml"
     : (
# 495 "src/ocaml/typer/preprocess/parser_raw.mly"
      (Parsetree.structure)
# 3702 "src/ocaml/typer/preprocess/parser_raw.ml"
    )) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3707 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1866 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 3712 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3717 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1864 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 3722 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_simple_core_type_no_attr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1561 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( ([],Some _2) )
# 3728 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_generalized_constructor_arguments) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_simple_core_type_no_attr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_core_type_list_no_attr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1559 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (List.rev _2,Some _4) )
# 3734 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_generalized_constructor_arguments) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_core_type_list_no_attr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1557 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (List.rev _2,None) )
# 3740 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_generalized_constructor_arguments) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 1555 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( ([],None) )
# 3746 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_generalized_constructor_arguments) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_functor_arg) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 528 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [ _1 ] )
# 3752 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_functor_args) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_functor_arg) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_functor_args) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 526 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 :: _1 )
# 3758 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_functor_args) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 523 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "_" )
# 3764 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_functor_arg_name) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3769 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 521 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 3774 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_functor_arg_name) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_module_type) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_functor_arg_name) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 518 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkrhs _startpos__2_ _endpos__2_ _2, Some _4 )
# 3780 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_functor_arg) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 516 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkrhs _startpos__2_ _endpos__2_ "*", None )
# 3786 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_functor_arg) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_fun_def) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 3791 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1292 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_newtype(_3, _5)) )
# 3796 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_fun_def) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_fun_def) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_labeled_simple_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1287 "src/ocaml/typer/preprocess/parser_raw.mly"
    (
       let (l,o,p) = _1 in
       ghexp _startpos _endpos (Pexp_fun(l, o, p, _2))
      )
# 3805 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_fun_def) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_seq_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1285 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (merloc _endpos__1_ _2) )
# 3811 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_fun_def) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_type_constraint) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1261 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_constraint _startpos _endpos _3 _1 )
# 3817 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_fun_binding) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_strict_binding) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1259 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 3823 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_fun_binding) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_payload) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_attr_id) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2172 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (_2, _3) )
# 3829 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_floating_attribute) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_field_expr_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1319 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (mkrhs _startpos__3_ _endpos__3_ _3, _5) :: _1 )
# 3835 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_field_expr_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_label) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1317 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [mkrhs _startpos__1_ _endpos__1_ _1,_3] )
# 3841 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_field_expr_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_attributes) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_poly_type_no_attr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_label) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1818 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (_1, _4, _3) )
# 3847 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_attributes) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_constr_longident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_constr_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1607 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Te.rebind (mkrhs _startpos__1_ _endpos__1_ _1)
                (mkrhs _startpos__3_ _endpos__3_ _3)
                ~loc:(rloc _startpos _endpos) ~attrs:_4
    )
# 3856 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_extension_constructor_rebind) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_attributes) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_generalized_constructor_arguments) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_constr_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1601 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let args, res = _2 in
      Te.decl (mkrhs _startpos__1_ _endpos__1_ _1) ~args ?res
              ~loc:(rloc _startpos _endpos) ~attrs:_3
    )
# 3865 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_extension_constructor_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_payload) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_attr_id) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2192 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (_2, _3) )
# 3871 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_extension) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_attributes) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_attr_id) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2189 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Some _2, _3 )
# 3877 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_ext_attributes) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_attribute) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2187 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( None, _1 :: _2 )
# 3883 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_ext_attributes) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 2185 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( None, [] )
# 3889 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_ext_attributes) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr_semi_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1324 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 3895 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr_semi_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1322 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 3901 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr_semi_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_mod_longident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_override_flag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2211 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1, mkrhs _startpos__3_ _endpos__3_ _3, _2 )
# 3907 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr_open) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1297 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_3; _1] )
# 3913 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr_comma_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr_comma_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1295 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 3919 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr_comma_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_attribute) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1115 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Exp.attr _1 _2 )
# 3925 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_class_structure) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1113 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_object _3) _2 )
# 3931 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_simple_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1111 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_lazy _3) _2 )
# 3937 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_simple_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1109 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_assert _3) _2 )
# 3943 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_label) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1107 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_setinstvar(mkrhs _startpos__1_ _endpos__1_ _1, _3)) )
# 3949 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_7 : 'tv_expr) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_ope : unit) (_startpos__ope_ : Lexing.position) (_endpos__ope_ : Lexing.position) (_startofs__ope_ : int) (_endofs__ope_ : int) (_ops : unit) (_startpos__ops_ : Lexing.position) (_endpos__ops_ : Lexing.position) (_startofs__ops_ : int) (_endofs__ops_ : int) (_1 : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1105 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( bigarray_set (_startpos,_endpos) (_startpos__ops_,_endpos__ope_) _1 _4 _7 )
# 3955 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_7 : 'tv_expr) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_seq_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_ope : unit) (_startpos__ope_ : Lexing.position) (_endpos__ope_ : Lexing.position) (_startofs__ope_ : int) (_endofs__ope_ : int) (_ops : unit) (_startpos__ops_ : Lexing.position) (_endpos__ops_ : Lexing.position) (_startofs__ops_ : int) (_endofs__ops_ : int) (_1 : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1100 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos
          (Pexp_apply(ghexp _startpos__ops_ _endpos__ope_
                 (Pexp_ident(array_function _startpos__ops_ _endpos__ope_ "String" "set")),
                         ["",_1; "",_4; "",_7])) )
# 3964 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_7 : 'tv_expr) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_seq_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_ope : unit) (_startpos__ope_ : Lexing.position) (_endpos__ope_ : Lexing.position) (_startofs__ope_ : int) (_endofs__ope_ : int) (_ops : unit) (_startpos__ops_ : Lexing.position) (_endpos__ops_ : Lexing.position) (_startofs__ops_ : int) (_endofs__ops_ : int) (_1 : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1095 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos
          (Pexp_apply(ghexp _startpos__ops_ _endpos__ope_
                 (Pexp_ident(array_function _startpos__ops_ _endpos__ope_ "Array" "set")),
                         ["",_1; "",_4; "",_7])) )
# 3973 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label_longident) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1093 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_setfield(_1, mkrhs _startpos__3_ _endpos__3_ _3, _5)) )
# 3979 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_additive) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1091 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkuplus _startpos _endpos _1 _2 )
# 3985 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_subtractive) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1089 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkuminus _startpos _endpos _1 _2 )
# 3991 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1087 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ ":=" _3 )
# 3997 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1085 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ "&&" _3 )
# 4003 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1083 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ "&" _3 )
# 4009 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1081 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ "||" _3 )
# 4015 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1079 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ "or" _3 )
# 4021 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1077 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ ">" _3 )
# 4027 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1075 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ "<" _3 )
# 4033 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1073 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ "=" _3 )
# 4039 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1071 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ "%" _3 )
# 4045 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1069 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ "*" _3 )
# 4051 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1067 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ "-." _3 )
# 4057 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1065 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ "-" _3 )
# 4063 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1063 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ "+=" _3 )
# 4069 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1061 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ "+." _3 )
# 4075 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1059 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ "+" _3 )
# 4081 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 345 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4086 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1057 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ _2 _3 )
# 4091 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 344 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4096 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1055 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ _2 _3 )
# 4101 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 343 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4106 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1053 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ _2 _3 )
# 4111 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 342 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4116 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1051 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ _2 _3 )
# 4121 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 341 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4126 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1049 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkinfix _startpos _endpos _1 _startpos__2_ _endpos__2_ _2 _3 )
# 4131 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_8 : unit) (_startpos__8_ : Lexing.position) (_endpos__8_ : Lexing.position) (_startofs__8_ : int) (_endofs__8_ : int) (_7 : 'tv_expr) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1047 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_cons (rloc _startpos__2_ _endpos__2_) (ghexp _startpos _endpos (Pexp_tuple[_5;_7])) (rloc _startpos _endpos) )
# 4137 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1045 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_cons (rloc _startpos__2_ _endpos__2_) (ghexp _startpos _endpos (Pexp_tuple[_1;_3])) (rloc _startpos _endpos) )
# 4143 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_10 : unit) (_startpos__10_ : Lexing.position) (_endpos__10_ : Lexing.position) (_startofs__10_ : int) (_endofs__10_ : int) (_9 : 'tv_seq_expr) (_startpos__9_ : Lexing.position) (_endpos__9_ : Lexing.position) (_startofs__9_ : int) (_endofs__9_ : int) (_8 : unit) (_startpos__8_ : Lexing.position) (_endpos__8_ : Lexing.position) (_startofs__8_ : int) (_endofs__8_ : int) (_7 : 'tv_seq_expr) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : 'tv_direction_flag) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_seq_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_pattern) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1043 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_for(_3, (merloc _endpos__4_ _5), (merloc _endpos__6_ _7), _6, (merloc _endpos__8_ _9))) _2 )
# 4149 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_seq_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1039 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_while(_3, (merloc _endpos__4_ _5))) _2 )
# 4155 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1036 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_ifthenelse(_3, (merloc _endpos__4_ _5), None)) _2 )
# 4161 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_7 : 'tv_expr) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1032 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_ifthenelse(_3, (merloc _endpos__4_ _5), Some (merloc _endpos__6_ _7))) _2 )
# 4167 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_simple_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_name_tag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1027 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_variant(_1, Some _2)) )
# 4173 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_simple_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_constr_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1025 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_construct(mkrhs _startpos__1_ _endpos__1_ _1, Some _2)) )
# 4179 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_expr_comma_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1023 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_tuple(List.rev _1)) )
# 4185 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_match_cases) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_opt_bar) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1021 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_try(_3, List.rev _6)) _2 )
# 4191 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_match_cases) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_opt_bar) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1018 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_match(_3, List.rev _6)) _2 )
# 4197 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_fun_def) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_newtype) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1015 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_newtype(_3, _4)) _2 )
# 4203 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_fun_def) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_labeled_simple_pattern) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1011 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (l,o,p) = _3 in
        mkexp_attrs _startpos _endpos (Pexp_fun(l, o, p, _4)) _2 )
# 4210 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_match_cases) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_opt_bar) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1008 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_function(List.rev _4)) _2 )
# 4216 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_seq_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_expr_open) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1004 "src/ocaml/typer/preprocess/parser_raw.mly"
   ( let (flag,id,ext) = _3 in
      mkexp_attrs _startpos _endpos (Pexp_open(flag, id, (merloc _endpos__4_ _5))) ext )
# 4223 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_7 : 'tv_seq_expr) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_module_binding_body) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4228 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_ext_attributes) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1002 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_letmodule(mkrhs _startpos__4_ _endpos__4_ _4, _5, (merloc _endpos__6_ _7))) _3 )
# 4233 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_seq_expr) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_let_bindings_no_attrs) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_rec_flag) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 999 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos (Pexp_let(_3, List.rev _4, (merloc _endpos__5_ _6))) _2 )
# 4239 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_simple_labeled_expr_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 997 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp _startpos _endpos (Pexp_apply(_1, List.rev _2)) )
# 4245 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 995 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 4251 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_seq_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_let_bindings) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_let_operator) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2283 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( wrap_exp_attrs _startpos _endpos
      (let_operator _startpos _endpos _1 _3 _5) _2 )
# 4258 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_8 : unit) (_startpos__8_ : Lexing.position) (_endpos__8_ : Lexing.position) (_startofs__8_ : int) (_endofs__8_ : int) (_7 : 'tv_seq_expr) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_seq_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_pattern) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2277 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos
          (Pexp_let (Nonrecursive, [Vb.mk _3 (Fake.(app Lwt.un_stream _5))],
             Fake.(app Lwt.unit_lwt _7)))
          _2
    )
# 4268 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_10 : unit) (_startpos__10_ : Lexing.position) (_endpos__10_ : Lexing.position) (_startofs__10_ : int) (_endofs__10_ : int) (_9 : 'tv_seq_expr) (_startpos__9_ : Lexing.position) (_endpos__9_ : Lexing.position) (_startofs__9_ : int) (_endofs__9_ : int) (_8 : unit) (_startpos__8_ : Lexing.position) (_endpos__8_ : Lexing.position) (_startofs__8_ : int) (_endofs__8_ : int) (_7 : 'tv_seq_expr) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : 'tv_direction_flag) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_seq_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_pattern) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2272 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let expr = Pexp_for (_3, _5, _7, _6, Fake.(app Lwt.un_lwt _9)) in
      Fake.(app Lwt.to_lwt (mkexp_attrs _startpos _endpos expr _2)) )
# 4275 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_seq_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2267 "src/ocaml/typer/preprocess/parser_raw.mly"
  ( let expr = Pexp_while (_3, Fake.(app Lwt.un_lwt _5)) in
    Fake.(app Lwt.to_lwt (mkexp_attrs _startpos _endpos expr _2)) )
# 4282 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_8 : 'tv_seq_expr) (_startpos__8_ : Lexing.position) (_endpos__8_ : Lexing.position) (_startofs__8_ : int) (_endofs__8_ : int) (_7 : unit) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : 'tv_match_cases) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_opt_bar) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2261 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let expr = mkexp_attrs _startpos _endpos
        (Pexp_try (Fake.app Fake.Lwt.in_lwt _3, List.rev _6)) _2 in
      Fake.app (Fake.app Fake.Lwt.finally_ expr) _8 )
# 4290 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_seq_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2258 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Fake.app (Fake.app Fake.Lwt.finally_ _3) _5 )
# 4296 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_match_cases) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_opt_bar) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2254 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkexp_attrs _startpos _endpos
        (Pexp_try(Fake.app Fake.Lwt.in_lwt _3, List.rev _6)) _2 )
# 4303 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2251 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( reloc_exp _startpos _endpos (Fake.app Fake.Lwt.in_lwt _3) )
# 4309 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_match_cases) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_opt_bar) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_seq_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2246 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let expr = mkexp_attrs _startpos _endpos
          (Pexp_match(Fake.app Fake.Lwt.un_lwt _3, List.rev _6)) _2 in
      Fake.app Fake.Lwt.in_lwt expr )
# 4317 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_seq_expr) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_let_bindings) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_rec_flag) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_ext_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2242 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let expr = Pexp_let(_3, List.rev_map (fake_vb_app Fake.Lwt.un_lwt) _4, (merloc _endpos__5_ _6)) in
      Fake.app Fake.Lwt.in_lwt (mkexp_attrs _startpos _endpos expr _2) )
# 4324 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2004 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Downto )
# 4330 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_direction_flag) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2002 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Upto )
# 4336 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_direction_flag) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_ident) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_core_type2) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1668 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_alias(_1, _4)) )
# 4342 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type_no_attr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_core_type2) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1666 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 4348 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type_no_attr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_simple_core_type_no_attr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_core_type_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1808 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 4354 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type_list_no_attr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_simple_core_type_no_attr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1806 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 4360 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type_list_no_attr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_simple_core_type) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_core_type_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1803 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 4366 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_simple_core_type) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1801 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 4372 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_core_type) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_core_type_comma_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1798 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 4378 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type_comma_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_core_type) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1796 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 4384 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type_comma_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_core_type2) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_core_type2) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1679 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_arrow("", _1, _3)) )
# 4390 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_core_type2) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_core_type2) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4395 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1677 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_arrow(_1, _3, _5)) )
# 4400 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_core_type2) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_core_type2) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 381 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4405 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1675 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_arrow("?" ^ _1 , mkoption _2, _4)) )
# 4410 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_core_type2) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_core_type2) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4415 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1673 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_arrow("?" ^ _2 , mkoption _4, _6)) )
# 4420 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_simple_core_type_or_tuple) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1671 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 4426 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type2) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_attribute) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_core_type) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1663 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Typ.attr _1 _2 )
# 4432 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_core_type_no_attr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1661 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 4438 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_core_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_constructor_declaration) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_constructor_declarations) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1529 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 4444 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constructor_declarations) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_constructor_declaration) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1527 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 4450 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constructor_declarations) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_attributes) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_generalized_constructor_arguments) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_constr_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1532 "src/ocaml/typer/preprocess/parser_raw.mly"
    (
      let args,res = _2 in
      Type.constructor (mkrhs _startpos__1_ _endpos__1_ _1) ~args ?res ~loc:(rloc _startpos _endpos) ~attrs:_3
    )
# 4459 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constructor_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 1456 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [] )
# 4465 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constraints) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_constrain) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_constraints) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1454 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 4471 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constraints) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_core_type) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_core_type) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 920 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1, _3 )
# 4477 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constrain_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_core_type) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_core_type) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 917 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1, _3, (rloc _startpos _endpos) )
# 4483 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constrain) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1953 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Lident "true" )
# 4489 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constr_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1951 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Lident "false" )
# 4495 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constr_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1949 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Lident "()" )
# 4501 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constr_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1947 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Lident "[]" )
# 4507 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constr_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_mod_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1945 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 4513 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constr_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1937 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "true" )
# 4519 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constr_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1935 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "false" )
# 4525 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constr_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1932 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "::" )
# 4531 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constr_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1930 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "()" )
# 4537 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constr_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 410 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4542 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1927 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 4547 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constr_ident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 376 "src/ocaml/typer/preprocess/parser_raw.mly"
       (nativeint)
# 4552 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1837 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_nativeint _1 )
# 4557 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 350 "src/ocaml/typer/preprocess/parser_raw.mly"
       (int64)
# 4562 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1835 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_int64 _1 )
# 4567 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 349 "src/ocaml/typer/preprocess/parser_raw.mly"
       (int32)
# 4572 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1833 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_int32 _1 )
# 4577 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 330 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4582 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1831 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_float _1 )
# 4587 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 402 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string * string option)
# 4592 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1829 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (s, d) = _1 in Pconst_string (s, d) )
# 4597 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 310 "src/ocaml/typer/preprocess/parser_raw.mly"
       (char)
# 4602 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1827 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_char _1 )
# 4607 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 348 "src/ocaml/typer/preprocess/parser_raw.mly"
       (int)
# 4612 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1825 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Const_int _1 )
# 4617 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4622 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_ext_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1985 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Ldot(_1, _3) )
# 4627 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_clty_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4632 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1983 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Lident _1 )
# 4637 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_clty_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_type_parameter_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 762 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( List.rev _2 )
# 4643 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_type_parameters) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 760 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [] )
# 4649 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_type_parameters) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_class_type_declaration) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 937 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 4655 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_type_declarations) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_class_type_declaration) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_class_type_declarations) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 935 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 @ _1 )
# 4661 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_type_declarations) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_post_item_attributes) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_class_signature) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4666 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_class_type_parameters) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_virtual_flag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 940 "src/ocaml/typer/preprocess/parser_raw.mly"
    (
      [Ci.mk (mkrhs _startpos__3_ _endpos__3_ _3) _5
         ~virt:_1 ~params:_2
         ~attrs:_6 ~loc:(rloc _startpos _endpos)]
    )
# 4675 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_type_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_class_type) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_simple_core_type_or_tuple_no_attr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 867 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcty _startpos _endpos (Pcty_arrow("", _1, _3)) )
# 4681 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_class_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_simple_core_type_or_tuple_no_attr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4686 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 865 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcty _startpos _endpos (Pcty_arrow(_1, _3, _5)) )
# 4691 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_class_type) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_simple_core_type_or_tuple_no_attr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 381 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4696 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 863 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcty _startpos _endpos (Pcty_arrow("?" ^ _1, mkoption _2, _4)) )
# 4701 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_class_type) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_simple_core_type_or_tuple_no_attr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4706 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 861 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcty _startpos _endpos (Pcty_arrow("?" ^ _2 , mkoption _4, _6)) )
# 4711 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_class_signature) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 859 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 4717 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_class_fields) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_class_self_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 794 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Cstr.mk _1 (List.rev _2) )
# 4723 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_structure) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_class_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 791 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 4729 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_class_type) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_class_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 789 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkclass _startpos _endpos (Pcl_constraint(_2, _4)) )
# 4735 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_class_structure) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 787 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkclass _startpos _endpos (Pcl_structure(_2)) )
# 4741 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_class_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 785 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkclass _startpos _endpos (Pcl_constr(mkrhs _startpos__1_ _endpos__1_ _1, [])) )
# 4747 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_class_longident) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_core_type_comma_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 783 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkclass _startpos _endpos (Pcl_constr(mkloc _4 (rloc _startpos__4_ _endpos__4_), List.rev _2)) )
# 4753 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_simple_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_extension) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 878 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcty _startpos _endpos (Pcty_extension _1) )
# 4759 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_signature) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_attribute) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_class_signature) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 876 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Cty.attr _1 _2 )
# 4765 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_signature) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_class_sig_body) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 874 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcty _startpos _endpos (Pcty_signature _2) )
# 4771 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_signature) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_clty_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 872 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcty _startpos _endpos (Pcty_constr (mkrhs _startpos__1_ _endpos__1_ _1, [])) )
# 4777 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_signature) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_clty_longident) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_core_type_comma_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 870 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcty _startpos _endpos (Pcty_constr (mkloc _4 (rloc _startpos__4_ _endpos__4_), List.rev _2)) )
# 4783 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_signature) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_class_sig_field) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_class_sig_fields) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 891 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 :: _1 )
# 4789 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_sig_fields) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 889 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [] )
# 4795 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_sig_fields) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_floating_attribute) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 907 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkctf _startpos _endpos (Pctf_attribute _1) )
# 4801 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_sig_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (attrs : 'tv_post_item_attributes) (_startpos_attrs_ : Lexing.position) (_endpos_attrs_ : Lexing.position) (_startofs_attrs_ : int) (_endofs_attrs_ : int) (_1 : 'tv_item_extension) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 905 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkctf _startpos _endpos (Pctf_extension _1) ~attrs )
# 4807 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_sig_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (attrs : 'tv_post_item_attributes) (_startpos_attrs_ : Lexing.position) (_endpos_attrs_ : Lexing.position) (_startofs_attrs_ : int) (_endofs_attrs_ : int) (_2 : 'tv_constrain_field) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 903 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkctf _startpos _endpos (Pctf_constraint _2) ~attrs )
# 4813 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_sig_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (attrs : 'tv_post_item_attributes) (_startpos_attrs_ : Lexing.position) (_endpos_attrs_ : Lexing.position) (_startofs_attrs_ : int) (_endofs_attrs_ : int) (_5 : 'tv_poly_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_label) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_private_virtual_flags) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 898 "src/ocaml/typer/preprocess/parser_raw.mly"
    (
      let (p, v) = _2 in
      mkctf _startpos _endpos (Pctf_method (_3, p, v, _5)) ~attrs
    )
# 4822 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_sig_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (attrs : 'tv_post_item_attributes) (_startpos_attrs_ : Lexing.position) (_endpos_attrs_ : Lexing.position) (_startofs_attrs_ : int) (_endofs_attrs_ : int) (_2 : 'tv_value_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 896 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkctf _startpos _endpos (Pctf_val _2) ~attrs )
# 4828 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_sig_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (attrs : 'tv_post_item_attributes) (_startpos_attrs_ : Lexing.position) (_endpos_attrs_ : Lexing.position) (_startofs_attrs_ : int) (_endofs_attrs_ : int) (_2 : 'tv_class_signature) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 894 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkctf _startpos _endpos (Pctf_inherit _2) ~attrs )
# 4834 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_sig_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_class_sig_fields) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_class_self_type) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 881 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Csig.mk _1 (List.rev _2) )
# 4840 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_sig_body) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 886 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mktyp _startpos _endpos (Ptyp_any) )
# 4846 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_self_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_core_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 884 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 4852 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_self_type) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 801 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( ghpat _startpos _endpos (Ppat_any) )
# 4858 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_self_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_core_type) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_pattern) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 799 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkpat _startpos _endpos (Ppat_constraint(_2, _4)) )
# 4864 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_self_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_pattern) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 797 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( reloc_pat _startpos _endpos _2 )
# 4870 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_self_pattern) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4875 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_mod_longident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1990 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Ldot(_1, _3) )
# 4880 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 4885 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1988 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Lident _1 )
# 4890 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_longident) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_class_fun_def) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_labeled_simple_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 767 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (l,o,p) = _1 in mkclass _startpos _endpos (Pcl_fun(l, o, p, _2)) )
# 4896 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_fun_def) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_class_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_labeled_simple_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 765 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (l,o,p) = _1 in mkclass _startpos _endpos (Pcl_fun(l, o, p, _3)) )
# 4902 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_fun_def) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_class_fun_binding) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_labeled_simple_pattern) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 757 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( let (l,o,p) = _1 in mkclass _startpos _endpos (Pcl_fun(l, o, p, _2)) )
# 4908 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_fun_binding) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : 'tv_class_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_class_type) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 755 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkclass _startpos _endpos (Pcl_constraint(_4, _2)) )
# 4914 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_fun_binding) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_class_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 753 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 4920 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_fun_binding) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_class_field) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_class_fields) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 806 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 @ _1 )
# 4926 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_fields) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 804 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [] )
# 4932 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_fields) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_floating_attribute) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 821 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcf _startpos _endpos (Pcf_attribute _1) )
# 4938 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (attrs : 'tv_post_item_attributes) (_startpos_attrs_ : Lexing.position) (_endpos_attrs_ : Lexing.position) (_startofs_attrs_ : int) (_endofs_attrs_ : int) (_1 : 'tv_item_extension) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 819 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcf _startpos _endpos (Pcf_extension _1) ~attrs )
# 4944 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (attrs : 'tv_post_item_attributes) (_startpos_attrs_ : Lexing.position) (_endpos_attrs_ : Lexing.position) (_startofs_attrs_ : int) (_endofs_attrs_ : int) (_2 : 'tv_seq_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 817 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcf _startpos _endpos (Pcf_initializer _2) ~attrs )
# 4950 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (attrs : 'tv_post_item_attributes) (_startpos_attrs_ : Lexing.position) (_endpos_attrs_ : Lexing.position) (_startofs_attrs_ : int) (_endofs_attrs_ : int) (_2 : 'tv_constrain_field) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 815 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcf _startpos _endpos (Pcf_constraint _2) ~attrs )
# 4956 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (attrs : 'tv_post_item_attributes) (_startpos_attrs_ : Lexing.position) (_endpos_attrs_ : Lexing.position) (_startofs_attrs_ : int) (_endofs_attrs_ : int) (_2 : 'tv_method_) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 813 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcf _startpos _endpos (Pcf_method _2) ~attrs )
# 4962 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (attrs : 'tv_post_item_attributes) (_startpos_attrs_ : Lexing.position) (_endpos_attrs_ : Lexing.position) (_startofs_attrs_ : int) (_endofs_attrs_ : int) (_2 : 'tv_value) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 811 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcf _startpos _endpos (Pcf_val _2) ~attrs )
# 4968 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (attrs : 'tv_post_item_attributes) (_startpos_attrs_ : Lexing.position) (_endpos_attrs_ : Lexing.position) (_startofs_attrs_ : int) (_endofs_attrs_ : int) (_4 : 'tv_parent_binder) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_class_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_override_flag) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 809 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkcf _startpos _endpos (Pcf_inherit (_2, _3, _4)) ~attrs )
# 4974 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_field) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_extension) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 780 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkclass _startpos _endpos (Pcl_extension _1) )
# 4980 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_attribute) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_class_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 778 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( Cl.attr _1 _2 )
# 4986 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_class_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_let_bindings_no_attrs) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_rec_flag) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 776 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkclass _startpos _endpos (Pcl_let (_2, List.rev _3, _5)) )
# 4992 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_simple_labeled_expr_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_class_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 774 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkclass _startpos _endpos (Pcl_apply(_1, List.rev _2)) )
# 4998 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_class_fun_def) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 772 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _2 )
# 5004 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_class_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 770 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 5010 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_class_description) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 925 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 5016 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_descriptions) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_class_description) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_class_descriptions) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 923 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 @ _1 )
# 5022 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_descriptions) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : 'tv_post_item_attributes) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : 'tv_class_type) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 5027 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_class_type_parameters) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_virtual_flag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 928 "src/ocaml/typer/preprocess/parser_raw.mly"
    (
      [Ci.mk (mkrhs _startpos__3_ _endpos__3_ _3) _5
         ~virt:_1 ~params:_2
         ~attrs:_6 ~loc:(rloc _startpos _endpos)]
    )
# 5036 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_description) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_class_declaration) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 742 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 )
# 5042 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_declarations) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_class_declaration) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_class_declarations) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 740 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 @ _1 )
# 5048 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_declarations) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_5 : 'tv_post_item_attributes) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_class_fun_binding) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : (
# 367 "src/ocaml/typer/preprocess/parser_raw.mly"
       (string)
# 5053 "src/ocaml/typer/preprocess/parser_raw.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_class_type_parameters) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_virtual_flag) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 746 "src/ocaml/typer/preprocess/parser_raw.mly"
    (
      [Ci.mk (mkrhs _startpos__3_ _endpos__3_ _3) _4
         ~virt:_1 ~params:_2
         ~attrs:_5 ~loc:(rloc _startpos _endpos)]
    )
# 5062 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_class_declaration) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_attributes) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_attribute) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2182 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _1 :: _2 )
# 5068 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_attributes) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 2180 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [] )
# 5074 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_attributes) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : 'tv_payload) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_attr_id) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2166 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( (_2, _3) )
# 5080 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_attribute) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_attr_id) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_single_attr_id) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2163 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkloc (_1 ^ "." ^ _3.txt) (rloc _startpos _endpos))
# 5086 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_single_attr_id) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2161 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( mkloc _1 (rloc _startpos _endpos) )
# 5092 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_attr_id) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_core_type_no_attr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_amper_type_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1778 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( _3 :: _1 )
# 5098 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_amper_type_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_core_type_no_attr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 1776 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( [_1] )
# 5104 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_amper_type_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2055 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "+." )
# 5110 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_additive) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 2053 "src/ocaml/typer/preprocess/parser_raw.mly"
    ( "+" )
# 5116 "src/ocaml/typer/preprocess/parser_raw.ml"
     : 'tv_additive) in
  (raise Not_found : 'tv_with_type_binder * 'tv_with_constraints * 'tv_with_constraint * 'tv_virtual_flag * 'tv_value_type * 'tv_value * 'tv_val_longident * 'tv_val_ident * 'tv_typevar_list * 'tv_type_variance * 'tv_type_variable * 'tv_type_parameters * 'tv_type_parameter_list * 'tv_type_parameter * 'tv_type_longident * 'tv_type_kind * 'tv_type_declarations * 'tv_type_declaration * 'tv_type_constraint * 'tv_toplevel_directives * 'tv_tag_field * 'tv_subtractive * 'tv_structure_tail * 'tv_structure_item * 'tv_structure_head * 'tv_structure * 'tv_strict_binding * 'tv_str_type_extension * 'tv_str_extension_constructors * 'tv_str_exception_declaration * 'tv_single_attr_id * 'tv_simple_pattern_not_ident * 'tv_simple_pattern * 'tv_simple_labeled_expr_list * 'tv_simple_expr * 'tv_simple_core_type_or_tuple_no_attr * 'tv_simple_core_type_or_tuple * 'tv_simple_core_type_no_attr * 'tv_simple_core_type2 * 'tv_simple_core_type * 'tv_signed_constant * 'tv_signature_item * 'tv_signature * 'tv_sig_type_extension * 'tv_sig_extension_constructors * 'tv_sig_exception_declaration * 'tv_seq_expr * 'tv_row_field_list * 'tv_row_field * 'tv_record_expr * 'tv_rec_module_declarations * 'tv_rec_flag * 'tv_private_virtual_flags * 'tv_private_flag * 'tv_primitive_declaration * 'tv_post_item_attributes * 'tv_post_item_attribute * 'tv_poly_type_no_attr * 'tv_poly_type * 'tv_payload * 'tv_pattern_var * 'tv_pattern_semi_list * 'tv_pattern_comma_list * 'tv_pattern * (
# 501 "src/ocaml/typer/preprocess/parser_raw.mly"
      (Parsetree.expression)
# 5121 "src/ocaml/typer/preprocess/parser_raw.ml"
  ) * 'tv_parent_binder * 'tv_package_type_cstrs * 'tv_package_type_cstr * 'tv_package_type * 'tv_override_flag * 'tv_optional_type_variable * 'tv_optional_type_parameters * 'tv_optional_type_parameter_list * 'tv_optional_type_parameter * 'tv_opt_semi * 'tv_opt_default * 'tv_opt_bar * 'tv_opt_ampersand * 'tv_operator * 'tv_open_statement * 'tv_newtype * 'tv_name_tag_list * 'tv_name_tag * 'tv_mutable_flag * 'tv_mty_longident * 'tv_module_type * 'tv_module_rec_declaration * 'tv_module_expr * 'tv_module_declaration * 'tv_module_bindings * 'tv_module_binding_body * 'tv_module_binding * 'tv_mod_longident * 'tv_mod_ext_longident * 'tv_method_ * 'tv_meth_list * 'tv_match_cases * 'tv_match_case * 'tv_lident_list * 'tv_let_pattern * 'tv_let_operator * 'tv_let_bindings_no_attrs * 'tv_let_bindings * 'tv_let_binding_ * 'tv_let_binding * 'tv_lbl_pattern_list * 'tv_lbl_pattern * 'tv_lbl_expr_list * 'tv_lbl_expr * 'tv_labeled_simple_pattern * 'tv_labeled_simple_expr * 'tv_label_var * 'tv_label_longident * 'tv_label_let_pattern * 'tv_label_ident * 'tv_label_expr * 'tv_label_declarations * 'tv_label_declaration * 'tv_label * 'tv_item_extension * (
# 498 "src/ocaml/typer/preprocess/parser_raw.mly"
      (Parsetree.signature)
# 5125 "src/ocaml/typer/preprocess/parser_raw.ml"
  ) * (
# 495 "src/ocaml/typer/preprocess/parser_raw.mly"
      (Parsetree.structure)
# 5129 "src/ocaml/typer/preprocess/parser_raw.ml"
  ) * 'tv_ident * 'tv_generalized_constructor_arguments * 'tv_functor_args * 'tv_functor_arg_name * 'tv_functor_arg * 'tv_fun_def * 'tv_fun_binding * 'tv_floating_attribute * 'tv_field_expr_list * 'tv_field * 'tv_extension_constructor_rebind * 'tv_extension_constructor_declaration * 'tv_extension * 'tv_ext_attributes * 'tv_expr_semi_list * 'tv_expr_open * 'tv_expr_comma_list * 'tv_expr * 'tv_direction_flag * 'tv_core_type_no_attr * 'tv_core_type_list_no_attr * 'tv_core_type_list * 'tv_core_type_comma_list * 'tv_core_type2 * 'tv_core_type * 'tv_constructor_declarations * 'tv_constructor_declaration * 'tv_constraints * 'tv_constrain_field * 'tv_constrain * 'tv_constr_longident * 'tv_constr_ident * 'tv_constant * 'tv_clty_longident * 'tv_class_type_parameters * 'tv_class_type_declarations * 'tv_class_type_declaration * 'tv_class_type * 'tv_class_structure * 'tv_class_simple_expr * 'tv_class_signature * 'tv_class_sig_fields * 'tv_class_sig_field * 'tv_class_sig_body * 'tv_class_self_type * 'tv_class_self_pattern * 'tv_class_longident * 'tv_class_fun_def * 'tv_class_fun_binding * 'tv_class_fields * 'tv_class_field * 'tv_class_expr * 'tv_class_descriptions * 'tv_class_description * 'tv_class_declarations * 'tv_class_declaration * 'tv_attributes * 'tv_attribute * 'tv_attr_id * 'tv_amper_type_list * 'tv_additive)

and menhir_end_marker =
  0

# 2305 "src/ocaml/typer/preprocess/parser_raw.mly"
  

# 5138 "src/ocaml/typer/preprocess/parser_raw.ml"

# 219 "/home/kakadu/.opam/4.02.2+multicore+plugins/lib/menhir/standard.mly"
  


# 5144 "src/ocaml/typer/preprocess/parser_raw.ml"
