(*  Title:      mixr.ML
    Author:     Matej Urbas

MixR: provides the necessary infrastructure for heterogeneous reasoning
          with Spider diagrams in Isabelle.
*)

signature DIABELLI =
sig
  type sd
  type OriginalForm

  (* Indicates a translation error.

     The string describes the error in english.

     The term indicates the location where the translation failed. *)
  exception SD_TRANSLATE_ERROR of string * term

  (* Indicates an error.

     The string describes the error in english. *)
  exception SD_ERROR of string

  (* Indicates a general error (also containing some other cause exceptions).

     The string describes the error in english. *)
  exception SD_GERROR of (string * exn list)

  (* This exception indicates that Speedith exited with a non-zero error code. *)
  exception SD_SPEEDITH_ERROR of string * int

  val traverse_term: term -> string

  val print_props_tac: Proof.context -> tactic




(*==============================================================================
  = External tool invocation
  ============================================================================*)

  (* Escapes the given string for double-quoting in bash.
     Note: This function also puts the string into double-quotes.

     @returns  the escaped string. *)
  val bash_escape: string -> string

  (* Exectues the program (given in the first parameter) with the given command-
     line arguments (second parameter).

     @param  1  the command to execute in bash.

     @param  2  the list of arguments to the command (which will be escaped and
                double-quoted).

     @returns  a pair of a string (the output of the program) and an integer
               (the exit code of execution). *)
  val exec_args: string -> string list -> (string * int)
  
  (* Starts speedith in batch mode. Passes to it the given term (converted to a
     spider diagram first), and instructs it to apply the inference rules given
     by a list of inference description strings.

     @param  1  the term to convert to a spider diagram and pass to Speedith.

     @param  2  [optional] the context theory to use when converting Speedith's
                output formula back to Isabelle/HOL. Use 'NONE' if you do not
                want to provide a theory or if you know that the theory can be
                obtained via 'Context.the_thread_data ()'.

     @param  3  the descriptions of inference rules to apply (in the given
                order) on the spider diagram (given in parameter 1).

     @returns  the transformed term.

     @throws  SD_SPEEDITH  if Speedith exited with a non-zero error code. *)
  val speedith_batch_apply: term -> theory option -> (string*string) list -> term




(*==============================================================================
  = Translation
  ============================================================================*)

  val strict_snf_to_sd: term -> sd
  val lax_snf_to_sd: term -> sd
  val mlsnf_to_sd: term -> sd

  (* This function translates an Isabelle/HOL term of the 'MFOL spider normal'
   form into a spider diagram record suitable for input to Speedith.

   @param  1  A term. Here is an example of a valid term:

                  @{term "(∃s1 s2. distinct[s1, s2] ∧ s1 ∈ A ∩ B ∧ s2 ∈ (A - B) ∪ (B - A)) ⟶ (∃s1 s2. distinct[s1, s2] ∧ s1 ∈ A ∧ s2 ∈ B)"}

   @returns  A record of type 'MixR.sd'. Containing the term translated to
             a spider diagram notation suitable for export to the external
             reasoner.

   @throws  SD_TRANSLATE_ERROR  If the input term could not have been
            translated to a spider diagram.

   @throws  SD_ERROR *)
  val from_snf_to_sd: term -> (sd * OriginalForm)

  (* This function translates an Isabelle/HOL term that is in the 'Meta-Level
     Spider Normal Form' (or ML-SNF) into a spider diagram record, which is
     suitable for input to Speedith.

   @param  1  A term. Here is an example of a valid term:

                  @{term "⋀s1 s2. ⟦s1 ≠ s2; s1 ∈ A; s1 ∈ B; s2 ∈ A; s2 ∉ B⟧ ⟹ ∃s1 s2. s1 ≠ s2 ∧ s1 ∈ A ∧ s2 ∈ B"}

   @returns  A record of type 'MixR.sd'. Containing the term translated to
             a spider diagram notation suitable for export to the external
             reasoner.

   @throws  SD_TRANSLATE_ERROR  If the input term could not have been
            translated to a spider diagram.

   @throws  SD_ERROR *)
  val from_mlsnf_to_sd: term -> sd

  (* This function translates an Isabelle/HOL term of the higher-order spider
     normal form (HO-SNF) into spider diagram notation suitable for input to the
     external diagrammatic reasoner.

     @param  1  A term. Here is an example of a valid term:

                    @{term "(∃f. sd [s, s'] f (f s ∈ A ∩ B ∧ f s' ∈ (A - B) ∪ (B - A)))"}

     @returns  A record of type 'MixR.sd'. Containing the term translated to
               a spider diagram notation suitable for export to the external
               reasoner.

     @throws  SD_TRANSLATE_ERROR  If the input term could not have been
              translated to a spider diagram. *)
  val from_hosnf_to_sd: term -> sd
  
  (* Converts a list of terms to a list of corresponding spider diagrams.
  
     If a term cannot be converted to a spider diagram, then NONE will be
     produced for it.
     
     This method does not throw exceptions.
     
     @param  1  a list of terms to convert to spider diagrams.
     
     @returns  a list of spider diagrams and the forms of the original formulae
               (boxed in an `option`). *)
  val from_terms_to_sds: term list -> (sd * OriginalForm) option list




(*==============================================================================
  = Utility functions
  ============================================================================*)
  (* Returns a list of terms (corresponding to current subgoals in the current
     proof).
     
     @returns (terms, state)
     
       terms - the list of terms that correspond to the current subgoals.
       
       state - the proof state from which we have obtained the terms (this one
               itself has been obtained via `Toplevel.proof_of (Isar.state ())`).
               You can get the context from it via `Proof.context_of state`.
     
     @throws SD_ERROR if we cannot obtain the list of terms for any reason
                      (e.g.: not being in a proof etc.). *)
  val get_goal_terms: unit -> (term list * Proof.state)



(*==============================================================================
  = I3P Communication Routines
  ============================================================================*)

  (* Translates the current goals into spider diagrams and writes the
     translations to the common output via the `tracing` function.
     
     If a subgoal is successfully converted to a spider diagram, the following
     two lines will be printed through the `tracing` function:

        Line 1: < SNF | MLSNF >
        Line 2: [the string representation of the spider diagram]

     The first line indicates the original form of the formula. The second line
     is the actual string representation of the spider diagram.

     If the subgoal is not successfully converted, then only a single line is
     printed and it will contain the string "INVALID".

     *)
  val i3p_write_sds_goals: unit -> unit



(*==============================================================================
  = Random stuff (for testing etc.)
  ============================================================================*)

  val random_tests: string -> (string * int)
  val print_subgoals: unit -> string




(*==============================================================================
  = Proof utility functions
  ============================================================================*)

  (* Replaces a subgoal with an arbitrary term.

     @param  1 the arbitrary term with which to replace sugoal 'i'.

     @param  2 the subgoal (its number) we would like to replace.

     @param  3 the theorem. This argument is provided by the 'apply'
               mechanism (omit it when using apply), e.g.:

         apply (tactic {* MixR.make_subgoal_tac @{term "Trueprop True"} 1 *})
  *)
  val make_subgoal_tac: term -> int -> thm -> thm Seq.seq



(*==============================================================================
  = MixR Reasoning Tactics
  ============================================================================*)
  
  val sd_tac: (string*string) list -> Proof.context -> int -> tactic
end;



structure MixR: DIABELLI =
struct

(*==============================================================================
  = Auxilliary types
  ============================================================================*)

(* Some auxilliary types used in the record that contains all information about
   a spider diagram statement. *)
type spider_name = string;
type contour_name = string;
type zone = (contour_name list * contour_name list);
type region = zone list;
type operator_name = string

(*==============================================================================
  = sd - the main datatype for spider diagrams representation.
  ============================================================================*)

(* The following type is used as the intermediate representation of a spider
   diagram statement. It contains all data needed to draw a spider diagram. *)
datatype sd =
    PrimarySD of {
      spiders: spider_name list,
      habitats: (spider_name * region) list,
      sh_zones: zone list
    }
  | UnarySD of {
      operator: operator_name,
      arg1: sd
    }
  | BinarySD of {
      operator: operator_name,
      arg1: sd,
      arg2: sd
    }
  | NullSD;

(* This is an enumeration of known Isabelle formula formats. The problem is
   that we can convert many types of Isabelle formulae into spider diagrams (the
   same holds in the other direction). We want to preserve the format of the
   formulae as much as possible across translations. This is why we try to
   remember what the original formula form in Isabelle is. *)
datatype OriginalForm =
    SNF     (* Formulae similar to @{term "(∃s1 s2. distinct[s1, s2] ∧ s1 ∈ A ∩ B ∧ s2 ∈ (A - B) ∪ (B - A)) ⟶ (∃s1 s2. distinct[s1, s2] ∧ s1 ∈ A ∧ s2 ∈ B)"}. *)
  | MLSNF   (* Formulae similar to @{term "⋀s1 s2. ⟦s1 ≠ s2; s1 ∈ A; s1 ∈ B; s2 ∈ A; s2 ∉ B⟧ ⟹ ∃s1 s2. s1 ≠ s2 ∧ s1 ∈ A ∧ s2 ∈ B"}. *)
  | INVALID (* A formula that could not have been converted to spider diagrams. *)

(*==============================================================================
  = Exceptions
  ============================================================================*)

exception SD_TRANSLATE_ERROR of (string * term);
exception SD_ERROR of string;
exception SD_GERROR of (string * exn list);
exception SD_SPEEDITH_ERROR of (string * int);
exception SD_SPEEDITH_GERROR of (string * exn list);

(*==============================================================================
  = make_subgoal_tac
  ============================================================================*)

fun make_subgoal_tac prop i st = SUBGOAL (fn (subgoal, _) =>
   let
     val thy = Thm.theory_of_thm st;
     val adhoc_rule = Skip_Proof.make_thm thy (Logic.mk_implies (prop, subgoal));
   in
     compose_tac (false, adhoc_rule, 1) i
   end) i st;

(*==============================================================================
  = from_snf_to_sd
  ============================================================================*)

(* 'collect_ex_spiders' gets a list of all existentially quantified spiders.

  @param   1  a list of spiders to which to append the found spiders (should be
              an empty list--this is just an accumulator list).

  @param   2  the term where to look for existentially quantified spiders.

  @returns `(spNames : string list, t : term)`

           where 'spNames' is a list of the collected names of quantified
           spiders, and 't' is the term over which all the collected spiders
           quantify. *)
fun collect_ex_spiders spNames (@{term "Ex :: ('a::HOL.type => bool) => bool"} $ Abs (spName, _, t)) = (collect_ex_spiders (spName::spNames) t)
  | collect_ex_spiders spNames t = (spNames, t)

(* Makes a list of all conjunctively connected terms in a primary expression
   (i.e., an expression that will get converted into a primary spider
   diagram). These conjunctions are inside the scope of the existentially
   quantified spiders.

   @returns a list of terms (`term list`). *)
fun collect_conjuncts (@{term "op & :: bool => bool => bool"} $ t1 $ t2) = (collect_conjuncts t1) @  (collect_conjuncts t2)
  | collect_conjuncts t = [t]

(* Looks for the conjunctive term that consists of the 'distinct' predicate
   (where the argument to the 'distinct' predicate is a list with all the
   spiders that are existentially quantified in the conjunct scope).

   @returns  a list of terms (without the one containing the 'distinct'
             predicate.

   @throws  SD_TRANSLATE_ERROR
   @throws  SD_ERROR *)
fun find_distinct conjuncts (_::[]) = conjuncts (* No 'distinct' needed for one spider. *)
  | find_distinct conjuncts [] = conjuncts (* Same for zero spiders. *)
  | find_distinct ((@{term "List.distinct :: 'a::HOL.type List.list => bool"} $ spHOLlst)::conjuncts) (spiders : string list) =
      let
          (* We have a distinct predicate here. It must have exactly the same elements as the existentially quantified spiders. *)
          val spidersInDistinct = map (fn (Bound i) => nth spiders i | _ => raise SD_ERROR ("The list in the 'distinct' term should consist only of spiders.")) (HOLogic.dest_list spHOLlst)
          (* Now make sure the two lists are the same. *)
          val listsEqual = eq_list op= ((sort_distinct string_ord spidersInDistinct), (sort_distinct string_ord spiders))
          (*val _ = writeln ("Found 'distinct' with spiders: " ^ (PolyML.makestring spidersInDistinct))*)
      in
          if listsEqual then conjuncts else raise (SD_TRANSLATE_ERROR ("Primary spider diagram extraction failed. Could not find the 'distinct' term for spiders '" ^ (PolyML.makestring spiders) ^ "'.", spHOLlst))
      end
  | find_distinct (c::conjuncts) spiders = c::(find_distinct conjuncts spiders)
  | find_distinct [] spiders = raise (SD_ERROR ("Primary spider diagram extraction failed. Could not find the 'distinct' term for spiders '" ^ (PolyML.makestring spiders) ^ "'."))




(*==============================================================================
  = strict_snf_to_sd
  ============================================================================*)

type StringSet = string Symtab.table
type IntStringMap = string Inttab.table
type StringIntMap = int Symtab.table

type Zone = bool Symtab.table


(* Fetches a value from the map or throws an exception if the value was not
   found.

   @returns `'a` *)
fun Inttab_get_one (tbl : 'a Inttab.table) (key : int) =
  case (Inttab.lookup tbl key) of
      SOME theval => theval
    | NONE => raise (SD_ERROR "Could not find the entry in te map.");


(* Turns a list into a map of indices to the elements. The first element gets
   the index 0.

   @returns  `'a Inttab.table` *)
fun to_index_map (xs : 'a list) =
  let
      fun impl (e::es) i themap = impl es (i + 1) (Inttab.update (i, e) themap)
        | impl [] i themap = themap
  in
      impl xs 0 Inttab.empty
  end;


(* This function traverses through all the subterms of the given term list and
   returns all contours it finds.

   @param  1  a `term list` which to search through for all the mentioned
              contours.

   @returns  `contours : StringSet * count : int`, where the keys of
             `countours` are the names of contours and the values are the=
             indices (starting from 0 and increasing in the order in which they
             are mentioned). The `count` return value is to the number of all
             mentioned contours. *)
fun get_contours (terms : term list) =
    let
        val contours = Unsynchronized.ref Symtab.empty
        val count = Unsynchronized.ref 0
        fun term_visitor (Free (cname, _)) @{typ "'a set"} _ =
            let
                val _ = contours := Symtab.update (cname, cname) (!contours)
            in () end
          | term_visitor _ _ _ = ()
        fun list_traverse ((t::ts) : term list) = let val _ = fold_term_types (term_visitor) t () val _ = list_traverse ts in () end
          | list_traverse [] = ()
        val _ = list_traverse terms
        (* Count all the contours. *)
        val _ = Symtab.forall (fn _ => let val _ = count := (!count) + 1 in true end) (!contours)
    in
        (!contours, !count)
    end;

(* Adds the in- and out-contours to the "underspecified zone", by checking
   that no contour is both in the in- and the out-contours. *)
fun add_to_zone in_contours out_contours underspec_zone =
    let
        val ins = List.foldl (fn (c, tbl) => Symtab.update (c, true) tbl) underspec_zone in_contours
        val inouts = List.foldl (fn (c, tbl) =>
                                   case (Symtab.lookup tbl c) of
                                       SOME true => raise (SD_ERROR ("The contour" ^ c ^ " has been specified as both an in- and out-contour."))
                                     | _ => Symtab.update (c, false) tbl) ins out_contours
    in
        inouts
    end;

(* Constructs a `zone`, from the given `Zone` table. *)
fun zonetbl_to_zone (zone : Zone) =
    let
        fun fold_ins (c, isin) cins = if isin then (c::cins) else cins
        fun fold_outs (c, isin) couts = if isin then couts else (c::couts)
        val incontours = Symtab.fold_rev fold_ins zone []
        val outcontours = Symtab.fold_rev fold_outs zone []
    in
        (incontours, outcontours)
    end

(* Constructs a valid SD region 'R' such that:

     `sd_region_sem R = (⋂ in_contours) - (⋃ out_contours)` *)
fun get_super_region in_contours out_contours all_contours =
    let
        val underspec_zone = add_to_zone in_contours out_contours Symtab.empty
        val other_contours = List.filter (fn c => not (Symtab.defined underspec_zone c)) (Symtab.keys all_contours)
        fun impl_super_region (c::cs) curzone =
            let
            in
                (impl_super_region cs (Symtab.update_new (c, true) curzone)) @
                (impl_super_region cs (Symtab.update_new (c, false) curzone))
            end
          | impl_super_region [] curzone = [curzone]
        val sregiontbls = impl_super_region other_contours underspec_zone
        val sregion = List.map (fn z => zonetbl_to_zone z) sregiontbls
    in
        sregion
    end;

local

    fun get_zone_outs (Free (s, @{typ "'a set"})) all_contours = if (Symtab.defined all_contours s) then [s] else raise (SD_ERROR ("Hit an unknown contour '" ^ s ^ "'."))
      | get_zone_outs (@{term "sup :: 'a set => 'a set => 'a set"} $ t1 $ t2) all_contours = (get_zone_outs t1 all_contours) @ (get_zone_outs t2 all_contours)
      | get_zone_outs t _ = raise (SD_TRANSLATE_ERROR ("Could not determine the 'out' part of the zone. Expected a union of sets.", t))

    fun get_zone_ins (Free (s, @{typ "'a set"})) all_contours = if (Symtab.defined all_contours s) then [s] else raise (SD_ERROR ("Hit an unknown contour '" ^ s ^ "'."))
      | get_zone_ins (@{term "inf :: 'a set => 'a set => 'a set"} $ t1 $ t2) all_contours = (get_zone_ins t1 all_contours) @ (get_zone_ins t2 all_contours)
      | get_zone_ins t _ = raise (SD_TRANSLATE_ERROR ("Could not determine the 'in' part of the zone. Expected an intersetion of sets.", t))

    fun get_zones (t as Free (s, @{typ "'a set"})) all_contours contour_count =
        let
            val region = if Symtab.defined all_contours s
                         then get_super_region [s] [] all_contours
                         else raise (SD_TRANSLATE_ERROR ("The set " ^ s ^ " is unknown.", t))
        in
            region
        end
      | get_zones (@{term "minus :: 'a set => 'a set => 'a set"} $ t1 $ t2) all_contours contour_count = [(get_zone_ins t1 all_contours, get_zone_outs t2 all_contours)] (* Handle the canonical format. *)
      | get_zones (@{term "inf :: 'a set => 'a set => 'a set"} $ t1 $ t2) all_contours contour_count = get_super_region ((get_zone_ins t1 all_contours) @ (get_zone_ins t2 all_contours)) [] all_contours
      | get_zones t all_contours contour_count = raise (SD_TRANSLATE_ERROR ("Could not extract the zone. The zone is of an unknown format.", t))
in
    fun get_region (@{term "sup :: 'a set => 'a set => 'a set"} $ t1 $ t2) all_contours contour_count =
        let
            val lregions = (get_region t1 all_contours contour_count)
            val rregions = (get_region t2 all_contours contour_count)  (* Handle the union format. *)
        in
            lregions @ rregions
        end
      | get_region t all_contours contour_count = get_zones t all_contours contour_count
end;


(* Extracts spiders' habitats from the given terms. This function throws an
   exception if for any reason the habitats could not have been extracted (i.e.,
   if an unknown spider was referenced, if the region was invalid or of an
   unknown format, if a habitat of a spider is mentioned more than once etc.).

   @param  1  the terms (that were conjunctively connected) from which to
              extract the habitats.

   @param  2  a `StringSet` of all mentioned contours (this is needed to calculate the
              in- and out-contours of a zone if it was specified in an
              incomplete manner).

   @param  3  the `IntStringMap` of all spiders in this primary spider diagram.
              This map maps spider's names to their bound index.

   @returns  a pair `(other_terms : term list, habitats : region Symtab.table)`
             where `other_terms` is a list of terms that were not habitat
             specifications (all the remaining terms from `param 1`), and
             `habitats` is a list of spiders with their habitat regions. *)
fun get_habitats (((t as (@{term "op : :: 'a => 'a set => bool"} $ (Bound spiderIndex) $ region_term))::terms) : term list) (contours : StringSet) contours_count (spiders : IntStringMap) =
    let
        val spider = (Inttab_get_one spiders spiderIndex) handle ex => raise (SD_GERROR ("The bound variable could not have been found in the list of spiders.", [ex]))
        val (other_terms, habs) = get_habitats terms contours contours_count spiders

        val cur_habitat = if Symtab.defined habs spider then raise (SD_TRANSLATE_ERROR ("The habitat for the spider " ^ spider ^ " has been specified more than once.", t))
                                                        else get_region region_term contours contours_count
    in
        (other_terms, Symtab.update_new (spider, cur_habitat) habs) handle (ex as (Symtab.DUP key)) => raise (SD_GERROR ("Duplicate region found for spider \"" ^ key ^ "\"", [ex]))
    end
 |  get_habitats (t::terms) contours contours_count spiders =
    let
        val (other_terms, habitats) = get_habitats terms contours contours_count spiders
    in
        (t::other_terms, habitats)
    end
 |  get_habitats [] _ _ _ = ([], Symtab.empty);


local
  (* 'from_snf_to_sd_inner' expects a list of terms connected with conjunctions. Each of the
     conjunctions can be either the 'distinct spiders' term, a habitat
     statement or a shaded zone statement.

     There must be exactly one 'distinct spiders' term and 'spiders' should be
     the same as the first parameter to this function.

     This function produces a primary spider diagram (see 'PrimarySD').

     @param  1  the list of spiders that participate in this primary spider
                diagram.

     @param  2  the term that should contain the whole primary spider diagram.

     @param  3  indicates whether a strict or lax conversion should be
                performed.

     @returns   a primary spider diagram (see PrimarySD {...}). *)
   fun snf_to_sd_primary (spiders : string list) (t : term) (strict : bool) =
   let
       (* Extract all conjunctively connected terms. *)
       (* Check that amongst these terms there is one 'distinct' term which
          satisfies the condition, and remove this term and return the
          new list of conjuncts. Otherwise raise an exception. *)
       val terms = (t |> collect_conjuncts |> find_distinct) (rev spiders)
       (* Now find all the contours that are in one way or the other mentioned
          in this formula (they will be free variables of type `'a set`).

          This is a sorted list of contour names. *)
       val (contours, contours_count) = get_contours terms
       (* Create a map of indices to spiders. This is for faster spider lookup. *)
       val spidermap = to_index_map spiders
       (* Get habitats. *)
       val (other_terms, habitats) = get_habitats terms contours contours_count spidermap
       (* From the remaining terms extract the habitats of spiders and
          remove all corresponding terms. *)
       (* Now find all 'shaded zone' terms and remove those too. *)
       (* TODO: Implement the shaded zones! *)
       (* If any terms remain, raise an error. *)
       val _ = case other_terms of [] => () | _ => raise (SD_ERROR ("Unexpected terms found in the formula."))
   in
       PrimarySD { spiders = spiders, habitats = Symtab.dest habitats, sh_zones = [] }
   end


  (* Expects an outer term, which may be of any of the following forms:

       A  &  B
       A  |  B
       A --> B
       A <-> B
       ¬A (not yet implemented)
       True
       Trueprop A

     @param  1  the term to convert to a spider diagram.

     @param  2  indicates whether a strict or a lax conversion should be done.

     @returns  a spider diagram of type `sd`.
  *)
  fun snf_to_sd_outer (@{term "op --> :: bool => bool => bool"} $ t1 $ t2) (strict : bool) = BinarySD { operator = "op -->", arg1 = snf_to_sd_outer t1 strict, arg2 = snf_to_sd_outer t2 strict }
    | snf_to_sd_outer (@{term "op | :: bool => bool => bool"} $ t1 $ t2) strict = BinarySD { operator = "op |", arg1 = snf_to_sd_outer t1 strict, arg2 = snf_to_sd_outer t2 strict }
    | snf_to_sd_outer (@{term "op & :: bool => bool => bool"} $ t1 $ t2) strict = BinarySD { operator = "op &", arg1 = snf_to_sd_outer t1 strict, arg2 = snf_to_sd_outer t2 strict }
    | snf_to_sd_outer (@{term "op = :: bool => bool => bool"} $ t1 $ t2) strict = BinarySD { operator = "op <-->", arg1 = snf_to_sd_outer t1 strict, arg2 = snf_to_sd_outer t2 strict }
    | snf_to_sd_outer (@{term "Ex :: ('a::HOL.type => bool) => bool"} $ Abs (spName, _, t)) strict =
      let
          val (spiders, inner_term) = collect_ex_spiders [spName] t
      in
          (snf_to_sd_primary spiders inner_term strict)
      end
    | snf_to_sd_outer (Const ("==>", @{typ "prop => prop => prop"}) $ t1 $ t2) (strict : bool) = BinarySD { operator = "op -->", arg1 = snf_to_sd_outer t1 strict, arg2 = snf_to_sd_outer t2 strict }
    | snf_to_sd_outer (@{term "Trueprop :: bool => prop"} $ t) strict = snf_to_sd_outer t strict
    | snf_to_sd_outer (@{term "True"}) strict = NullSD
    | snf_to_sd_outer t _ = raise (SD_TRANSLATE_ERROR ("Could not translate to spider diagrams. Unexpected snf_to_sd_outer term.", t))
in
  fun strict_snf_to_sd t = snf_to_sd_outer t true
  fun lax_snf_to_sd t = snf_to_sd_outer t false
end;

(* Gets a list of all meta-universally quantified spiders.

  @param   1  a list of spiders to which to append the found spiders (should be
              an empty list--this is just an accumulator list).

  @param   2  the term where to look for existentially quantified spiders.

  @returns `(spNames : string list, t : term)`

           where 'spNames' is a list of the collected names of quantified
           spiders, and 't' is the term over which all the collected spiders
           quantify. *)
fun collect_ml_spiders spNames (@{term "all :: ('a => prop) => prop"} $ Abs (spName, _, tInner)) = collect_ml_spiders (spNames @ [spName]) tInner
  | collect_ml_spiders spNames t = (spNames, t)

(* Collects all meta-implication antecedents together with the conclusion.

   Reads terms of the form "[| t1; t2; ...; tN |] ==> tC" and

   @returns `(terms : term list, conclusion : term)` where terms = [ t1, t2,
            ..., tN ] and conclusion = tC.

*)
fun collect_ml_imp (ts : term list) (t : term as (Const ("==>", @{typ "prop => prop => prop"}) $ (Const ("HOL.Trueprop", @{typ "HOL.bool => prop"}) $ tLeft) $ tRight)) = collect_ml_imp (tLeft :: ts) tRight
  | collect_ml_imp ts (@{term "Trueprop :: bool => prop"} $ t) = (ts, t)
  | collect_ml_imp ts t = raise (SD_TRANSLATE_ERROR ("Could not translate the ML formula. Unexpected term.", t))

local
    datatype 'a in_out = IN of 'a | OUT of 'a

    fun get_sp_in_out_set spiders (@{term "HOL.Not :: bool => bool"} $ (@{term "Set.member :: 'a => 'a set => bool"} $ Bound sp $ (Free (c, @{typ "'a set"})))) = SOME (OUT (nth (rev spiders) sp, c))
      | get_sp_in_out_set spiders (@{term "Set.member :: 'a => 'a set => bool"} $ Bound sp $ (Free (c, @{typ "'a set"}))) = SOME (IN (nth (rev spiders) sp, c))
      | get_sp_in_out_set spiders t = NONE

in
    fun get_sp_in_out_sets (spiders : string list) (t::ts) ins outs trest =
        let
            val sio = get_sp_in_out_set spiders t
        in
            case (sio) of
                NONE => get_sp_in_out_sets spiders ts ins outs (t::trest)
              | SOME (IN a) => get_sp_in_out_sets spiders ts (a::ins) outs trest
              | SOME (OUT a) => get_sp_in_out_sets spiders ts ins (a::outs) trest
        end
      | get_sp_in_out_sets (spiders : string list) [] ins outs trest = (ins, outs, trest)
end;



fun get_habitats_from_cons spiders spInCons spOutCons =
    let
        fun get_all_contours ((_, c)::spCons) cons = get_all_contours spCons (c::cons)
          | get_all_contours [] cons = cons
        val all_contours = Ord_List.make string_ord (get_all_contours spOutCons (get_all_contours spInCons []))
        fun sp_habitat_from_in_out_cons sp =
          let
              fun filter_for_sp (s, c) = if s = sp then SOME c else NONE
              val inCons = Ord_List.make string_ord (List.mapPartial filter_for_sp spInCons)
              val outCons = Ord_List.make string_ord (List.mapPartial filter_for_sp spOutCons)
              val otherCons = Ord_List.subtract string_ord all_contours (Ord_List.union string_ord inCons outCons)
              fun habitat_from_in_out_other inc outc (c::others) = (habitat_from_in_out_other (c::inc) outc others) @ (habitat_from_in_out_other inc (c::outc) others)
                | habitat_from_in_out_other inc outc [] = [(inc, outc)]
          in
              (sp, habitat_from_in_out_other inCons outCons otherCons)
          end
    in
        map sp_habitat_from_in_out_cons spiders
    end

(* MLSNF to SD conversion methods. *)
local
in
    fun mlsnf_to_sd (t as (@{term "all :: ('a => prop) => prop"} $ Abs (spName, _, tInner))) =
        let
            val (spiders, inner_term) = collect_ml_spiders [spName] tInner
            val (antecedentTerms, consequentTerm) = collect_ml_imp [] inner_term
            val (contours, contours_count) = get_contours antecedentTerms
            val nestedSD = lax_snf_to_sd consequentTerm
            (* TODO: Also allow inequalities instead of just distinct. *)
            val withoutDistinct = find_distinct antecedentTerms spiders
            (* Create a map of indices to spiders. This is for faster spider lookup. *)
            val spidermap = to_index_map spiders
            val (spInCons, spOutCons, otherTerms) = get_sp_in_out_sets spiders withoutDistinct [] [] []
            (* TODO: Extract shaded zones from otherTerms. *)
            val _ = case otherTerms of [] => true | (t::ts) => raise (SD_TRANSLATE_ERROR ("Could not translate the meta-level formula. Some unknown terms were found.", t))
                        val psd = PrimarySD {spiders = spiders, habitats = get_habitats_from_cons spiders spInCons spOutCons, sh_zones = []}
        in
            if otherTerms = [] then BinarySD { operator = "op -->", arg1 = psd, arg2 = nestedSD }
                               else raise (SD_TRANSLATE_ERROR ("Primary spider diagram extraction from a meta-level formula failed. The fomula is not of the expected format.", t))
        end
      | mlsnf_to_sd t = raise (SD_TRANSLATE_ERROR ("Could not translate to spider diagrams. Not an SNF Meta-Level formula.", t))
end

(* TODO: To make the translation spider type-independent, I could use the
'const_name' antiquotation (e.g.: @{const_name "Ex"}) and store the type of the
first spider. Then check other constructed types based on this. *)

local

  fun get_zone_outs (Free (s, @{typ "'a set"}))  = [s]
    | get_zone_outs (@{term "sup :: 'a set => 'a set => 'a set"} $ t1 $ t2) = (get_zone_outs t1) @ (get_zone_outs t2)
    | get_zone_outs t = raise (SD_TRANSLATE_ERROR ("Could not determine the 'out' part of the zone. Expected a union of sets.", t))

  fun get_zone_ins (Free (s, @{typ "'a set"}))  = [s]
    | get_zone_ins (@{term "inf :: 'a set => 'a set => 'a set"} $ t1 $ t2) = (get_zone_ins t1) @ (get_zone_ins t2)
    | get_zone_ins t = raise (SD_TRANSLATE_ERROR ("Could not determine the 'in' part of the zone. Expected an intersetion of sets.", t))

  fun get_zone (Free (s, @{typ "'a set"})) = ([s], [])
    | get_zone (@{term "inf :: 'a set => 'a set => 'a set"} $ t1 $ t2) = ((get_zone_ins t1) @ (get_zone_ins t2), [])
    | get_zone (@{term "minus :: 'a set => 'a set => 'a set"} $ t1 $ t2) = ( get_zone_ins t1, get_zone_outs t2 )
    | get_zone t = raise (SD_TRANSLATE_ERROR ("Could not extract the zone. The zone is of an unknown format.", t))

  fun get_region (Free (s, @{typ "'a set"})) = [([s], [])]
    | get_region (@{term "sup :: 'a set => 'a set => 'a set"} $ t1 $ t2) = [ get_zone t1, get_zone t2 ]
    | get_region t = [ get_zone t ]

  (* Extracts (from the list of inner conjunct terms) a list of habitats (see the
     'habitats' attribute of the PrimarySD constructor).

     @param   conjuncts    a list of terms that are in the scope of the
                           existenatially quantified spiders (the latter are
                           provided in the second parameter).

     @param   spiders      a list of spider names (which are existentially
                           quantified).

     @returns a pair (conjs, habs) where 'conjs' are those terms that do not
              contain a habitat definition, and 'habs' is the list of extracted
              habitats.
  *)
  fun get_habitats ((@{term "op : :: 'a => 'a set => bool"} $ (Bound spiderIndex) $ region)::conjuncts) spiders =
      let
          val hab = (nth (rev spiders) spiderIndex, get_region region)
          val (retConjs, habs) = get_habitats conjuncts spiders
      in
          (retConjs, hab::habs)
      end
    | get_habitats (t::conjuncts) spiders =
      let
          val (retConjs, habs) = get_habitats conjuncts spiders
      in
          (t::retConjs, habs)
      end
    | get_habitats [] _ = ([], [])

  (* 'from_snf_to_sd_inner' expects a list of terms connected with conjunctions. Each of the
     conjunctions can be either the 'distinct spiders' term, a habitat
     statement or a shaded zone statement.

     There must be exactly one 'distinct spiders' term and 'spiders' should be
     the same as the first parameter to this function.

     This function produces a primary spider diagram (see 'PrimarySD').

     @param  1  the list of spiders that participate in this primary spider
                diagram.

     @param  2  the term that should contain the whole primary spider diagram.

     @returns   a primary spider diagram (see PrimarySD {...}). *)
  fun from_snf_to_sd_inner (spiders : string list) (t : term) =
      let
          (* Extract all conjunctively connected terms. *)
          (* Check that amongst those terms is one 'distinct' term which
             satisfies the condition, and remove this term and return the
             new list of conjuncts. Otherwise raise an exception. *)
           val (_, habitats) = spiders |> (((collect_conjuncts t, spiders) |-> find_distinct) |> get_habitats)
           (* From the remaining terms extract the habitats of spiders and
             remove all corresponding terms. *)
           (* Now find all 'shaded zone' terms and remove those too. *)
           (* TODO: Implement! *)
           (* If any terms remain, raise an error. *)
           (*val _ = writeln ("Extracting a primary diagram: " ^ PolyML.makestring habitats)*)
      in
          PrimarySD { spiders = spiders, habitats = habitats, sh_zones = [] }
      end

  fun from_snf_to_sd_outer (@{term "op --> :: bool => bool => bool"} $ t1 $ t2) = BinarySD { operator = "op -->", arg1 = from_snf_to_sd_outer t1, arg2 = from_snf_to_sd_outer t2 }
    | from_snf_to_sd_outer (@{term "op | :: bool => bool => bool"} $ t1 $ t2) = BinarySD { operator = "op |", arg1 = from_snf_to_sd_outer t1, arg2 = from_snf_to_sd_outer t2 }
    | from_snf_to_sd_outer (@{term "Ex :: ('a::HOL.type => bool) => bool"} $ Abs (spName, _, t)) =
      let
          val (spiders, inner_term) = collect_ex_spiders [spName] t
          (*val _ = raise (SD_TRANSLATE_ERROR (PolyML.makestring spiders, t))*)
      in
        (from_snf_to_sd_inner spiders inner_term)
      end
    (*| from_snf_to_sd_outer (t as (@{term "all :: ('a => prop) => prop"} $ Abs _)) = from_mlsnf_to_sd_outer t*)
    | from_snf_to_sd_outer (@{term "Trueprop :: bool => prop"} $ t) = from_snf_to_sd_outer t
    | from_snf_to_sd_outer (@{term "True"}) = NullSD
    | from_snf_to_sd_outer t = raise (SD_TRANSLATE_ERROR ("Could not translate to spider diagrams. Unexpected from_snf_to_sd_outer term.", t))

    and

      from_mlsnf_to_sd_outer (t as (@{term "all :: ('a => prop) => prop"} $ Abs (spName, _, tInner))) =
      let
          val (spiders, inner_term) = collect_ml_spiders [spName] tInner
          val (antecedentTerms, consequentTerm) = collect_ml_imp [] inner_term
          val nestedSD = from_snf_to_sd_outer consequentTerm
          val withoutDistinct = find_distinct antecedentTerms spiders
          val (spInCons, spOutCons, otherTerms) = get_sp_in_out_sets spiders withoutDistinct [] [] []
          (* TODO: Extract shaded zones from otherTerms. *)
          val _ = case otherTerms of [] => true | (t::ts) => raise (SD_TRANSLATE_ERROR ("Could not translate the meta-level formula. Some unknown terms were found.", t))
          val psd = PrimarySD {spiders = spiders, habitats = get_habitats_from_cons spiders spInCons spOutCons, sh_zones = []}
      in
          if otherTerms = [] then BinarySD { operator = "op -->", arg1 = psd, arg2 = nestedSD }
                             else raise (SD_TRANSLATE_ERROR ("Primary spider diagram extraction from a meta-level formula failed. The fomula is not of the expected format.", t))
      end
    | from_mlsnf_to_sd_outer t = raise (SD_TRANSLATE_ERROR ("Could not translate to spider diagrams. Not an SNF Meta-Level formula.", t))
in
  fun from_snf_to_sd t = (strict_snf_to_sd t, SNF) handle e => ((from_mlsnf_to_sd_outer t, MLSNF) handle e2 => raise SD_SPEEDITH_GERROR ("Translation from Isabelle/HOL to spider diagrams failed.", [e, e2]))
  fun from_mlsnf_to_sd t = from_mlsnf_to_sd_outer t
end;




(*==============================================================================
  = from_hosnf_to_sd
  ============================================================================*)

local
  fun get_spiders (@{term "Cons :: 'a => 'a list => 'a list"} $ Free (spider, @{typ "'a"}) $ xs) = (spider :: get_spiders xs)
    | get_spiders (@{term "Nil :: 'a list"}) = []
    | get_spiders t = raise (SD_TRANSLATE_ERROR ("Could not determine the set of spiders. The list of spiders contains an invalid term.", t))

  fun get_zone_outs (Free (s, @{typ "'b set"}))  = [s]
    | get_zone_outs (@{term "sup :: 'b set => 'b set => 'b set"} $ t1 $ t2) = (get_zone_outs t1) @ (get_zone_outs t2)
    | get_zone_outs t = raise (SD_TRANSLATE_ERROR ("Could not determine the 'out' part of the zone. Expected a union of sets.", t))

  fun get_zone_ins (Free (s, @{typ "'b set"}))  = [s]
    | get_zone_ins (@{term "inf :: 'b set => 'b set => 'b set"} $ t1 $ t2) = (get_zone_ins t1) @ (get_zone_ins t2)
    | get_zone_ins t = raise (SD_TRANSLATE_ERROR ("Could not determine the 'in' part of the zone. Expected an intersetion of sets.", t))

  fun get_zone (Free (s, @{typ "'b set"})) = ([s], [])
    | get_zone (@{term "inf :: 'b set => 'b set => 'b set"} $ t1 $ t2) = ((get_zone_ins t1) @ (get_zone_ins t2), [])
    | get_zone (@{term "minus :: 'b set => 'b set => 'b set"} $ t1 $ t2) = ( get_zone_ins t1, get_zone_outs t2 )
    | get_zone t = raise (SD_TRANSLATE_ERROR ("Could not extract the zone. The zone is of an unknown format.", t))

  fun get_region (Free (s, @{typ "'b set"})) = [([s], [])]
    | get_region (@{term "sup :: 'b set => 'b set => 'b set"} $ t1 $ t2) = [ get_zone t1, get_zone t2 ]
    | get_region t = [ get_zone t ]

  fun get_habitats (@{term "op & :: bool => bool => bool"} $ t1 $ t2) = (get_habitats t1) @ (get_habitats t2)
    | get_habitats (@{term "op : :: 'b => 'b set => bool"} $ (Bound _ $ Free (spider, @{typ "'a"})) $ t) = [(spider, get_region t)]
    | get_habitats t = raise (SD_TRANSLATE_ERROR ("Could not determine spider habitats. The habitat predicate contains an invalid term.", t))

  fun inner_term_to_sd (Const ("Playground.sd", @{typ "'a List.list => ('a => 'b) => bool => bool"}) $ spiders $ _ $ predicate) = PrimarySD {spiders = get_spiders spiders, habitats = get_habitats predicate, sh_zones = []}
    | inner_term_to_sd t = raise (SD_TRANSLATE_ERROR ("Could not translate to spider diagrams. Unexpected term.", t))
in
  fun from_hosnf_to_sd (@{term "op --> :: bool => bool => bool"} $ t1 $ t2) = BinarySD { operator = "op -->", arg1 = from_hosnf_to_sd t1, arg2 = from_hosnf_to_sd t2 }
    (*| from_hosnf_to_sd (@{term "op | :: (('a => 'b) => bool) => bool"} $ Abs (_, _, t)) = inner_term_to_sd t*)
    | from_hosnf_to_sd (@{term "Ex :: (('a => 'b) => bool) => bool"} $ Abs (_, _, t)) = inner_term_to_sd t
    (*| from_hosnf_to_sd (@{term "Ex :: ('a => bool) => bool"} $ Abs (s, _, t)) = inner_term_to_sd t*)
    | from_hosnf_to_sd t = raise (SD_TRANSLATE_ERROR ("Could not translate to spider diagrams. Unexpected outer term.", t))
end;

(*==============================================================================
  = traverse_term
  ============================================================================*)

(* Just having some fun traversing terms and making a string out of them. *)
fun traverse_term (t1 $ t2) = "[ " ^ (traverse_term t1) ^ " $ " ^ (traverse_term t2) ^ " ]"
  | traverse_term (Const (s, _)) = "Const = '" ^ s ^ "'"
  | traverse_term (Free (s, _)) = "Free = '" ^ s ^ "'"
  | traverse_term (Var ((s, i), _)) = "Var = '" ^ s ^ "' (" ^ Int.toString i ^ ")"
  | traverse_term (Bound i) = "Bound = " ^ Int.toString i
  | traverse_term (Abs (s, _, t)) = "[ Abs '" ^ s ^ "': " ^ (traverse_term t) ^ " ]";

(*==============================================================================
  = print_props_tac
  ============================================================================*)
  
fun print_props_tac ctxt st =
  let
      val _ = writeln (traverse_term (hd (Thm.prems_of st)))
      val _ = tracing (implode [ "Full prop: ", Pretty.string_of (Syntax.pretty_term ctxt (Thm.full_prop_of st)) ])
      val _ = tracing (implode [ "Prop: ", Pretty.string_of (Syntax.pretty_term ctxt (Thm.prop_of st)) ])
      val _ = tracing (implode ([ "Prems: " ] @ (map (fn t => Pretty.string_of (Syntax.pretty_term ctxt t)) (Thm.prems_of st))))
      val _ = tracing (implode [ "Concl: ", Pretty.string_of (Syntax.pretty_term ctxt (Thm.concl_of st)) ])
  in
      all_tac st
  end;

(*==============================================================================
  = bash_escape
  ============================================================================*)

local
  fun bash_escape_for_dq chr = case chr of
                             #"\"" => "\\\""
                           | #"\\" => "\\\\"
                           | #"$" => "\\$"
                           | #"!" => "\\!"
                           | chr   => Char.toString chr;
  fun bash_quote_dq str = "\"" ^ (String.translate bash_escape_for_dq str) ^ "\""
in
  fun bash_escape str = bash_quote_dq str
end

(*==============================================================================
  = exec_args
  ============================================================================*)

fun exec_args cmd args =
  let
      val qArgs = List.foldl (fn (s2, s1) => s1 ^ " " ^ s2) "" (map bash_escape args)
      val _ = tracing (cmd ^ qArgs)
  in
      Isabelle_System.bash_output (cmd ^ qArgs)
  end

(*==============================================================================
  = speedith_batch_apply
  ============================================================================*)

val DIABELLI_JAVA_PATH = "DIABELLI_JAVA_PATH"
val DIABELLI_SPEEDITH_PATH = "DIABELLI_SPEEDITH_PATH"
val DIABELLI_SPEEDITH_OUTPUT_FORMAT = "DIABELLI_SPEEDITH_OUTPUT_FORMAT"

fun speedith_batch_apply t othy args =
  let
      val args_prep = map (fn (x, y) => ("-" ^ x, y)) args
      val args_prep2 = List.foldr (fn ((x, y), xs) => x::(y::xs)) [] args_prep
      val (sd, originalForm) = from_snf_to_sd t
      val _ = tracing ("Invoking Speedith with the spider diagram: " ^ (PolyML.makestring sd))
      val retVal as (sout, ecode) = exec_args
                            (getenv DIABELLI_JAVA_PATH)
                                      ([
                                         "-jar", getenv DIABELLI_SPEEDITH_PATH,
                                         "-b",
                                         "-of", getenv DIABELLI_SPEEDITH_OUTPUT_FORMAT,
                                         "-sd", PolyML.makestring (sd)
                                       ] @ ["-ofa", (case originalForm of MLSNF => "ml=true" | SNF => "ml=false") ^ (",useXSymbols=true")]
                                       @ args_prep2)
      val _ = tracing ("Speedith returned: " ^ sout)
      fun read_term (Context.Theory ctxt) formula = (writeln "Theory"; Syntax.read_term_global ctxt formula)
        | read_term (Context.Proof ctxt) formula = (writeln "Proof"; Syntax.read_term ctxt formula)
  in
      if ecode = 0
      then
          (case othy of
              SOME thy => Syntax.read_term_global thy sout
            | NONE => (read_term (Context.the_thread_data ()) sout))
      else
        raise (SD_SPEEDITH_ERROR retVal)
  end




(*==============================================================================
  = from_terms_to_sds
  ============================================================================*)
fun from_terms_to_sds terms =
  let
      fun impl_terms_to_sds [] sds = sds
        | impl_terms_to_sds (t::terms) sds = impl_terms_to_sds terms (sds @ [(SOME (from_snf_to_sd t)) handle _ => NONE])
      val sds = impl_terms_to_sds terms []
  in
      sds
  end;




(*==============================================================================
  = Utility functions
  ============================================================================*)

fun get_goal_terms _ =
  let
      val state = Isar.state ()
      val _ = if Toplevel.is_proof state then () else raise (SD_ERROR "Not inside a proof.")
      val proof = Toplevel.proof_of state
      val terms = Unsynchronized.ref []
      
      val _ = Seq.hd (Proof.apply
                         (Method.Basic
                             (fn ctx =>
                                SIMPLE_METHOD (fn thm => let val _ = (terms := Thm.prems_of thm) in all_tac thm end))
                         ) proof)
  in
      (!terms, proof)
  end;



(*==============================================================================
  = I3P Communication Routines
  ============================================================================*)

fun i3p_write_sds_goals _ =
  let
      val (terms, proof) = get_goal_terms ()
      val sds = from_terms_to_sds terms
      fun impl_write_sds [] = ()
        | impl_write_sds ((SOME (sd:sd, form:OriginalForm))::sds) = let val _ = tracing (PolyML.makestring form) val _ = tracing (PolyML.makestring sd) in () end
        | impl_write_sds (NONE::sds) = tracing (PolyML.makestring INVALID);
  in
      impl_write_sds sds
  end;




(*==============================================================================
  = Random Test Stuff
  ============================================================================*)

fun random_tests str =
  let
      val (out, ret) = Isabelle_System.bash_output ("echo " ^ str)
      val _ = tracing (PolyML.makestring ([ ("A","B"), ("C","D") ]))
  in
      (out, ret)
  end;

fun print_subgoals _ =
  let
      val ctxt = (case (Context.thread_data ()) of
                     SOME (Context.Proof pctx) => pctx
                   | _ => raise (SD_ERROR "Could not get the proof context. Are you inside a proof?"))
      val _ = tracing "is this tracing? or is this love?"
      val _ = tracing (PolyML.makestring (Proof_Context.print_lthms ctxt))
  in
      "tralala"
  end;
  



(*==============================================================================
  = sd_tac
  ============================================================================*)

fun sd_tac args ctxt i st = SUBGOAL (fn (subgoal, _) =>
   let
       fun mk_trueprop_if (t as (Const ("HOL.Trueprop", _) $ _)) = t
         | mk_trueprop_if (t as (Const ("==>", _) $ _ $ _)) = t
         | mk_trueprop_if (t as (Const ("all", _) $ _)) = t
         | mk_trueprop_if (t as (Const ("==", _) $ _ $ _)) = t
         | mk_trueprop_if t = HOLogic.mk_Trueprop t
       (*val thy = Thm.theory_of_thm st;
       val speedithTerm = speedith_batch_apply subgoal (SOME thy) args
       val _ = tracing ("Parsed Speedith's term: " ^ (PolyML.makestring speedithTerm))
       val inter1 = Logic.mk_implies (mk_trueprop_if speedithTerm, subgoal)
       val _ = tracing ("Intermediate goal: " ^ (PolyML.makestring inter1))*)
       (*val inter1Thm = Goal.prove ctxt [] [] inter1 (K ((auto_tac (clasimpset_of ctxt)) THEN (ALLGOALS (Intuitionistic.prover_tac ctxt NONE))))*)
       (*val inter1Thm = (Goal.prove ctxt [] [] inter1 (K (auto_tac (clasimpset_of ctxt))))*)
       (*val _ = tracing ("Intermediate theorem: " ^ (PolyML.makestring inter1Thm))*)

       val thy = Proof_Context.theory_of ctxt;
       val speedithTerm = speedith_batch_apply subgoal (SOME thy) args
       val intert = Logic.mk_implies (mk_trueprop_if speedithTerm, subgoal)
       val _ = tracing ("Have "^Syntax.string_of_term @{context} intert)
       val intert_cterm = Thm.cterm_of thy intert
       val interThm = Goal.prove_internal [] intert_cterm (K ((auto_tac ctxt) THEN (ALLGOALS (Intuitionistic.prover_tac ctxt NONE))))
       val _ = tracing ("Interm: "^Display.string_of_thm @{context} interThm)
   in
       compose_tac (false, interThm, 1) i
   end) i st

end;