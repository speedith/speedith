(*  Title:      diabelli.ML
    Author:     Matej Urbas

Diabelli: provides the necessary infrastructure for heterogeneous reasoning
          with Spider diagrams in Isabelle.
*)

signature DIABELLI =
sig
  type sd

  (* Replaces a subgoal with an arbitrary term.

     Parameter 1 (prop): the arbitrary term with which to replace sugoal 'i'.

     Parameter 2 (i): the number of the subgoal which we want to replace.

     Parameter 3 (st): the theorem. This argument is provided by the 'apply'
                       mechanism (omit it when using apply), e.g.:

         apply (tactic {* Diabelli.make_subgoal_tac @{term "Trueprop True"} 1 *})
  *)
  val make_subgoal_tac: term -> int -> thm -> thm Seq.seq
  (* This function translates an Isabelle/HOL term of the 'MFOL spider normal'
   form into a spider diagram record suitable for input to Speedith.

   @param  1  A term. Here is an example of a valid term:

                  @{term "(∃s1 s2. distinct[s1, s2] ∧ s1 ∈ A ∩ B ∧ s2 ∈ (A - B) ∪ (B - A)) ⟶ (∃s1 s2. distinct[s1, s2] ∧ s1 ∈ A ∧ s2 ∈ B)"}

   @returns  A record of type 'Diabelli.sd'. Containing the term translated to
             a spider diagram notation suitable for export to the external
             reasoner.

   @exception  SD_TRANSLATE_ERROR: If the input term could not have been
               translated to a spider diagram. *)
  val from_snf_to_sd: term -> sd
  (* This function translates an Isabelle/HOL term of the higher-order spider
     normal form (HO-SNF) into spider diagram notation suitable for input to the
     external diagrammatic reasoner.

     @param  1  A term. Here is an example of a valid term:

                    @{term "(∃f. sd [s, s'] f (f s ∈ A ∩ B ∧ f s' ∈ (A - B) ∪ (B - A)))"}

     @returns  A record of type 'Diabelli.sd'. Containing the term translated to
               a spider diagram notation suitable for export to the external
               reasoner.

     @throws  SD_TRANSLATE_ERROR  If the input term could not have been
              translated to a spider diagram. *)
  val from_hosnf_to_sd: term -> sd
  val traverse_term: term -> string
  val print_props_tac: Proof.context -> tactic
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

  val random_tests: string -> (string * int)
end;



structure Diabelli: DIABELLI =
struct



(* Some auxilliary types used in the record that contains all information about
   a spider diagram statement. *)
type spider_name = string;
type contour_name = string;
type zone = (contour_name list * contour_name list);
type region = zone list;
type operator_name = string



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

(* Some private helper functions: *)
(* fun string_of_term t = Pretty.string_of (Syntax.pretty_term @{context} t) *)



fun make_subgoal_tac prop i st = SUBGOAL (fn (subgoal, _) =>
   let
     val thy = Thm.theory_of_thm st;
     val adhoc_rule = Skip_Proof.make_thm thy (Logic.mk_implies (prop, subgoal));
   in
     compose_tac (false, adhoc_rule, 1) i
   end) i st;



exception SD_TRANSLATE_ERROR of (string * term);
exception SD_ERROR of string;




local
  (* 'collect_ex_spiders' gets a list of all existentially quantified spiders.

  @param   1  a list of spiders to which to append the found spiders

  @param   2  the term where to look for existentially quantified spiders.

  @returns (spNames : string list, t : term)

           where 'spNames' is a list of the collected names of quantified
           spiders, and 't' is the term over which all the collected spiders
           quantify. *)
  fun collect_ex_spiders spNames (@{term "Ex :: ('a::HOL.type => bool) => bool"} $ Abs (spName, _, t)) = (collect_ex_spiders (spNames @ [spName]) t)
    | collect_ex_spiders spNames t = (spNames, t)

  (* Makes a list of all conjunctively connected terms in a primary expression
     (i.e., an expression that will get converted into a primary spider
     diagram). These conjunctions are inside the scope of the existentially
     quantified spiders.

     @returns a list of terms. *)
  fun collect_conjuncts (@{term "op & :: bool => bool => bool"} $ t1 $ t2) = (collect_conjuncts t1) @  (collect_conjuncts t2)
    | collect_conjuncts t = [t]

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

  (* Looks for the conjunctive term that consists of the 'distinct' predicate
     (where the argument to the 'distinct' predicate is a list with all the
     spiders that are existentially quantified in the conjunct scope).

     @returns a list of term (without the one containing the 'distinct'
              predicate.*)
  fun find_distinct conjuncts (_::[]) = conjuncts (* No 'distinct' needed for one spider. *)
    | find_distinct conjuncts [] = conjuncts (* Same for zero spiders. *)
    | find_distinct ((@{term "List.distinct :: 'a::HOL.type List.list => bool"} $ spHOLlst)::conjuncts) (spiders : string list) = 
      (* We have a distinct predicate here. It must have exactly the same elements as the existentially quantified spiders. *)
      let
          val spidersInDistinct = map (fn (Bound i) => nth spiders i | _ => raise SD_ERROR ("The list in the 'distinct' term should consist only of spiders.")) (HOLogic.dest_list spHOLlst)
          (* Now make sure the two lists are the same. *)
          val listsEqual = eq_list op= ((sort_distinct string_ord spidersInDistinct), (sort_distinct string_ord spiders))
          (*val _ = writeln ("Found 'distinct' with spiders: " ^ (PolyML.makestring spidersInDistinct))*)
      in
          if listsEqual then conjuncts else raise (SD_TRANSLATE_ERROR ("Primary spider diagram extraction failed. Could not find the 'distinct' term for spiders '" ^ (PolyML.makestring spiders) ^ "'.", spHOLlst))
      end
    | find_distinct (c::conjuncts) spiders = c::(find_distinct conjuncts spiders)
    | find_distinct _ spiders = raise (SD_ERROR ("Primary spider diagram extraction failed. Could not find the 'distinct' term for spiders '" ^ (PolyML.makestring spiders) ^ "'."))

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
    | from_snf_to_sd_outer (@{term "Ex :: ('a::HOL.type => bool) => bool"} $ Abs (spName, _, t)) =
      let
          val (spiders, inner_term) = collect_ex_spiders [spName] t
          (*val _ = raise (SD_TRANSLATE_ERROR (PolyML.makestring spiders, t))*)
      in
        (from_snf_to_sd_inner spiders inner_term)
      end
    | from_snf_to_sd_outer (@{term "True"}) = NullSD
    | from_snf_to_sd_outer t = raise (SD_TRANSLATE_ERROR ("Could not translate to spider diagrams. Unexpected from_snf_to_sd_outer term.", t))
in
  fun from_snf_to_sd t = from_snf_to_sd_outer t
end;



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



(* Just having some fun traversing terms and making a string out of them. *)
fun traverse_term (t1 $ t2) = "[ " ^ (traverse_term t1) ^ " $ " ^ (traverse_term t2) ^ " ]"
  | traverse_term (Const (s, _)) = "Const = '" ^ s ^ "'"
  | traverse_term (Free (s, _)) = "Free = '" ^ s ^ "'"
  | traverse_term (Var ((s, i), _)) = "Var = '" ^ s ^ "' (" ^ Int.toString i ^ ")"
  | traverse_term (Bound i) = "Bound = " ^ Int.toString i
  | traverse_term (Abs (s, _, t)) = "[ Abs '" ^ s ^ "': " ^ (traverse_term t) ^ " ]";



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

fun exec_args cmd args =
  let
      val qArgs = List.foldl (fn (s2, s1) => s1 ^ " " ^ s2) "" (map bash_escape args)
      val _ = writeln qArgs
  in
      Secure.bash_output (cmd ^ qArgs)
  end




fun random_tests str =
  let
      val (out, ret) = Secure.bash_output ("echo " ^ str)
  in
      (out, ret)
  end;

end;