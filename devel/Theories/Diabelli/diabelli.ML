(*  Title:      diabelli.ML
    Author:     Matej Urbas

Diabelli: provides the necessary infrastructure for heterogeneous reasoning
          with Spider diagrams in Isabelle.
*)

(* NOTE: Documentation on each of the members of the DIABELLI structure is
         provided below (in comments, just above their respective
         implementations). *)
signature DIABELLI =
sig
  type sd
  
  val make_subgoal_tac: term -> int -> thm -> thm Seq.seq
  val from_term_to_sd: term -> sd
  val traverse_term: term -> string
  val print_props_tac: Proof.context -> tactic
  val bash_escape: string -> string

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
fun string_of_term t = Pretty.string_of (Syntax.pretty_term @{context} t)



(* Replaces a subgoal with an arbitrary term.

Parameter 1 (prop): the arbitrary term with which to replace sugoal 'i'.

Parameter 2 (i): the number of the subgoal which we want to replace.

Parameter 3 (st): the theorem. This argument is provided by the 'apply'
                  mechanism (omit it when using apply), e.g.:
     
         apply (tactic {* Diabelli.make_subgoal_tac @{term "Trueprop True"} 1 *})

*)
fun make_subgoal_tac prop i st = SUBGOAL (fn (subgoal, _) =>
   let
     val thy = Thm.theory_of_thm st;
     val adhoc_rule = Skip_Proof.make_thm thy (Logic.mk_implies (prop, subgoal));
   in
     compose_tac (false, adhoc_rule, 1) i
   end) i st;



exception SD_TRANSLATE_ERROR of (string * term);



(* This function translates an Isabelle HOL term into spider diagram notation
   suitable for input to the external diagrammatic reasoner.

   Parameter 1: A term. Here is an example of a valid term:

                  @{term "(∃f. sd [s, s'] f (f s ∈ A ∩ B ∧ f s' ∈ (A - B) ∪ (B - A)))"}

   Returns: A record of type 'Diabelli.sd'. Containing the term translated to
            a spider diagram notation suitable for export to the external
            reasoner.

   Exception SD_TRANSLATE_ERROR: If the input term could not have been
            translated to a spider diagram. *)
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
  fun from_term_to_sd (@{term "op --> :: bool => bool => bool"} $ t1 $ t2) = BinarySD { operator = "op -->", arg1 = from_term_to_sd t1, arg2 = from_term_to_sd t2 }
    (*| from_term_to_sd (@{term "op | :: (('a => 'b) => bool) => bool"} $ Abs (_, _, t)) = inner_term_to_sd t*)
    | from_term_to_sd (@{term "Ex :: (('a => 'b) => bool) => bool"} $ Abs (_, _, t)) = inner_term_to_sd t
    (*| from_term_to_sd (@{term "Ex :: ('a => bool) => bool"} $ Abs (s, _, t)) = inner_term_to_sd t*)
    | from_term_to_sd t = raise (SD_TRANSLATE_ERROR ("Could not translate to spider diagrams. Unexpected outer term.", t))
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
   fun escape_char chr = case chr of
                             #"\"" => "\\\""
                           | #"\\" => "\\\\"
                           | chr   => Char.toString chr
in
    fun bash_escape str = String.translate escape_char str
end




fun random_tests str =
  let
      val (out, ret) = Secure.bash_output ("echo " ^ str)
  in
      (out, ret)
  end;

end;