(* Michaël PÉRIN, Verimag / Université Grenoble-Alpes, Février 2017
 *
 * Part of the project TURING MACHINES FOR REAL
 *
 * CONTENT 
 *
 *   Realisation of the Universal Turing Machine as a 3-Bands TM (PROJECT 2019)
 *
 *)


(* PROJET 2019 
 *
 * Contributeurs 
 *
 * NOM Prénom : Théo CUOQ
 * NOM Prénom : Jessy DUCHAINE
 * NOM Prénom : Ludovic JOZEAU
 * NOM Prénom : Axel JOSEPH
 *
 *)


open Symbol
open Alphabet
open Band
   
open Pattern
open Action
open State
open Turing_Machine   


open Configuration
open Execution
   
(** TYPE *)

  
type machine_code = string * (Symbol.t list) (* (name,code) where code = sequence of symbols of the Alphabet.utm *)
          
type data = Symbol.t list (* sequence of symbols of the Alphabet.zero_unit = {Z,U} *)


          
                          
(** Some Turing Machines FOR TESTING the Universal Turing Machine *)

let nop: Turing_Machine.t = Turing_Machine.nop 

          
(*** The "executable" TM that does the negation of each bit of a binary word *)
                          
let neg_TM: Turing_Machine.t =
  let init   = nop.initial
  and accept = nop.accept
  in Turing_Machine.export	
  { nop with
    name =  "M_neg" ; 
    transitions = 
      [ (init, Action(RWM(Match(VAL U), Write Z, Right)), init) ;
	(init, Action(RWM(Match(VAL Z), Write U, Right)), init) ; 
        (init, Action(RWM(Match(VAL B), Write B, Here )), accept) 
      ]
  }
  
(**** The named "code" of the previous TM *)
  
let neg_code: machine_code =
  let code = 
    [ O;Std;Z;C ; U ; Z ; R ; O;Std;Z;C ; (* (Std0) -U/Z:R-> (Std0) *)
      O;Std;Z;C ; Z ; U ; R ; O;Std;Z;C ; (* (Std0) -Z/U:R-> (Std0) *)
      O;Std;Z;C ; B ; B ; H ; O;Acc;U;C   (* (Std0) -B/B:H-> (Acc1) *)
    ]
  in ("m_neg",code)

   
  
(*** A TM that increases an little-endian binary integer by one unit: incr([n]_2) = [n+1]_2 *)
                          
let incr_TM: Turing_Machine.t =
  let init = nop.initial and accept = nop.accept
  in Turing_Machine.export	 
  { nop with
    name =  "M_incr" ; 
    transitions = 
      [ (init, Action(RWM(Match(VAL U), Write Z, Right)), init) ;
	(init, Action(RWM(Match(VAL Z), Write U, Here )), accept) ; 
        (init, Action(RWM(Match(VAL B), Write U, Here )), accept) 
      ]
  }

(**** The named "code" of the previous TM *)
  
let incr_code: machine_code =
  let code = [ (* ... à compléter ... *) ]
  in
  ("m_incr", code)


  
  
(*** decreases an little-endian binary integer by one unit: incr([n]_2) = [n-1]_2 *)
  
let decr_TM: Turing_Machine.t =
  let init = nop.initial and accept = nop.accept and reject = nop.reject in
  let unit = State.fresh_from init in
  let zero = State.fresh_from unit in
  let back = State.fresh_from zero
  in Turing_Machine.export	
  { nop with
    name = "M_decr" ;
    transitions = 
      [ (init, Action( RWM (Match(VAL Z), No_Write, Right)), unit) ;
	(init, Action( RWM (Match(VAL U), Write Z , Here )), accept) ;
	(init, Action( RWM (Match(VAL B), No_Write, Here )), reject) ;
	
	(unit , Action( RWM (Match(VAL B), No_Write, Left )), reject) ;
	(unit , Action( RWM (Match(VAL Z), No_Write, Right)), unit) ;
	(unit , Action( RWM (Match(VAL U), Write B , Right)), zero) ;
	
	(zero , Seq [ Action( RWM (Match(VAL B), No_Write, Left)) ; Action( RWM (Match(VAL B), No_Write, Left)) ], back) ;
	(zero , Seq [ Action( RWM (Match(BUT B), No_Write, Left)) ; Action( RWM (Match(VAL B), Write  Z, Left)) ], back) ;
	
	(back , Action( RWM (Match(VAL Z), Write U , Left )), back) ;
	(back , Action( RWM (Match(VAL B), No_Write, Right)), accept) 
      ]
  }

(**** The "code" of the previous TM written on one band *)
  
let decr_code: machine_code =
  let code = [ (* ... à compléter ... *) ]
  in  ("m_decr", code)


(* Finds the next start of transition (opening parenthesis of the starting state) *)
(* Finds the  next opening parenthesis, twice *)
let next_start: Turing_Machine.t =
  let init = nop.initial and accept = nop.accept and reject = nop.reject in
  let inter = State.fresh_from init
  in Turing_Machine.export	
  { nop with
    name = "M_decr" ;
    transitions = 
      [ (init, Action( RWM (Match(BUT O), No_Write, Right)), init) ;
        (init, Action( RWM (Match(VAL O), No_Write, Right)), inter) ;
        (inter, Action( RWM (Match(BUT O), No_Write, Right)), inter) ;
        (inter, Action( RWM (Match(VAL O), No_Write, Here)), accept)
      ]
  }
    

(** THE UNIVERSAL TURING MACHINE *)

(* UTM is a three-bands Turing Machine
 *
 * UTM(m,w) acts as an interpreter:  It runs the code of the Turing Machine m (written on band B2) onto the data w (witten on band B1) 
 * The current state of m is written on band B3.
 *
 *)

  
let utm: Turing_Machine.t = 
  let init = nop.initial in
  let accept = nop.accept in
  let std1 = State.fresh_from init in
  let std_check_acc = State.fresh_from std1 in
  let std_check_acc_2 = State.fresh_from std_check_acc in
  (* Found a new candidate transition, head is on first character *)
  let std_find_next_trans = State.fresh_from std_check_acc_2 in
  (* Bringing B2 to a new transition and B3 to its beginning *)
  let std_next_state = State.fresh_from std_find_next_trans in
  let std_next_trans_reset = State.fresh_from std_next_state in
  let std_end_next_trans = State.fresh_from std_next_trans_reset in

  let std_check_trans_next = State.fresh_from std_end_next_trans in
  let std_exec = State.fresh_from std_check_trans_next in
  let std_exec_move = State.fresh_from std_exec in

  (* Read a state *)
  let macros_transitions =
    Transition.foreach_symbol_of Alphabet.utm.symbols (IN [O;Std;Acc;Exc;Z;U]) (fun s ->
	[ (init, Action( Simultaneous [ Nop ; RWM(Match(VAL s), No_Write, Right) ; RWM(Match ANY, Write s, Right) ]), init) ]
      )
  in
  (* find the next potential transition (finds the first matching state of B2 and B3) *)
  let next_transition =
    Transition.foreach_symbol_of Alphabet.utm.symbols (IN [O;Std;Acc;Exc;Z;U]) (fun s ->
	[ (std_find_next_trans, Action( Simultaneous [ Nop ; RWM(Match(VAL s), No_Write, Right) ; RWM(Match(VAL s), No_Write, Right) ]), std_find_next_trans) ;
    (std_find_next_trans, Action( Simultaneous [ Nop ; RWM(Match(VAL s), No_Write, Right) ; RWM(Match(BUT s), No_Write, Right) ]), std_next_state)
    ] )
  in
  (* checks if the current transition in B2 matches the entry of B1 (executes the transition if it matches, else searches for another transition)*)
  let check_transition =
    Transition.foreach_symbol_of Alphabet.utm.symbols (IN [Z;U;B;D;S]) (fun s ->
	[ (std_end_next_trans, Action( Simultaneous [ RWM(Match(VAL s), No_Write, Here) ; RWM(Match(VAL s), No_Write, Right) ; Nop ] ), std_exec);
    (std_end_next_trans, Action( Simultaneous [ RWM(Match(VAL s), No_Write, Here) ; RWM(Match(BUT s), No_Write, Here) ; Nop ] ), std_check_trans_next) ]
      ) @ [(std_check_trans_next, Parallel [ Action(Nop) ; Run(next_start) ; Action(Nop) ], std_find_next_trans)]
  in
  let exec =
    Transition.foreach_symbol_of Alphabet.utm.symbols (IN [Z;U;B;D;S]) (fun s ->
	[ (std_exec, Action( Simultaneous [ RWM(Match ANY, Write s, Here) ; RWM(Match(VAL s), No_Write, Right) ; Nop]), std_exec_move)]
    
      ) @
    [ (std_exec_move, Action( Simultaneous [ RWM(Match ANY, No_Write, Left) ; RWM(Match(VAL L), No_Write, Right)  ; Nop]), init);
    (std_exec_move, Action( Simultaneous [ RWM(Match ANY, No_Write, Right) ; RWM(Match(VAL R), No_Write, Right) ; Nop]), init);
    (std_exec_move, Action( Simultaneous [ Nop ; RWM(Match(VAL H), No_Write, Right) ; Nop] ), init)]
  in
  Turing_Machine.export	
  { nop with
    nb_bands = 3 ;
    name = "UTM" ;
    transitions =
      macros_transitions  @ (*read first state *)
        [
          (* end of first state *)
          (init, Action( Simultaneous [ Nop ; RWM(Match(VAL C), No_Write, Right) ; RWM(Match ANY, Write C, Right)]), std1) ;
          (* return to the beginning of the states *)
          (std1, Parallel [ Action(Nop) ; Run(TM_Basic.left_most) ; Run(TM_Basic.left_most) ], std_check_acc) ;
          (* check if we are in acc state *)
          (std_check_acc, Action( Simultaneous [ Nop; Nop; RWM(Match ANY, No_Write, Right)]), std_check_acc_2) ;
          (std_check_acc_2, Action( Simultaneous [ Nop; Nop; RWM(Match(VAL Acc), No_Write, Here)]), accept) ;
          (std_check_acc_2, Action( Simultaneous [ Nop; Nop; RWM(Match(VAL Std), No_Write, Left)]), std_find_next_trans)
        ] @
          (* TODO: truc à THEO *)
      next_transition @
        [ 
          (std_find_next_trans, Action( Simultaneous [ Nop ; RWM(Match(VAL C), No_Write, Right) ; RWM(Match(VAL C), No_Write, Left) ]), std_next_trans_reset);
          (std_next_trans_reset, Parallel [ Action(Nop) ; Action(Nop) ; Run(TM_Basic.left_most) ], std_end_next_trans);
          (std_next_state, Parallel [ Action(Nop) ; Run(next_start) ; Run(TM_Basic.left_most) ], std_find_next_trans)
        ] @
          (*check if we read on B1 what we want to read on B2 *)
      check_transition @
          (* put exec *)
      exec
  }

  
(* Using the UTM as an interpreter:  UTM m w *)
  
let run_UTM_on: machine_code -> data -> Configuration.t = fun interpretable_m w ->
  let (machine_name,machine_code) = interpretable_m in
  let band1 = Band.make "Data" Alphabet.zero_unit  w
  and band2 = Band.make machine_name Alphabet.utm  machine_code
  and band3 = Band.make "State" Alphabet.utm []
  in
  let cfg = Configuration.make utm [ band1 ; band2 ; band3 ]
  in
  Execution.i_log_run cfg 



(* Running an executable TM on a word w *)  
  
let run_TM_on: Turing_Machine.t -> data -> Configuration.t = fun executable_M w  ->
  let band = Band.make "Data" Alphabet.zero_unit w 
  in
  let cfg = Configuration.make executable_M [ band ]
  in
  Execution.i_log_run cfg 



(* DEMO *)  
  
let demo: unit -> unit = fun () ->
  begin
    print_string "\n\n* DEMO * UTM.ml:\n\n" ;
    List.iter (fun _ -> ())
      [ run_TM_on neg_TM [U;Z;Z;U] ;
        run_UTM_on neg_code [U;Z;Z;U] ;
        (* ... à compléter ... *)
      ]
  end
