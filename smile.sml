(* An interpreter for a dynamically typed language that otherwise
   looks much like a subset of SML. 

   Design decisions:

     * values (the results of evaluation) are represented by a
       separate type from unevaluated expressions, even when those
       expressions are literals like true or "hello".  This leans on
       the type system to help ensure we do not forget to evaluate
       anything.

 *)

(* Variable symbols are represented by strings. *)
type sym = string

(* Expressions: this is the abstract syntax of our language.
   You can write programs in our language by constructing ML values
   of type expr.  These values encode Abstract Syntax Trees.  *)
datatype expr = Unit
              | Bool of bool
              | Int of int
              | String of string
              | Plus of expr * expr
              | Minus of expr * expr
              | Times of expr * expr
              | Div of expr * expr
              | Mod of expr * expr
              | Concat of expr * expr
              | Lt of expr * expr
              | Gt of expr * expr
              | Le of expr * expr
              | Ge of expr * expr
              | Eq of expr * expr
              | Ne of expr * expr
              | Neg of expr
              | Not of expr
              | IfThenElse of expr * expr * expr
              | AndAlso of expr * expr
              | OrElse of expr * expr
              | Tuple of expr list
              | Constructor of sym * expr
              | Fn of sym * expr
              | Apply of expr * expr
              | Var of sym
              | Let of binding list * expr
              | Case of expr * (pattern * expr) list

(* patterns appear in Case exprs *)
     and pattern = UnitP
                 | Wildcard
                 | VarP of sym
                 | BoolP of bool
                 | IntP of int 
                 | StringP of string
                 | TupleP of pattern list
                 | TagP of sym * pattern

(* Fun and Val bindings appear in Let exprs *)
     and binding = Fun of sym * sym * expr
                 | Val of sym * expr

(* Values: these are not part of program syntax.  They are the results
of evaluating an expression. *)
datatype value = UnitV
               | BoolV of bool
               | IntV of int
               | StringV of string
               | TupleV of value list
               | TagV of sym * value
               | ClosureV of (sym * value) list ref * sym * expr

(******************** IMPLEMENTATION *************************)

(* We will build an environment-based interpreter.  Environments are
represented by association lists mapping symbols to values. *)
type environment = (sym * value) list

(* Look up a variable in an environment.
   Raise Unbound if the variable is not bound in the environment. 

   sym -> environment -> value
*)
exception Unbound of sym
fun lookup x [] = raise (Unbound x)
  | lookup x ((k,v)::rest) = if k=x then v else lookup x rest

(* Raise Unimplemented where you haven't finished the interpreter
   or the given type of expression is not expected to appear at
   run time. *)
exception Unimplemented

(* Raise MoMatch when there is no match in a Case expression *)
exception NoMatch

(* Raise TypeError when an operation is applied to incompatible values *)
exception TypeError

fun match UnitV UnitP = SOME [] 
  | match (BoolV x) (BoolP y) =  SOME [] 
  | match (StringV x) (StringP y) = SOME [] 
  | match (IntV x) (IntP y) = SOME [] 
  | match v (VarP s) = SOME [(s,v)] 
(*  | match (TupleV vs) (TupleP []) = NONE 
    | match (TupleV []) (TupleP ps) = NONE
    | match (TupleV []) (TupleP []) = SOME [] 
    | match (TupleV (v::vs)) (TupleP (p::ps)) = (* if (match p v) then match (TupleV vs) (TupleP ps) else false *)		
      (case (match v p) of NONE => NONE 
			 | SOME rest => (match (TupleV vs) (TupleP ps)))*)
  | match (TupleV vs) (TupleP ps) = 
     let fun help (TupleV []) (TupleP []) = SOME []
	   | help (TupleV (v::vs)) (TupleP (p::ps)) =
						   case (match v p) of NONE => NONE
								     | SOME rest => help (TupleV vs) (TupleP ps)
     in help (TupleV vs) (TupleP ps)
     end 

  | match (TagV(s1,v)) (TagP(s2,p)) = if (s1=s2) 
				   then case (match v p) of NONE => NONE 
							   | SOME [] => SOME []
				   else NONE (* ?? *)
  | match _ Wildcard = SOME [] 

(* Evaluate the given expression in the given environment.
   This is a recursive function.  Most expressions just continue
   to use the same environment, but some expressions evaluate their
   subexpressions in larger or different environments.

   environment -> expr -> value
*)

fun eval env Unit = UnitV
  | eval env (Bool b) = BoolV b
  | eval env (Int i) = IntV i
  | eval env (String s) = StringV s
  | eval env (Neg e) = (case eval env e of
                            IntV i => IntV (~i)
                          | _ => raise TypeError)
  | eval env (Not e) = (case eval env e of
                            BoolV b => BoolV (not b)
                          | _ => raise TypeError)
  | eval env (Plus (e1,e2)) = (case (eval env e1, eval env e2) of
                                 (IntV i, IntV j) => IntV (i + j)
                               | _ => raise TypeError)
  | eval env (Minus (e1,e2)) = (case (eval env e1, eval env e2) of
                                  (IntV i, IntV j) => IntV (i - j)
                                | _ => raise TypeError)
  | eval env (Times (e1,e2)) = (case (eval env e1, eval env e2) of
                                  (IntV i, IntV j) => IntV (i * j)
                                | _ => raise TypeError)
  | eval env (Div (e1,e2)) = (case (eval env e1, eval env e2) of
                                (IntV i, IntV j) => IntV (i div j)
                              | _ => raise TypeError)
  | eval env (Mod (e1,e2)) = (case (eval env e1, eval env e2) of
                                (IntV i, IntV j) => IntV (i mod j)
                              | _ => raise TypeError)
  | eval env (Lt (e1,e2)) = (case (eval env e1, eval env e2) of
                               (IntV i, IntV j) => BoolV (i < j)
                             | _ => raise TypeError)
  | eval env (Gt (e1,e2)) = (case (eval env e1, eval env e2) of
                               (IntV i, IntV j) => BoolV (i > j)
                             | _ => raise TypeError)
  | eval env (Le (e1,e2)) = (case (eval env e1, eval env e2) of
                               (IntV i, IntV j) => BoolV (i <= j)
                             | _ => raise TypeError)
  | eval env (Ge (e1,e2)) = (case (eval env e1, eval env e2) of
                               (IntV i, IntV j) => BoolV (i >= j)
                             | _ => raise TypeError)
  | eval env (Concat (e1,e2)) = 
    (case (eval env e1, eval env e2) of
         (StringV i, StringV j) => StringV (i ^ j)
       | _ => raise TypeError)
  | eval env (Eq (e1,e2)) = BoolV ((eval env e1)=(eval env e2))
  | eval env (Ne (e1,e2)) = BoolV ((eval env e1)<>(eval env e2))

  (* Now the interesting parts (sample solution uses 50-60 more lines
     for the rest of eval) *)

  (* Evaluate the "if" expression, i, to value vi.
     If vi is the true value,
        the result is the evaluation of the "then" expression, t,
     else if vi is the false value,
        the result is the evaluation of the "else" expression, e,
     else if vi is any other value,
        there is a type error.

     Note that, with our current dynamically typed language,
     we do not check that the "then" and "else" expression 
     have the same result type.  Why not?
   *)
  (*
  | eval env (IfThenElse (i,t,e)) =
    (if (case eval env i of
                   BoolV v => v
                 | _ => raise TypeError)
           then eval env t else eval env e)
   *)
  (*
  | eval env (IfThenElse (i,t,e)) =
    eval env (case eval env i of
                  BoolV true => t
                | BoolV false => e
                | _ => raise TypeError)
   *)
  (* And another... *)
  | eval env (IfThenElse (i,t,e)) =
    eval env (case eval env i of
                  BoolV true => t
                | BoolV false => e
                | _ => raise TypeError)

   (*Evaluate expression e1 to value v1.
     If v1 is the false value,
        the result is false,
     else if v1 is the true value,
        Evaluate e2 to v2.
        If v2 is the false value,
           the result is false,
        else if v2 is the true value,
           the result is true,
        else if v2 is any other value,
           there is a type error.
     else if v1 is any other value,
        there is a type error.
   *)
  (*
  | eval env (AndAlso (e1,e2)) = 
    BoolV (case eval env e1 of
               BoolV false => false
             | BoolV true => (case eval env e2 of
                                  BoolV v => v
                                | _ => raise TypeError)
             | _ => raise TypeError)
   *)
  (*
  | eval env (AndAlso (eq,e2)) = 
    BoolV ((case eval env e1 of
                BoolV v => v
              | _ => raise TypeError)
           andalso
           (case eval env e2 of
                BoolV v => v
              | _ => raise TypeError))
   *)
(*
  | eval env (AndAlso (e1,e2)) = eval env (IfThenElse (e1,e2,Bool false))
  *)
  (* This one is right... what's the difference? *)
  | eval env (AndAlso (e1,e2)) =
    (case eval env (IfThenElse (e1,e2,Bool false)) of
         BoolV v => BoolV v
       | _ => raise TypeError)


  | eval env (OrElse (e1,e2))  = (case eval env (IfThenElse (e1,Bool true,e2)) of
                                      BoolV v => BoolV v
                                    | _ => raise TypeError)
  (* Given Tuple [e1,...,en],
     Evaluate each subexpression ei to value vi, in order.
     The result is TupleV [v1,...,vn]
     
     Feels like a familiar higher order function...
     Also note the use of a partially applied eval!
  *)
  | eval env (Tuple es) = TupleV (map (eval env) es)
  (* Evaluate the subexpression to a value and produce
     a tagged version of that value. *)
  | eval env (Constructor (n,e)) = TagV (n, eval env e)

  (* Now for the real fun... *)
  (* Anonymous functions: fn x => e

     DESCRIBE THIS. *) 
  | eval env (Fn (x,e)) = ClosureV (ref env, x, e)
  (* Fn assigns the variable x to the expression e to be 
     to be evaluated in the environment env and ties all 
     of the information up into a closure value. 
     In this case we are adding to an existing closure.  
   *)

  | eval env (Apply (e1,e2)) =
    let
        val closure = eval env e1
	(* evaluating e1 in the given environment and binding it 
	   to the variable closure 
	 *)        
        val arg_value = eval env e2
        (* evaluating e2 in the given environment and binding it 
	   to the variable arg_value 
	 *)
    in
        case closure of
            ClosureV (closure_env, x, e) =>
	    (* evaluating the first thing and consing it onto the environment, new env is returned  *)
            (* This takes an environment, formatted as a list, called 
   	       closure_env, and x is assigned to the value returned 
	       when evaluates the expression e with 
	     *)
            eval ((x,arg_value)::(!closure_env)) e
	    (* 
	     *)
          | _ => raise TypeError
    end

  (* x
     Lookup a variable in the current environment. *)
  | eval env (Var x) = lookup x env

  (* let <bindings> in e end
     Evaluate bindings in order, building the environment
     in which to evaluate e. *)     
  | eval env (Let (bindings,e)) =
    let fun bindhelp [] env' = env'
          | bindhelp (Val (x,e')::rest) env' = 
            bindhelp rest ((x, eval env' e')::env')
	  | bindhelp (Fun (f,x,e')::rest) env' = 
	    let
		val closure_env = ref []
		val closure = ClosureV(closure_env,x,e') (* closure will map to itself *)
		val new_env =  (f,closure)::env'
	        val _ = closure_env:=new_env 
	    in 
		bindhelp rest new_env
		(* bindhelp rest closure_env *)
	    end
		
    (****** COMPLETE THE IMPLEMENTATION OF FUN BINDINGS ******)

    in
        eval (bindhelp bindings env) e
    end

  (* COMPLETE THE IMPLEMENTATION OF CASE EXPRESSIONS

     case e of
         <pattern> => <expr> 
       | <pattern> => <expr>
       |  ...

     Evaluate e, then match against each pattern in order
     until a matching pattern is found, and evaluate the
     corresponding expression in the current environment,
     extended with bindings introduced in the pattern.

     This one is the most involved. *)
  | eval env (Case (e, cases)) = (* raise Unimplemented *)
    let	val x = eval env e 
  	fun help x [] = raise NoMatch
	  | help x ((pat,exp)::cases) = 
	    case (match x pat) of SOME [] => eval env exp (* c is a pair of exp and pat i.e. pat => exp *)  
				| NONE => help x cases   
    in
	help x cases 
    end	
  
(*  | Case of expr * (pattern * expr) list *)
    (* let e1 = eval env e *) 
    (* compare e1 to each of the items in cases *)

	    (* list of pairs of patterns and expressions, pull out the value that matches the pattern
	     BoolP pattern BoolV match then => 
	     otherwise check the next one 
	     think about ML cases
	     eval cases iterates over the list 
	     matching calls match function, write outside of eval to test - takes a v and a p, in the function binding list possibilities
	     match UnitV and UnitP as the first and second argument - pattern match at the same time 
	     wildcard case at the end catches everything that doesnt match BoolV(x) BoolP(y) return x = y 
	     recursive because value definitions are recursive: tuples have sub patterns
	     similiar to eval in art, but here pattern matching oover 2 things at the same time *)



(**** Examples ****)
val _ = Control.Print.printDepth := 100


val factml =
    let 
        fun fact x =
            if x <= 1
            then 1
            else x * (fact (x-1))
    in
        fact 6
    end

val factlang =
    (Let ([Fun ("fact", "x",
               IfThenElse (Le (Var "x", Int 1),
                           Int 1,
                           Times (Var "x", 
                                  Apply (Var "fact",
                                         Minus (Var "x", Int 1)))))
         ],
         Apply (Var "fact", Int 6)))

val factlang_result = eval [] factlang

