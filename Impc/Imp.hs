-----------------------------------------------------------------------------
--
-- Module      :  :  DSem_imp
-- APL Lab Template in Haskell!!
--
-- ----------------------------------------------	--
-- denotational semantics definitions: in Haskell	--
-- ----------------------------------------------	--
-- Imp: expressions language (Watt, Ex. 3.6)	--
--      with commands    (store).. 		--
--      and  definitions (evnironment).. 	--
--
--     (A nicer version of Ex. 4.7 from text)	--
-- --------------------------------------------	--
--
-----------------------------------------------------------------------------
module Imp where

-- --------------------------------------------	--
-- ---------- Abstract Syntax -----------------	--

			-- terminal nodes of the syntax --
type      Numeral  = Int
type      Ident    = String

			-- parsed phrases of the abstract syntax --
data Command =
              Skip
            | Assign     (Ident,       Expression)
            | Letin      (Declaration, Command   )
            | Cmdcmd     (Command,     Command   )
            | Ifthen     (Expression,  Command, Command)
            | Whiledo    (Expression,  Command   )
            | Callproc   (Ident, ActualParameter)
            | Loop		 (Ident, Expression, Expression, Command)
            | Prog       (Command)
            | Goto       (Ident)
            | Leave      (Ident)
            | AssignCmd  (Ident, Command)

data Expression =
            Num    Numeral
    	    | False_
    	    | True_
    	    | Notexp     Expression
    	    | Id         Ident
    	    | Sumof      (Expression,  Expression)
    	    | Subof      (Expression,  Expression)
    	    | Prodof     (Expression,  Expression)
    	    | Less       (Expression,  Expression)
    	    | Callfunc   (Ident, ActualParameter)
            | Leten   	 (Declaration, Expression)
         --   deriving Show

data Declaration =
	      Constdef (Ident,  Expression)
	    | Vardef   (Ident,  TypeDef   )
	    | Func     (Ident, FormalParameter, Expression)
	    | Proc 	   (Ident, FormalParameter, Command)

data TypeDef = Bool | Int

data Dec = ConstDef (Ident, TypeDef)

type FormalParameter =  Dec

type ActualParameter =  Expression

-- --------------------------------------------	--
-- ---------- Semantic Domains ----------------	--

type	Integer	= Int
type	Boolean	= Bool
type	Location	= Int

data	Value	= IntValue    Int
		        | TruthValue  Bool
		        | Output (Value, Answer)
		        | Halt
                  deriving (Eq, Show)
                  
type	Storable  = Value
type    Answer    = Value
type    Argument  = Value

type 	Fn  = Argument -> Econt -> Store -> Value
type    Pr  = Argument -> Ccont -> Store -> Value
type    Cm  = Store    -> Value

data	Bindable  = Const Value 
					| Variable Location
					| Function Fn
					| Procedure Pr
					| Commandable Cm
                  --deriving (Eq, Show)

data	Denotable = Unbound | Bound Bindable
                  --deriving (Eq, Show)
                  
-- ----------- Continuations ---------------	--
type Econt  = Value    -> Answer
type Dcont  = Environ  -> Store -> Answer
type Ccont  = Store    -> Answer

-- ---------- Semantic Functions --------------	--
valuation :: Int         -> Value
evaluate  :: Expression  -> Environ -> Econt  -> Ccont
elaborate :: Declaration -> Environ -> Dcont  -> Ccont
execute   :: Command     -> Environ -> Ccont  -> Ccont
run       :: Command     -> Numeral -> Answer
draw      :: Expression  -> String
-- --------------------------------------------	--
-- ---------- Auxiliary Semantic Functions ----	--
add   (x, y) = x + y
diff  (x, y) = x - y
prod  (x, y) = x * y

lessthan  (x, y) = x < y

-- ---------- Storage   ---------- --
-- fun deallocate sto loc:Location = sto	-- ... later --

data Sval  = Stored Storable | Undef | Unused
 
-- The actual storage in a Store
type DataStore = Location -> Sval

--	                 --bot---   --top---  --data---
data Store = Store (Location,  Location,  DataStore)

update :: (Store, Location, Value) -> Store
update (Store(bot,top,sto), loc, v) =
	let new adr = if adr==loc
			      then Stored v else (sto adr)
	in Store( bot, top, new)

		-- fetch from store, and convert into Storable (=Const)
fetch ::(Store,Location) -> Storable
fetch  (Store(bot,top,sto), loc)  =
	let stored_value(Stored stble) = stble
	    stored_value(Unused)       = error ("Store: Unused")
	    stored_value(Undef)        = error ("Store: Undefined ")
	in  stored_value(sto loc)

		-- create a new "undefined" location in a store
allocate :: Store -> (Store, Location)
allocate ( Store(bot,top,sto) )  =
	let newtop  = top+1
	    new adr = if adr==newtop
			      then Undef else (sto adr)
	in (Store( bot, newtop, new), newtop)

-- ---------- Envirionment   ----------
type  Environ  =  Ident -> Denotable

bind :: (Ident,Bindable) -> Environ
bind  (name, val) =  \id -> if id==name
                            then Bound(val) else Unbound

-- look through the layered environment bindings
find :: (Environ, Ident) -> Bindable
find  (env, id)  =
	let getbv(Bound bdbl) = bdbl
	    getbv(Unbound)    = error ("undefined: " ++ id)
	in getbv( env id)

-- -------- Define equal for overlay --------------
equal :: Denotable -> Bool
equal Unbound = True
equal x = False

overlay :: (Environ, Environ) -> Environ
overlay  (env', env)  =
	\id -> let val = env' id
	       in  if (equal val) then env id
	                            else val

-- ---------- Etc...
--    coerce a Bindable into a Const..
coerc :: (Store, Bindable) -> Value
coerc (sto, Const v)      = v
coerc (sto, Variable loc) = fetch(sto,loc)

-- ---------- Initialize system  ----------
env_null :: Environ
env_null =  \i -> Unbound

--  store_null =  empty (=0), addressing starts at 1
sto_init :: DataStore
sto_init =  \loc -> Unused

sto_null :: Store
sto_null =  Store( 1, 0, sto_init)

kont_null :: Econt
kont_null = \v -> Output(v, Halt)

cont_null :: Ccont
cont_null  = \any_store -> Halt

qont_null :: Dcont
qont_null  = \any_env -> cont_null

-- --------------------------------------------

-- --------------- Actual and formal parameters ------------------

bind_parameter :: FormalParameter -> Argument -> Environ
bind_parameter ( ConstDef(id, tdef) ) arg = bind(id, Const(arg))

give_argument  :: ActualParameter -> Environ -> Econt -> Store -> Argument
give_argument ( exp ) env cont sto = evaluate exp env cont sto

-- ---------- Semantic Equations --------------

				-- from integer to Const Value
valuation ( n ) = IntValue(n)

execute ( Skip ) env cont sto = cont sto

execute ( Assign(name, exp) ) env cont sto  =
		let Variable loc = find(env, name) in
		let cont' rhs = cont(update( sto, loc, rhs )) in
 		evaluate exp env cont' sto

execute ( Letin(def,c) ) env cont sto =
		let cont' env' sto' = execute c (overlay (env', env)) cont sto'
     	in elaborate def env cont' sto

execute ( Cmdcmd(c1,c2) ) env cont sto  =
		let cont' = execute c2 env cont in
		execute c1 env cont' sto

execute ( Ifthen(e,c1,c2) ) env cont sto =
		let cont' = \v -> if v == TruthValue (True)
						  then execute c1 env cont sto
						  else execute c2 env cont sto
	    in evaluate e env cont' sto	

execute ( Whiledo(e,c) ) env cont sto =
		let cont' sto' = evaluate e env cont'' sto'	
     					 where cont'' = \(TruthValue v) -> if v == True
     													   then execute c env cont' sto'
     													   else cont sto'
		in cont' sto

execute ( Callproc(id, ap) ) env cont sto =
		let Procedure proc = find(env, id) in
		let cont' arg = proc arg cont sto in
		give_argument ap env cont' sto

execute ( AssignCmd(id, c) ) env cont sto =
		let cont' = execute c (overlay(bind(id, Commandable cont'), env)) cont 
		in cont' sto 

execute ( Goto i ) env cont sto =
		let Commandable cont' = find(env, i)
  		in cont' sto

execute ( Leave i ) env cont sto = cont sto
			
     			-- simple, just build a Const
evaluate ( Num(n)  )  env cont sto  = cont(IntValue n)
evaluate ( True_   )  env cont sto  = cont(TruthValue  True)
evaluate ( False_  )  env cont sto  = cont(TruthValue  False)

     			-- lookup id, and  coerce as needed
evaluate ( Id(n)  )  env cont sto  = cont(coerc( sto, find(env,n) ))

     			-- get Consts, and compute result
evaluate ( Sumof(e1,e2) ) env cont sto =
		let cont' (IntValue i1) = evaluate e2 env (cont'' i1) sto
              		where cont'' i1 (IntValue i2) = cont(IntValue (add(i1, i2)))
  		in  evaluate e1 env cont' sto

evaluate ( Subof(e1,e2) ) env cont sto =
     	let cont' (IntValue i1) = evaluate e2 env (cont'' i1) sto
              		where cont'' i1 (IntValue i2) = cont(IntValue (diff(i1, i2)))
  		in  evaluate e1 env cont' sto

evaluate ( Prodof(e1,e2) ) env cont sto =
     	let cont' (IntValue i1) = evaluate e2 env (cont'' i1) sto
              		where cont'' i1 (IntValue i2) = cont(IntValue (prod(i1, i2)))
  		in  evaluate e1 env cont' sto

evaluate ( Less(e1,e2) ) env cont sto =
		let cont' (IntValue i1) = evaluate e2 env (cont'' i1) sto
					where cont'' i1 (IntValue i2) = cont(TruthValue(lessthan(i1, i2)))
		in evaluate e1 env cont' sto

evaluate ( Notexp(e) ) env cont sto =
     	if evaluate e env cont sto == cont(TruthValue ( True ))
     	then cont(TruthValue ( False ))
     	else cont(TruthValue ( True ))

evaluate ( Callfunc(id, ap) ) env cont sto =
		let Function func = find(env, id) in
		let cont' arg = func arg cont sto in 
		give_argument ap env cont' sto		
		
-- layer environment, and compute result
evaluate ( Leten(def,e) ) env cont sto =
		let cont' env' sto' = evaluate e (overlay (env', env)) cont sto'
     	in elaborate def env cont' sto

elaborate ( Constdef(name,e) ) env cont sto =
		let cont' v = cont (bind(name, Const v)) sto
  		in  evaluate e env cont' sto

elaborate ( Vardef(name,tdef) ) env cont sto =
     	let (sto', loc) = allocate sto in
      	let env' = bind(name, Variable loc) 
  		in  cont env' sto'
		
elaborate ( Func( id, fp, e ) ) env cont sto =
		let func arg = evaluate e (overlay (env', env))
                 	   where env' = bind_parameter fp arg
  		in  cont (bind(id, Function func)) sto

elaborate ( Proc( id, fp, c ) ) env cont sto =
		let proc arg = execute c (overlay (env', env))
                 	   where env' = bind_parameter fp arg
  		in  cont (bind(id, Procedure proc)) sto

-- -------------------------- Program run ---------------------
run ( Prog(c) ) i =
	let (sto', loc) = allocate sto_null in
	let env = overlay(env_null, bind("input", Variable loc)) in
	let env' = overlay(env, bind("result", Variable loc)) in
	let sto'' = update(sto', loc, IntValue i) in
	let cont s = fetch(s, loc) in
	execute c env' cont sto''

	
draw e = show (evaluate e env_null kont_null sto_null)
		
-- ============================================	 --
