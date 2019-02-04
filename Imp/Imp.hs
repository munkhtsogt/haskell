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
                  deriving (Eq, Show)

type	Storable  = Value

type    Argument  = Value
type 	Fn  = Argument -> Store -> Value
type    Pr  = Argument -> Store -> Store
				
data	Bindable  = Const Value 
					| Variable Location
					| Function Fn
					| Procedure Pr
                  --deriving (Eq, Show)

data	Denotable = Unbound | Bound Bindable
                  --deriving (Eq, Show)

-- --------------------------------------------	--
-- ---------- Semantic Functions --------------	--
valuation :: Int         -> Value
evaluate  :: Expression  -> Environ -> Store ->  Value
elaborate :: Declaration -> Environ -> Store ->  (Environ,Store)
execute   :: Command     -> Environ -> Store ->  Store
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

-- --------------------------------------------

-- --------------- Actual and formal parameters ------------------

bind_parameter :: FormalParameter -> Argument -> Environ
bind_parameter ( ConstDef(id, tdef) ) arg = bind(id, Const(arg))

give_argument  :: ActualParameter -> Environ -> Store -> Argument
give_argument ( exp ) env sto = evaluate exp env sto

-- ---------- Semantic Equations --------------

				-- from integer to Const Value
valuation ( n ) = IntValue(n)

execute ( Skip ) env sto = sto

execute ( Assign(name,exp) ) env sto  =
 		let rhs = evaluate exp env sto
 		    Variable loc = find( env,name)
 		in  update( sto, loc, rhs)

execute ( Letin(def,c) ) env sto =
     	let (env', sto') = elaborate def env sto
     	in execute c (overlay (env', env)) sto'

execute ( Cmdcmd(c1,c2) ) env sto  =
		execute c2 env (execute c1 env sto)

execute ( Ifthen(e,c1,c2) ) env sto =
		if evaluate e env sto == TruthValue ( True )
		then execute c1 env sto
		else execute c2 env sto	

execute ( Whiledo(e,c) ) env sto =
     	let while env sto =
     		if evaluate e env sto == TruthValue ( True )
     		then while env (execute c env sto)
     		else sto
 		in while env sto

execute ( Callproc(id, ap) ) env sto =
		let Procedure procedure = find(env, id) in
		let arg = give_argument ap env sto in
		procedure arg sto

execute ( Loop(name, e1, e2, c) ) env sto =
		let (env', sto') = elaborate (Vardef(name, Int)) env sto in
		let Variable loc = find(env', name)  in
		let rhs = evaluate e1 env sto in
		let IntValue i = evaluate e1 env sto in
		let IntValue n = evaluate e2 env sto in
		let loop i n env sto =
			if i < n
			then let sto_p = evaluate (Num(i+1)) env sto in 
				 loop (i + 1) n env (execute c env (update(sto, loc, sto_p)))
			else sto
		in loop i n (overlay(env', env)) (update(sto', loc, rhs))
		
     			-- simple, just build a Const
evaluate ( Num(n)  )  env sto  = IntValue n
evaluate ( True_   )  env sto  = TruthValue  True
evaluate ( False_  )  env sto  = TruthValue  False

     			-- lookup id, and  coerce as needed
evaluate ( Id(n)  )  env sto  = coerc( sto, find(env,n) )

     			-- get Consts, and compute result
evaluate ( Sumof(e1,e2) ) env sto =
     	let IntValue i1 = evaluate e1 env sto
     	    IntValue i2 = evaluate e2 env sto
     	in  IntValue  ( add(i1,i2) )

evaluate ( Subof(e1,e2) ) env sto =
     	let IntValue i1 = evaluate e1 env sto
     	    IntValue i2 = evaluate e2 env sto
     	in  IntValue  ( diff(i1,i2) )

evaluate ( Prodof(e1,e2) ) env sto =
     	let IntValue i1 = evaluate e1 env sto
     	    IntValue i2 = evaluate e2 env sto
     	in  IntValue  ( prod(i1,i2) )

evaluate ( Less(e1,e2) ) env sto =
     	let IntValue i1 = evaluate e1 env sto
     	    IntValue i2 = evaluate e2 env sto
     	in  TruthValue  ( lessthan(i1,i2) )

evaluate ( Notexp(e) ) env sto =
     	if evaluate e env sto == TruthValue ( True )
     	then TruthValue ( False )
     	else TruthValue ( True )

evaluate ( Callfunc(id, ap) ) env sto =
		let Function func = find(env, id) in
		let arg = give_argument ap env sto in
		func arg sto
		
-- layer environment, and compute result
evaluate ( Leten(def,e) ) env sto =
     	let (env', sto') = elaborate def env sto
		in  evaluate e (overlay (env', env)) sto'

elaborate ( Constdef(name,e) ) env sto =
     	let v = evaluate e env sto
		in  ( bind(name, Const  v), sto )

elaborate ( Vardef(name,tdef) ) env sto =
     	let (sto',loc) = allocate sto
		in  ( bind(name, Variable loc), sto' )
		
elaborate ( Func( id, fp, e ) ) env sto =
		let func arg sto' =
			let parenv = bind_parameter fp arg in
			evaluate e (overlay(parenv, env)) sto'
		in ( bind(id, Function func), sto )

elaborate ( Proc( id, fp, c ) ) env sto =
		let proc arg sto' =
			let parenv = bind_parameter fp arg in
			execute c (overlay(parenv, env)) sto'
		in ( bind(id, Procedure proc), sto )		
  		
-- ============================================	 --
