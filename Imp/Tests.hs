-----------------------------------------------------------------------------
--
-- Module      :  :  Imp_tests
-- APL:: IMP DSem - Lab Tests
--
-- ----------------------------------------------	--
-- denotational semantics definitions: in Haskell	--
-- ----------------------------------------------	--
--
-----------------------------------------------------------------------------

import Imp

-- ============================================	 --

-- ---------- Test it..! ----------------------	--



e1 = Num(2)

e2 = Sumof(Num(1),Num(2))

v1 = evaluate e1 env_null sto_null		--  = 2

v2 = evaluate e2 env_null sto_null		--  = 3



v3 = evaluate (Sumof(Num(1), Prodof(Num(2),Num(3)))) env_null sto_null --  = 7



dx  = Constdef("x",Num(2))	-- a declaration

dxx = elaborate dx env_null sto_null



{--

v4 = evaluate (
        Leten( dx, Sumof( Num(1), Id("x") ))
        ) env_null sto_null -- = 3

 --}
 

{- ----------------------------------------------- --

--   let value x ~ 2

 *   in let var y : int

 *      in  y:= 3

 *          if x<y then y:=1

 *                 else y:=2

 --}

pgm =

  Letin( Constdef( "x", Num(2)),

         Letin( Vardef( "y", Int),

		    Cmdcmd( Assign( "y", Num(3)),

		        Ifthen( Less(Id("x"),Id("y")),

			        Assign("y",Num(1)),

			        Assign("y",Num(2))

				)

			)

		)

         )

  

s1 = execute pgm  env_null sto_null

				-- dump the store....

                        -- y --

-- t1 = map ($ fetch s1) [ 1 ]



{- ----------------------------------------------- --

 *   let Const  x ~ 2

 *   in let var     y : int

 *      in y := 3

 *         let var z : int

 *         in  z:= 0

 *             z := z+1

 --}

x_ = Id("x")	-- a shorthand...

y_ = Id("y")

z_ = Id("z")


pgm3 =

  Letin( Constdef( "x", Num(2)),

       Letin( Vardef( "y", Int),

              Cmdcmd( Assign( "y", Num(3)),

	              Letin ( Vardef( "z", Int),

		              Cmdcmd( Assign( "z",Num(0)),

                                      Assign("z", Sumof(z_,Num(1)))

				      )

			      )

		      )

	      )

       )

  

sto3 = execute pgm3  env_null sto_null

    

				-- dump the store....

--                            y  z

v5 = map (curry fetch sto3) [ 1, 2 ]


				-- dump the store....

dump :: Store -> [Value]
dump (sto @ (Store(lo, hi, dat)) ) =

    map (curry fetch sto) [lo .. hi]

s2 = dump sto3



{- -----------------------------------------------

--   let Const  x ~ 2

 *   in let var     y : int

 *      in y := 3

 *         let var z : int

 *         in  z:= 0		{ multiply z = x*y }

 *             while 0<y do  z := z+x y := y-1

 --}

x = Id("x")	-- a shorthand...

y = Id("y")

z = Id("z")

pgm2 =

  Letin( Constdef( "x", Num(2)),

       Letin( Vardef( "y", Int),

              Cmdcmd( Assign( "y", Num(3)),

	              Letin ( Vardef( "z", Int),

		              Cmdcmd( Assign( "z",Num(0)),

                                      Whiledo( Less(Num(0),y_),

                                          Cmdcmd( Assign("z", Sumof(z_,x_)),

                                                  Assign("y", Subof(y_,Num(1)))

						  )

					  )

				      )

			      )

		      )

	      )

       )

  

sto2 = execute pgm2  env_null sto_null



	-- dump the store....

    -- y  z 

s3 = dump sto2
------------------------------------
impTestVals = [ v1, v2, v3 ]
impTestStos = [ dump s1, s2, s3 ]

-- ------------- Function ----------------------
pgm4	=  Letin(Func("add", ConstDef("x", Int), Sumof(x_, Num(5))),
                 Letin(Vardef("y", Int),
                       Assign("y", Callfunc("add", Num(10)))
               	 )
           )

sto4 = execute pgm4 env_null sto_null
s4 = dump sto4
 
-- ------------- Procedure ----------------------
pgm5 = Letin(Vardef("y", Int), 
			 Letin(Proc("foo", ConstDef("x", Int), Assign("y", x_)),
			 	   Callproc("foo", Num(9))	
			 )
	   )

sto5 = execute pgm5 env_null sto_null
s5 = dump sto5

-- -------------- Java/C++ Loop --------------------------
i_ = Id("i")
s_ = Id("s")
pgm6  = Letin(Vardef("s", Int), 
			 Cmdcmd(Assign("s", Num(0)), 
					Loop( "i", 
						  Num(0), 
						  Num(10), 
						  Assign("s", Sumof(s_, i_))
					)
			 )
		)
sto6 = execute pgm6 env_null sto_null
s6 = dump sto6

main = do
	print "------ APL:: DSem_imp"
	print impTestVals
	print impTestStos
	print "------ APL:: Function"
	print "func add(x) { "
	print "  return x + 5;"
	print "}"
	print "add(10) = ?"
	print s4
	print "------ APL:: Procedure"
	print "int y;"
	print "func foo(x) { "
	print "  y = x;"
	print "}"
	print "foo(9); y = ?"
	print s5
	print "------ APL:: Loop"
	print "int s = 0;"
	print "for(int i=0; i<10; i++) {"
	print "  s = s + i;"
	print "}"
	print "s = ? & i = ?"
	print s6
